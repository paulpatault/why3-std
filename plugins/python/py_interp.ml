
open Why3
open Py_ast
open Format

let () = Random.self_init ()
let print_ref = ref (fun (_s:string) -> ())
let input_ref = ref (fun (s:string) -> s)

let get_vec v i =
  if i < Vector.length v && i >= 0 then Vector.get v i
  else raise (Invalid_argument "Vector.get")

let set_vec v i x =
  if i < Vector.length v && i >= 0 then Vector.set v i x
  else raise (Invalid_argument "Vector.set")

let binop_to_string fmt = function
  | Badd -> fprintf fmt "+"
  | Bsub -> fprintf fmt "-"
  | Bmul -> fprintf fmt "*"
  | Bdiv -> fprintf fmt "//"
  | Bmod -> fprintf fmt "%s" "%"
  | Beq  -> fprintf fmt "=="
  | Bneq -> fprintf fmt "!="
  | Blt  -> fprintf fmt "<"
  | Ble  -> fprintf fmt "<="
  | Bgt  -> fprintf fmt ">"
  | Bge  -> fprintf fmt ">="
  | Band -> fprintf fmt "and"
  | Bor  -> fprintf fmt  "or"

let unop_to_string fmt = function
  | Uneg -> fprintf fmt "-"
  | Unot -> fprintf fmt "not"

type func = (string, string list * block) Hashtbl.t

type env_state = {
  vars: (string, expr) Hashtbl.t;
  funcs: func;
}

type state = {
  mutable stack: (expr -> block) list;
  prog: block;
  env: env_state list;
}

let mk_new_env () =
  { vars = Hashtbl.create 10; funcs = Hashtbl.create 10 }

let transform_idx v idx =
  if BigInt.sign idx < 0 then BigInt.add (BigInt.of_int (Vector.length v)) idx else idx

let py_div_mod n1 n2 =
  let q, r = BigInt.euclidean_div_mod n1 n2 in
  if BigInt.sign n2 >= 0 then (q, r)
  else
    let q = if BigInt.sign r > 0 then BigInt.sub q BigInt.one else q in
    let r = if BigInt.sign r > 0 then BigInt.add r n2 else r in
    (q, r)

let py_div n1 n2 = fst (py_div_mod n1 n2)
let py_mod n1 n2 = snd (py_div_mod n1 n2)

let const_to_string = function
  | Enone     -> "None"
  | Ebool b   -> if b then "True" else "False"
  | Eint s    -> s
  | Estring s -> s
  | Evector _ -> "vec"

let bool const =
  match const with
  | Enone     -> false
  | Ebool b   -> b
  | Eint i    -> let i = BigInt.of_string i in not (BigInt.eq i BigInt.zero)
  | Estring s -> s <> ""
  | Evector v -> not (Vector.is_empty v)

let rec py_compare v1 v2 ~loc =
  match v1, v2 with
  | Ebool b1,   Ebool b2   -> Bool.compare b1 b2
  | Eint n1,    Eint n2    -> BigInt.compare (BigInt.of_string n1) (BigInt.of_string n2)
  | Estring s1, Estring s2 -> String.compare s1 s2
  | Evector v1, Evector v2 ->
    let vtol v =
      let rec aux acc = function
        | -1 -> acc
        | i -> aux (get_vec v i :: acc) (i-1)
      in aux [] (Vector.length v - 1) in
    List.compare (py_compare ~loc) (vtol v1) (vtol v2)
  | _ ->
    Loc.errorm ~loc
      "TypeError: comparison not supported between instances of '%s' and '%s'"
      (const_to_string v1) (const_to_string v2)

let binop_comp ~loc = function
  | Beq  -> fun e1 e2 -> py_compare ~loc e1 e2 =  0
  | Bneq -> fun e1 e2 -> py_compare ~loc e1 e2 <> 0
  | Blt  -> fun e1 e2 -> py_compare ~loc e1 e2 <  0
  | Ble  -> fun e1 e2 -> py_compare ~loc e1 e2 <= 0
  | Bgt  -> fun e1 e2 -> py_compare ~loc e1 e2 >  0
  | Bge  -> fun e1 e2 -> py_compare ~loc e1 e2 >= 0
  | _    -> assert false

let binop_op = function
  | Badd -> BigInt.add
  | Bsub -> BigInt.sub
  | Bmul -> BigInt.mul
  | Bdiv -> py_div
  | Bmod -> py_mod
  | _    -> assert false

let binop_logic = function
  | Band -> (&&)
  | Bor ->  (||)
  | _    -> assert false

let mk_state ?stack ?prog ?env state =
  let stack = match stack with None -> state.stack | Some stack -> stack in
  let prog = match prog with None -> state.prog | Some prog -> prog in
  let env = match env with None -> state.env | Some env -> env in
  {stack; prog; env}

let mk_Dstmt stmt_desc ~loc =
  Dstmt {stmt_desc; stmt_loc=loc}

let mk_stmt stmt_desc ~loc =
  {stmt_desc; stmt_loc=loc}

let mk_expr expr_desc ~loc =
  {expr_desc; expr_loc=loc}

let get_current_env state =
  match state.env with
  | [] -> assert false
  | env::_ -> env

let expr (state: state) match_value: state =
  let loc = match_value.expr_loc in
  match match_value.expr_desc with
  | Econst c ->
      begin match state.stack with
      | [] -> Printf.printf "%s\n" (const_to_string c); state
      | f::k ->
        let app = f match_value in
        mk_state state ~stack:k ~prog:(app@state.prog)
      end

  | Elist l ->
    let rec eval_list r el stack =
      let f ret v = 
        match v.expr_desc with
          | Econst c ->
            Vector.push !r c; ret
          | _ -> assert false
      in

      match el with
        | []      -> stack
        | _e :: [] ->
          let expr = mk_expr (Econst Enone) ~loc in
          let none = mk_Dstmt (Seval expr) ~loc in
          f [none] :: stack
        | _e :: el -> eval_list r el (f [] :: stack)
    in

    let r = ref (Vector.create ~capacity:0 ~dummy:Enone) in
    let stack = eval_list r l [] in

    let f _ =
      let expr = mk_expr  (Econst (Evector !r)) ~loc in
      [mk_Dstmt (Seval expr) ~loc]
    in

    let l = List.map (fun e -> mk_Dstmt (Seval e) ~loc:e.expr_loc) l in
    mk_state state ~stack:(stack@f::state.stack) ~prog:(l@state.prog)

  | Ebinop (b, e1, e2) ->
      begin match e1.expr_desc, e2.expr_desc with
      | Econst c1, Econst c2 ->
        begin match c1, c2, b with
        | Eint s1, Eint s2, (Badd | Bsub | Bmul | Bdiv | Bmod) ->
          let b = binop_op b in
          let n1 = BigInt.of_string s1 in
          let n2 = BigInt.of_string s2 in
          let r = b n1 n2 in
          let expr = mk_expr (Econst (Eint (BigInt.to_string r))) ~loc in
          let res = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog:(res::state.prog)
        | c1, c2, (Beq | Bneq | Blt | Ble | Bgt | Bge) ->
          let b = binop_comp ~loc b in
          let r = b c1 c2 in
          let expr = mk_expr (Econst (Ebool r)) ~loc in
          let res = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog:(res::state.prog)
        | c1, c2, (Band | Bor) ->
          let b = binop_logic b in
          let b1 = bool c1 in
          let b2 = bool c2 in
          let r = b b1 b2 in
          let expr = mk_expr (Econst (Ebool r)) ~loc in
          let res = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog:(res::state.prog)
        | _ -> assert false
        end
      | Econst e1', _e2 ->
        begin match e1', b with
        | Ebool true, Bor | Ebool false, Band ->
          let e1 = mk_Dstmt (Seval e1) ~loc in
          mk_state state ~prog:(e1::state.prog)
        | _ ->
          let f e2 =
            let expr = mk_expr (Ebinop (b, e1, e2)) ~loc in
            [mk_Dstmt (Seval expr) ~loc]
          in
          let e = mk_Dstmt (Seval e2) ~loc:e2.expr_loc in
          mk_state state ~stack:(f::state.stack) ~prog:(e::state.prog)
        end
      | _e1, _e2 ->
        let f e1 =
          let expr = mk_expr (Ebinop (b, e1, e2)) ~loc in
          [mk_Dstmt (Seval expr) ~loc]
        in
        let e = mk_Dstmt (Seval e1) ~loc:e1.expr_loc in
        mk_state state ~stack:(f::state.stack) ~prog:(e::state.prog)
      end

  | Eunop (u, e) ->
    begin match u, e.expr_desc with
      | Uneg, Econst (Eint n)  ->
        let n = BigInt.of_string n in
        let expr = mk_expr (Econst (Eint (BigInt.minus n |> BigInt.to_string))) ~loc in
        let stmt = mk_Dstmt (Seval expr) ~loc in
        mk_state state ~prog:(stmt::state.prog)
      | Unot, Econst c ->
        let b = bool c in
        let expr = mk_expr (Econst (Ebool (not b))) ~loc in
        let stmt = mk_Dstmt (Seval expr) ~loc in
        mk_state state ~prog:(stmt::state.prog)
      | (Uneg | Unot), _e ->
        let f e =
          let expr = mk_expr (Eunop (u, e)) ~loc in
          [mk_Dstmt (Seval expr) ~loc]
        in
        let e = mk_Dstmt (Seval e) ~loc; in
        mk_state state ~stack:(f::state.stack) ~prog:(e::state.prog)
    end
  | Eident (x: Why3.Ptree.ident)  ->
      begin try
        let env = get_current_env state in
        let e = Hashtbl.find env.vars x.id_str in
        let stmt = mk_Dstmt (Seval e) ~loc in
        mk_state state ~prog:(stmt::state.prog)
      with Not_found ->
        Loc.errorm ~loc "NameError: name '%s' is not defined" x.id_str
      end
  | Ecall (f, el) ->
    let rec eval_list r el state = match el with
      | []      -> state
      | e :: [] ->
        let expr = mk_expr (Econst Enone) ~loc in
        let none = mk_Dstmt (Seval expr) ~loc in
        (fun v -> r := v :: !r; [none]) :: state
      | e :: el -> eval_list r el ((fun v -> r := v :: !r; []) :: state)
    in
    let r = ref [] in
    state.stack <- eval_list r [] state.stack;
    assert false
    (* let r = ref [] in
    let e::el = el in
    st := (fun v -> r:=v::!r; [Enone])::st;
    eval_list r el ((fun _ -> ... calculer l'appel à partir de !r ...) :: state) *)

  | _ -> assert false

let stmt (state: state) match_value: state =
  let match_value = match match_value with Dstmt x -> x | _ -> assert false in
  let loc = match_value.stmt_loc in
  match match_value.stmt_desc with
  | Seval x ->
    expr state x
  | Sif (e, b1, b2) ->
    begin match e.expr_desc with
    | Econst c ->
      let b = if bool c then b1 else b2 in
      mk_state state ~prog:(b@state.prog)
    | e ->
      let f e = [mk_Dstmt (Sif(e, b1, b2)) ~loc] in
      let e = mk_expr e ~loc in
      let stmt = mk_Dstmt (Seval e) ~loc in
      mk_state state ~stack:(f::state.stack) ~prog:(stmt::state.prog)
    end
  | Sassign (id, e) ->
    let f e =
      let env = get_current_env state in
      Hashtbl.replace env.vars id.id_str e;
      []
    in
    let e = mk_Dstmt (Seval e) ~loc in
    mk_state state ~stack:(f::state.stack) ~prog:(e::state.prog)
  | Swhile (cond, _inv, _var, b) ->
    begin match cond.expr_desc with
    | Econst c ->
      if bool c then mk_state state ~prog:(b@state.prog)
      else state
    | _ ->
      let f e = [mk_Dstmt (Sif(e, b@[Dstmt match_value], [])) ~loc] in
      let stmt = mk_Dstmt (Seval cond) ~loc in
      mk_state state ~stack:(f::state.stack) ~prog:(stmt::state.prog)
    end
  | _ -> assert false

let step (state: state): state =
  match state.prog with
  | [] -> assert false
  | s::k ->
      let state = {stack=state.stack; prog=k; env=state.env} in
      stmt state s

let little_steps path =
  let c = open_in path in
  let file = Py_lexer.parse path c in
  let state = ref {stack=[]; prog=file; env=[mk_new_env ()]} in
  while !state.stack <> [] || !state.prog <> [] do
    state := step !state;
  done


let () = little_steps Sys.argv.(1)
