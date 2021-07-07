
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

type func = (string, string list * block) Hashtbl.t

type env = {
  vars: (string, expr) Hashtbl.t;
  funcs: func;
}

type prog = {
  main: block;
  cont: block list;
  brk: block list;
  ret: block list;
}

type state = {
  mutable stack: (expr -> block) list;
  prog: prog;
  env: env list;
}

module Pprinter =
  struct
    let type_to_string fmt = function
      | Enone     -> fprintf fmt "NoneType"
      | Ebool _   -> fprintf fmt "bool"
      | Eint _    -> fprintf fmt "int"
      | Estring _ -> fprintf fmt "str"
      | Evector _   -> fprintf fmt "list"

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

    let rec const_to_string fmt = function
      | Enone     -> fprintf fmt "None"
      | Ebool b   -> if b then fprintf fmt "True" else fprintf fmt "False"
      | Eint s    -> fprintf fmt "%s" s
      | Estring s    -> fprintf fmt "%s" s
      | Evector v -> fprintf fmt "[%a]" list_to_string (v, 0)

    and list_to_string fmt (vec, i) =
      if i = Vector.length vec then ()
      else if i + 1 = Vector.length vec
      then fprintf fmt "%a" const_to_string (get_vec vec i)
      else fprintf fmt "%a, %a" const_to_string (get_vec vec i) list_to_string (vec, (i+1))

    let rec expr_to_string fmt e =
      match e.expr_desc with
      | Econst a -> const_to_string fmt a
      | Eident i -> fprintf fmt "i"
      | Ebinop (b, e1, e2) ->
        fprintf fmt "(%a %a %a)" expr_to_string e1 binop_to_string b expr_to_string e2
      | Eunop (u, e) ->
        fprintf fmt "(%a %a)" unop_to_string u expr_to_string e
      | Ecall (i, el) -> (*TODO i*)
        fprintf fmt "function_i_(%a)" expr_list_to_string el
      | Edot (e, i, el) -> (*TODO i*)
        fprintf fmt "%a._i_(%a)" expr_to_string e expr_list_to_string el
      | Elist el ->
        fprintf fmt "[%a]" expr_list_to_string el
      | Emake (e1, e2) ->
        fprintf fmt "[%a] * %a" expr_to_string e1 expr_to_string e2
      | Eget (e1, e2) ->
        fprintf fmt "%a[%a]" expr_to_string e1 expr_to_string e2
    and expr_list_to_string fmt = function
      | [] -> ()
      | [e] -> fprintf fmt "%a" expr_to_string e
      | e::k -> fprintf fmt "%a, %a" expr_to_string e expr_list_to_string k

    let rec stmt_to_string fmt s =
      match s.stmt_desc with
      | Sblock b ->
        block_to_string fmt b
      | Sif (e, b1, b2) ->
          fprintf fmt "if %a:@.@[%a@]else:@.@[%a@]" expr_to_string e block_to_string b1 block_to_string b2
      | Sreturn e ->
        fprintf fmt "return %a@." expr_to_string e
      | Sassign (i, e) ->
        fprintf fmt "_i_ = %a@." expr_to_string e
      | Swhile (e, _, _, b) ->
          fprintf fmt "while %a:@.@[<hov 2>%a@]@." expr_to_string e block_to_string b
      | Sfor (i, e, _, b) ->
          fprintf fmt "for _i_ in %a:@.@[%a@]" expr_to_string e block_to_string b
      | Seval e ->
        expr_to_string fmt e
      | Sset (e1, e2, e3) ->
        fprintf fmt "%a[%a] = %a@." expr_to_string e1 expr_to_string e2 expr_to_string e3
      | Sbreak -> fprintf fmt "break@."
      | Scontinue -> fprintf fmt "continue@."
      | _ -> assert false

    and stmt_list_to_string fmt = function
      | [] -> ()
      | [e] -> fprintf fmt "%a" stmt_to_string e
      | e::k -> fprintf fmt "%a, %a" stmt_to_string e stmt_list_to_string k

    and decl_to_string fmt = function
      | Ddef _ | Dimport _ | Dlogic _ -> ()
      | Dstmt s -> stmt_to_string fmt s

    and block_to_string fmt = function
      | [] -> ()
      | [e] -> fprintf fmt "@[%a@]" decl_to_string e
      | e::k -> fprintf fmt "@[%a@] @[%a@]" decl_to_string e block_to_string k
  end

open Pprinter

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
      "TypeError: comparison not supported between instances of '%a' and '%a'"
      const_to_string v1 const_to_string v2

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

let mk_state ?stack ?prog_main ?prog_brk ?prog_cont ?prog_ret ?env state =
  let stack = match stack with None -> state.stack | Some stack -> stack in
  let prog_main = match prog_main with None -> state.prog.main | Some prog -> prog in
  let prog_brk = match prog_brk with None -> state.prog.brk | Some prog -> prog in
  let prog_cont = match prog_cont with None -> state.prog.cont | Some prog -> prog in
  let prog_ret = match prog_ret with None -> state.prog.ret | Some prog -> prog in
  let env = match env with None -> state.env | Some env -> env in
  let prog = {
    main=prog_main;
    brk=prog_brk;
    cont=prog_cont;
    ret=prog_ret;
  } in
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

let loop_out = function
  | _::brk, _::cont -> brk, cont
  | [], []          -> [], []
  | _ -> assert false

let get_hd = function
  | [] -> []
  | hd::_ -> hd

let get_hd_tl_vec vec ~loc =
  if Vector.is_empty vec then assert false
  else
    let hd = get_vec vec 0 in
    let tl = Vector.sub vec 1 (Vector.length vec - 1) in
    mk_expr (Econst hd) ~loc, mk_expr (Econst (Evector tl)) ~loc

let expr (state: state) match_value: state =
  let loc = match_value.expr_loc in
  match match_value.expr_desc with
  | Econst c ->
    begin match state.stack with
    | [] -> Printf.printf "%s\n" (asprintf "%a" const_to_string c); state
    | f::k ->
      let app = f match_value in
      mk_state state ~stack:k ~prog_main:(app@state.prog.main)
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
    let stack = List.rev (eval_list r l []) in

    let f _ =
      let expr = mk_expr  (Econst (Evector !r)) ~loc in
      [mk_Dstmt (Seval expr) ~loc]
    in

    let l = List.map (fun e -> mk_Dstmt (Seval e) ~loc:e.expr_loc) l in
    mk_state state ~stack:(stack@f::state.stack) ~prog_main:(l@state.prog.main)

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
        mk_state state ~prog_main:(res::state.prog.main)
      | c1, c2, (Beq | Bneq | Blt | Ble | Bgt | Bge) ->
        let b = binop_comp ~loc b in
        let r = b c1 c2 in
        let expr = mk_expr (Econst (Ebool r)) ~loc in
        let res = mk_Dstmt (Seval expr) ~loc in
        mk_state state ~prog_main:(res::state.prog.main)
      | c1, c2, (Band | Bor) ->
        let b = binop_logic b in
        let b1 = bool c1 in
        let b2 = bool c2 in
        let r = b b1 b2 in
        let expr = mk_expr (Econst (Ebool r)) ~loc in
        let res = mk_Dstmt (Seval expr) ~loc in
        mk_state state ~prog_main:(res::state.prog.main)
      | _ -> assert false
      end
    | Econst e1', _e2 ->
      begin match e1', b with
      | Ebool true, Bor | Ebool false, Band ->
        let e1 = mk_Dstmt (Seval e1) ~loc in
        mk_state state ~prog_main:(e1::state.prog.main)
      | _ ->
        let f e2 =
          let expr = mk_expr (Ebinop (b, e1, e2)) ~loc in
          [mk_Dstmt (Seval expr) ~loc]
        in
        let e = mk_Dstmt (Seval e2) ~loc:e2.expr_loc in
        mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
      end
    | _e1, _e2 ->
      let f e1 =
        let expr = mk_expr (Ebinop (b, e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc:e1.expr_loc in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    end

  | Eunop (u, e) ->
    begin match u, e.expr_desc with
    | Uneg, Econst (Eint n)  ->
      let n = BigInt.of_string n in
      let expr = mk_expr (Econst (Eint (BigInt.minus n |> BigInt.to_string))) ~loc in
      let stmt = mk_Dstmt (Seval expr) ~loc in
      mk_state state ~prog_main:(stmt::state.prog.main)
    | Unot, Econst c ->
      let b = bool c in
      let expr = mk_expr (Econst (Ebool (not b))) ~loc in
      let stmt = mk_Dstmt (Seval expr) ~loc in
      mk_state state ~prog_main:(stmt::state.prog.main)
    | (Uneg | Unot), _e ->
      let f e =
        let expr = mk_expr (Eunop (u, e)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    end

  | Eident (x: Why3.Ptree.ident)  ->
      begin try
        let env = get_current_env state in
        let e = Hashtbl.find env.vars x.id_str in
        let stmt = mk_Dstmt (Seval e) ~loc in
        mk_state state ~prog_main:(stmt::state.prog.main)
      with Not_found ->
        Loc.errorm ~loc "NameError: name '%s' is not defined" x.id_str
      end

  | Emake (e1, e2) ->
    begin match e1.expr_desc, e2.expr_desc with
    | Econst c1, Econst c2 ->
      begin match c1, c2 with
      | _, Eint i ->
        let v = Vector.make ~dummy:Enone (BigInt.of_string i |> BigInt.to_int) c1 in
        let expr = mk_expr (Econst (Evector v)) ~loc in
        let stmt = mk_Dstmt (Seval expr) ~loc in
        mk_state state ~prog_main:(stmt::state.prog.main)
      | _ -> assert false
      end
    | Econst _c, _e2 ->
      let f e2 =
        let expr = mk_expr (Emake (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e2) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)

    | _e1, _e2 ->
      let f e1 =
        let expr = mk_expr (Emake (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    end

  | Eget (e1, e2) ->
    begin match e1.expr_desc, e2.expr_desc with
    | Econst c1, Econst c2 ->
      begin match c1, c2 with
      | Evector v, Eint i ->
        let i = BigInt.of_string i |> transform_idx v |> BigInt.to_int in
        begin try
          let atom = get_vec v i in
          let expr = mk_expr (Econst atom) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog_main:(stmt::state.prog.main)
        with Invalid_argument _s -> assert false end
      | _ -> assert false
      end
    | Econst _c, _e2 ->
      let f e2 =
        let expr = mk_expr (Eget (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e2) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)

    | _e1, _e2 ->
      let f e1 =
        let expr = mk_expr (Eget (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    end

  | Ecall (f, el) ->
    begin try
      let params, b = Hashtbl.find (get_current_env state).funcs f.id_str in

      begin match el with
        | [{expr_desc=Econst (Evector v)}] ->
          let envf = {vars = Hashtbl.create 10; funcs = (get_current_env state).funcs} in
          let idx = ref 0 in
          if List.length params <> Vector.length v then assert false
          else
            List.iter (fun id -> Hashtbl.add envf.vars id (mk_expr (Econst (Vector.get v !idx)) ~loc); incr idx) params;
            mk_state state ~prog_main:(b@state.prog.main) ~prog_ret:(state.prog.main::state.prog.ret) ~env:(envf::state.env)
        | [] ->
          let envf = {vars = Hashtbl.create 10; funcs = (get_current_env state).funcs} in
          mk_state state ~prog_main:(b@state.prog.main) ~prog_ret:(state.prog.main::state.prog.ret) ~env:(envf::state.env)
        | _ ->
          let f e =
            let expr = mk_expr (Ecall(f, [e])) ~loc in
            [mk_Dstmt (Seval expr) ~loc]
          in
          let expr = mk_expr (Elist el) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~stack:(f::state.stack) ~prog_main:(stmt::state.prog.main)
      end
    with Not_found -> assert false end

  | Edot (e, id, params) -> assert false

let rec stmt (state: state) match_value: state =
  let loc = match_value.stmt_loc in
  match match_value.stmt_desc with
  | Sblock b ->
    mk_state state ~prog_main:(b@state.prog.main)

  | Seval x ->
    expr state x

  | Sif (e, b1, b2) ->
    begin match e.expr_desc with
    | Econst c ->
      let b = if bool c then b1 else b2 in
      mk_state state ~prog_main:(b@state.prog.main)
    | e ->
      let f e = [mk_Dstmt (Sif(e, b1, b2)) ~loc] in
      let e = mk_expr e ~loc in
      let stmt = mk_Dstmt (Seval e) ~loc in
      mk_state state ~stack:(f::state.stack) ~prog_main:(stmt::state.prog.main)
    end

  | Sassign (id, e) ->
    let f e =
      let env = get_current_env state in
      Hashtbl.replace env.vars id.id_str e;
      []
    in
    let e = mk_Dstmt (Seval e) ~loc in
    mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)

  | Sfor (id, e, _inv, b) ->

    let hd =
      match get_hd state.prog.cont with
      | Dstmt ({stmt_desc=Sfor(_, _, _, b);_} as stmt)::_ -> Some b, Some stmt
      | _          -> None, None
    in

    let first =
      match hd with
      | Some h, _ -> not (h == b)
      | _         -> true in

    let prog_brk, prog_cont =
      if first then
        state.prog.main::state.prog.brk, (Dstmt match_value::state.prog.main)::state.prog.cont
      else
        let prog_brk, prog_cont = loop_out (state.prog.brk, state.prog.cont) in
        let state = mk_state state ~prog_brk ~prog_cont in
        state.prog.main::state.prog.brk, (Dstmt match_value::state.prog.main)::state.prog.cont
    in

    begin match e.expr_desc with
    | Econst (Evector v) ->
        if Vector.is_empty v
        then
          let prog_brk, prog_cont = loop_out (state.prog.brk, state.prog.cont) in
          mk_state state ~prog_brk ~prog_cont
        else
          let hd_vec, tl_vec = get_hd_tl_vec v e.expr_loc in
          let env = (get_current_env state).vars in
          Hashtbl.replace env id.id_str hd_vec;
          let stmt = mk_Dstmt (Sfor(id, tl_vec, _inv, b)) ~loc in
          let prog_main = b@stmt::state.prog.main in
          mk_state state ~prog_main ~prog_brk ~prog_cont
    | Econst _ -> assert false
    | _v ->
      let f e = [mk_Dstmt (Sfor(id, e, _inv, b)) ~loc] in
      let e = mk_Dstmt (Seval e) ~loc in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main) ~prog_brk ~prog_cont
      end

  | Swhile (cond, _inv, _var, b) ->

    let hd =
      match get_hd state.prog.cont with
      | Dstmt m::_ -> Some m
      | _          -> None
    in

    let first =
      match hd with
      | Some {stmt_desc=Swhile(_, _, _, b');_} -> not (b' == b)
      | _      -> true in

    let prog_brk =
      if first then state.prog.main::state.prog.brk
      else state.prog.brk in
    let prog_cont =
      if first then (Dstmt match_value::state.prog.main)::state.prog.cont
      else state.prog.cont in

    begin match cond.expr_desc with
    | Econst c ->
      if bool c then
        let while_ = if first then match_value else Opt.get hd in
        mk_state state ~prog_main:(b@[Dstmt while_]@state.prog.main) ~prog_brk ~prog_cont
      else
        let prog_brk, prog_cont = loop_out (state.prog.brk, state.prog.cont) in
        mk_state state ~prog_brk ~prog_cont
    | _ ->
      let f e = [mk_Dstmt (Swhile(e, _inv, _var, b)) ~loc] in
      let e = mk_Dstmt (Seval cond) ~loc in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main) ~prog_brk ~prog_cont
    end

  | Sset (e1, e2, e3) ->
    begin match e1.expr_desc, e2.expr_desc, e3.expr_desc with
    | Econst (Evector v), Econst (Eint i), Econst c ->
      let i = BigInt.of_string i |> transform_idx v |> BigInt.to_int in
      set_vec v i c;
      state
    | Econst (Evector _v), _e2, Econst _c ->
      let f e2 =
        [mk_Dstmt (Sset (e1, e2, e3)) ~loc]
      in
      let e = mk_Dstmt (Seval e2) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    | _e1, _e2, Econst _c ->
      let f e1 =
        [mk_Dstmt (Sset (e1, e2, e3)) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    | _e1, _e2, _e3 ->
      let f e3 =
        [mk_Dstmt (Sset (e1, e2, e3)) ~loc]
      in
      let e = mk_Dstmt (Seval e3) ~loc; in
      mk_state state ~stack:(f::state.stack) ~prog_main:(e::state.prog.main)
    end

  | Sreturn e ->
    begin match e.expr_desc with
      | Econst _c ->
        let env = match state.env with
        | _::[] -> assert false
        | _::env -> env
        | _ -> assert false
        in
        let stmt = mk_Dstmt (Seval e) ~loc in
        let prog_main, prog_ret =
          match state.prog.ret with
            | ret::tr -> (stmt::ret), tr
            | _ -> assert false
        in
        mk_state state ~prog_main ~prog_ret ~env
      | _ ->
        let f e =
          [mk_Dstmt (Sreturn e) ~loc]
        in
        let stmt = mk_Dstmt (Seval e) ~loc in
        mk_state state ~stack:(f::state.stack) ~prog_main:(stmt::state.prog.main)
    end

  | Sbreak ->
    begin match state.prog.brk, state.prog.cont with
    | [], [] -> assert false
    | e1::k1, _e2::k2 -> mk_state state ~prog_main:e1 ~prog_brk:k1 ~prog_cont:k2
    | _ -> assert false
    end

  | Scontinue ->
    begin match state.prog.cont with
    | [] -> assert false
    | e::_ -> mk_state state ~prog_main:e
    end

  | Sassert _ | Slabel _ -> state

and block (state: state) match_value =
  match match_value with
    | Dstmt x -> stmt state x
    | Ddef (id, params, _, b) ->
      Hashtbl.replace (get_current_env state).funcs id.id_str ((List.map (fun (e: Py_ast.ident) -> e.id_str) params), b);
      state
    | _ -> assert false

let step (state: state): state =
  match state.prog.main with
  | [] -> assert false
  | s::k ->
      let state = mk_state state ~prog_main:k in
      block state s

let little_steps path =
  let c = open_in path in
  let file = Py_lexer.parse path c in
  let prog = {main=file; brk=[]; ret=[]; cont=[]} in
  let state = ref {stack=[]; prog=prog; env=[mk_new_env ()]} in
  while !state.stack <> [] || !state.prog.main <> [] do
    let _ = read_line () in
    Printf.printf "%s\n" (asprintf "%a" block_to_string !state.prog.main);
    state := step !state;
  done


let () = little_steps Sys.argv.(1)
