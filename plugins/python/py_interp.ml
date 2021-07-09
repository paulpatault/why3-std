
open Why3
open Py_ast
open Format

let () = Random.self_init ()

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
  stack: ((expr -> block) list) list;
  prog: prog;
  env: env list;
}

let print_ref = ref (fun (_s:string) -> ())
let input_ref = ref (fun (s:string) (_state:state) -> ())
let continue = ref true

module Pprinter =
  struct
    let type_const fmt = function
      | Enone     -> fprintf fmt "NoneType"
      | Ebool _   -> fprintf fmt "bool"
      | Eint _    -> fprintf fmt "int"
      | Estring _ -> fprintf fmt "str"
      | Evector _   -> fprintf fmt "list"

    let binop fmt = function
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

    let ident fmt (i: Py_ast.ident) =
      fprintf fmt "%s" i.id_str

    let unop fmt = function
      | Uneg -> fprintf fmt "-"
      | Unot -> fprintf fmt "not"

    let rec const fmt = function
      | Enone     -> fprintf fmt "None"
      | Ebool b   -> if b then fprintf fmt "True" else fprintf fmt "False"
      | Eint s    -> fprintf fmt "%s" s
      | Estring s -> fprintf fmt "%s" s
      | Evector v -> const_list fmt v

    and const_list fmt vec =
      let rec aux fmt (v, i) =
        if i = Vector.length v then ()
        else if i + 1 = Vector.length v
        then fprintf fmt "%a" const (get_vec v i)
        else fprintf fmt "%a, %a" const (get_vec v i) aux (v, (i+1))
      in
      fprintf fmt "[%a]" aux (vec, 0)

    let rec expr fmt e =
      match e.expr_desc with
      | Econst a -> const fmt a
      | Eident i -> ident fmt i
      | Ebinop (b, e1, e2) ->
        fprintf fmt "%a %a %a" expr e1 binop b expr e2
      | Eunop (u, e) ->
        fprintf fmt "%a %a" unop u expr e
      | Ecall (i, el) ->
        fprintf fmt "%a(%a)" ident i expr_list el
      | Edot (e, i, el) ->
        fprintf fmt "%a.%a(%a)" expr e ident i expr_list el
      | Elist el ->
        fprintf fmt "[%a]" expr_list el
      | Emake (e1, e2) ->
        fprintf fmt "[%a] * %a" expr e1 expr e2
      | Eget (e1, e2) ->
        fprintf fmt "%a[%a]" expr e1 expr e2
    and expr_list fmt = function
      | [] -> ()
      | [e] -> fprintf fmt "%a" expr e
      | e::k -> fprintf fmt "%a, %a" expr e expr_list k

    let rec stmt fmt s =
      match s.stmt_desc with
      | Sblock b ->
        block fmt b
      | Sif (e, b1, b2) ->
          begin match b2 with
          | [] ->
            fprintf fmt "@[<v 4>if %a:%a@]" expr e block b1
          | _  ->
            fprintf fmt "@[<v 4>if %a:%a@]@,@[<v 4>else:%a@]" expr e block b1 block b2
          end
      | Sreturn e ->
        fprintf fmt "return %a" expr e
      | Sassign (i, e) ->
        fprintf fmt "%a = %a" ident i expr e
      | Swhile (e, _, _, b) ->
          fprintf fmt "@[<v 4>while %a:%a@]" expr e block b
      | Sfor (i, e, _, b) ->
          fprintf fmt "@[<v 4>for %a in %a:%a@]" ident i expr e block b
      | Seval e ->
        expr fmt e
      | Sset (e1, e2, e3) ->
        fprintf fmt "%a[%a] = %a@ " expr e1 expr e2 expr e3
      | Sbreak -> fprintf fmt "break"
      | Scontinue -> fprintf fmt "continue"
      | _ -> ()

    and decl fmt = function
      | Ddef _ | Dimport _ | Dlogic _ -> ()
      | Dstmt s -> fprintf fmt "@,@[<v 4>%a@]" stmt s

    and block fmt = function
      | [] -> ()
      | [e] -> fprintf fmt "%a@," decl e
      | e::k -> fprintf fmt "%a@,%a" decl e block k

  end



let transform_idx v idx =
  if BigInt.sign idx < 0 then BigInt.add (BigInt.of_int (Vector.length v)) idx else idx

let rec py_compare v1 v2 ~loc =
  match v1, v2 with
  | Ebool b1,   Ebool b2   -> Bool.compare b1 b2
  | Eint n1,    Eint n2    -> BigInt.compare (BigInt.of_string n1) (BigInt.of_string n2)
  | Estring s1, Estring s2 -> String.compare s1 s2
  | Evector l1, Evector l2 ->
        let vtol v =
          let rec aux acc = function
            | -1 -> acc
            | i -> aux (get_vec v i :: acc) (i-1)
          in aux [] (Vector.length v - 1) in
        List.compare (py_compare ~loc) (vtol l1) (vtol l2)
  | _ ->
      Loc.errorm ~loc
        "TypeError: comparison not supported between instances of '%a' and '%a'"
        Pprinter.type_const v1 Pprinter.type_const v2

module Primitives =
  struct

    type t = (string, loc:Loc.position -> atom list -> atom) Hashtbl.t
    let list_func_table:t = Hashtbl.create 6
    let std_func_table:t = Hashtbl.create 6

    let vector_to_list v =
      let rec aux idx acc =
        if idx = Vector.length v then List.rev acc
        else
          aux (idx + 1) ((Vector.get v idx)::acc)
      in
      aux 0 []

    let input ~loc vl state =
      match vl with
      | [c] -> !input_ref (asprintf "%a" Pprinter.const c) state
      | []  -> !input_ref "" state
      | l   -> Loc.errorm ~loc
          "TypeError: input expected at most 1 argument, got %d" (List.length l)

    let int ~loc = function
      | [Eint i] -> Eint i
      | [Ebool b] ->
          if b then Eint "1"
          else Eint "0"
      | [Estring s] ->
          begin try Eint (BigInt.of_string s |> BigInt.to_string)
          with Failure _ ->
            Loc.errorm ~loc
            "ValueError: invalid literal for int() with base 10: '%s'" s
          end
      | [v] -> Loc.errorm ~loc
          "int() argument must be a string, a number or a bool, not '%a'"
          Pprinter.type_const v
      | l -> Loc.errorm ~loc "TypeError: int expected 1 argument, got %d" (List.length l)

    let len ~loc = function
      | [Evector v] ->
          Eint (Vector.length v |> string_of_int)
      | v::[] ->
          Loc.errorm ~loc "TypeError: object of type '%a' has no len()" Pprinter.type_const v
      | l ->
          Loc.errorm ~loc "TypeError: len() takes exactly one argument (%d given)" (List.length l)

    let print ~loc vl =
      let rec aux = function
        | [v] -> !print_ref (asprintf "%a@." Pprinter.const v)
        | v::lv -> !print_ref (asprintf "%a " Pprinter.const v); aux lv
        | [] -> ()
      in aux vl;
      Enone

    let randint ~loc = function
      | [Eint lo; Eint hi] ->
          let lo = BigInt.of_string lo in
          let hi = BigInt.of_string hi in
          let lo' = BigInt.to_int lo in
          let hi' = BigInt.to_int hi in
          if BigInt.compare lo hi > 0
          then Loc.errorm ~loc "ValueError: empty range for randint(%d, %d)" lo' hi';
          Eint (BigInt.of_int (Random.int (hi' - lo' + 1) + lo') |> BigInt.to_string)
      | [v1; v2] -> Loc.errorm ~loc
          "TypeError: randint() arguments must be int, not '%a' and '%a'"
          Pprinter.type_const v1 Pprinter.type_const v2
      | l -> Loc.errorm ~loc "TypeError: randint expected 2 arguments, got %d" (List.length l)

  let range ~loc vl =
      let aux lo hi =
        let lo' = BigInt.to_int lo in
        let hi' = BigInt.to_int hi in
        if BigInt.compare lo hi > 0
        then Loc.errorm ~loc "ValueError: empty range for range(%d, %d)" lo' hi'
        else
          let v = Vector.make (hi' - lo') (Eint "0") in
          for i=lo' to hi'-1 do
            set_vec v (i - lo') (Eint (BigInt.of_int i |> BigInt.to_string));
          done;
          Evector v
      in
      match vl with
        | [Eint hi] ->
            aux BigInt.zero (BigInt.of_string hi)
        | [v] ->
            Loc.errorm ~loc "TypeError: range() arguments must be int, not '%a'" Pprinter.type_const v
        | [Eint lo; Eint hi] ->
            aux (BigInt.of_string lo) (BigInt.of_string hi)
        | [v1; v2] ->
            Loc.errorm ~loc
              "TypeError: range() arguments must be int, not '%a' and '%a'"
              Pprinter.type_const v1 Pprinter.type_const v2
        | [Eint le; Eint ri; Eint step] ->
            let le = BigInt.of_string le |> BigInt.to_int in
            let ri = BigInt.of_string ri |> BigInt.to_int in
            let step = BigInt.of_string step |> BigInt.to_int in
            if (le > ri || step <= 0) && (ri > le || step >= 0)
            then Loc.errorm ~loc "ValueError: empty range for range(%d, %d)" le ri step
            else
              let len = (ri - le) / step + if (ri -le) mod step <> 0 then 1 else 0 in
              let v = Vector.make len (Eint "0") in
              for i=0 to len-1 do
                set_vec v i (Eint (BigInt.of_int (le + i * step) |> BigInt.to_string));
              done;
              Evector v
        | [v1; v2; v3] ->
            Loc.errorm ~loc
              "TypeError: range() arguments must be int, not '%a', '%a' and '%a'"
              Pprinter.type_const v1 Pprinter.type_const v2 Pprinter.type_const v3
        | [] ->
            Loc.errorm ~loc "TypeError: range expected at least 1 argument, got 0"
        | l ->
            Loc.errorm ~loc
              "TypeError: range expected at most 3 arguments, got %d"
              (List.length l)

    let type_error m args i =
      sprintf "TypeError: list.%s() takes exactly %s argument (%d given)" m args i

    let attribute_error t m =
      sprintf "AttributeError: '%s' object has no attribute '%s'"
        (asprintf "%a" Pprinter.type_const t) m

    let pop ~loc = function
      | [Evector v] ->
          begin try Vector.pop v
          with Vector.Empty ->
            Loc.errorm ~loc "IndexError: pop from empty list"
          end
      | Evector _v::l ->
          Loc.errorm ~loc "%s" (type_error "pop" "zero" (List.length l))
      | v::_l ->
          Loc.errorm ~loc "%s" (attribute_error v "pop")
      | [] -> assert false

    let append ~loc = function
      | [Evector v; x] -> Vector.push v x; Enone
      | Evector _v::l -> Loc.errorm ~loc "%s" (type_error "append" "one" (List.length l))
      | v::_l -> Loc.errorm ~loc "%s" (attribute_error v "append")
      | [] -> assert false

    let copy ~loc = function
      | [Evector l] -> Evector (Vector.copy l)
      | Evector _v::l -> Loc.errorm ~loc "%s" (type_error "copy" "zero" (List.length l))
      | v::_l -> Loc.errorm ~loc "%s" (attribute_error v "copy")
      | [] -> assert false

    let clear ~loc = function
      | [Evector l] -> Vector.clear l; Enone
      | Evector _v::l -> Loc.errorm ~loc "%s" (type_error "clear" "zero" (List.length l))
      | v::_l -> Loc.errorm ~loc "%s" (attribute_error v "clear")
      | [] -> assert false

    let reverse ~loc = function
      | [Evector l] ->
          let len = Vector.length l in
          let n = (len / 2) - 1 in
          for i=0 to n do
            let temp = get_vec l i in
            set_vec l i (get_vec l (len - i - 1));
            set_vec l (len - i - 1) temp
          done;
          Enone
      | Evector _v::l -> Loc.errorm ~loc "%s" (type_error "reverse" "zero" (List.length l))
      | v::_l -> Loc.errorm ~loc "%s" (attribute_error v "reverse")
      | [] -> assert false

    let sort ~loc = function
      | [Evector l] ->
          Vector.sort (py_compare ~loc) l;
          Enone
      | Evector _v::l ->
          Loc.errorm ~loc "%s" (type_error "sort" "zero" (List.length l))
      | v::_l ->
          Loc.errorm ~loc "%s" (attribute_error v "sort")
      | [] -> assert false

    let slice ~loc vl =
      let aux lo hi l =
        if lo < 0 then Loc.errorm ~loc "ValueError: list index out of range"
        else if hi > Vector.length l then
          Loc.errorm ~loc "ValueError: empty range for list[%d:%d]" lo hi
        else if hi < lo then
          Loc.errorm ~loc "ValueError: empty range for list[%d:%d]" lo hi
        else
          let len = hi - lo in
          Evector (Vector.sub l lo len)
      in
      match vl with
        | [Evector l; Enone; Enone] ->
            aux 0 (Vector.length l) l
        | [Evector l; Enone; Eint hi] ->
            let hi = BigInt.of_string hi in
            aux 0 (transform_idx l hi |> BigInt.to_int) l
        | [Evector l; Eint lo; Enone] ->
            let lo = BigInt.of_string lo in
            aux (transform_idx l lo |> BigInt.to_int) (Vector.length l) l
        | [Evector l; Eint lo; Eint hi] ->
            let lo = BigInt.of_string lo in
            let hi = BigInt.of_string hi in
            let lo = transform_idx l lo |> BigInt.to_int in
            let hi = transform_idx l hi |> BigInt.to_int in
            aux lo hi l
        | Evector _v::l ->
            Loc.errorm ~loc "%s" (type_error "slice" "two" (List.length l))
        | v::_l ->
            Loc.errorm ~loc "%s" (attribute_error v "slice")
        | [] -> assert false

    let () =
      Hashtbl.add list_func_table "pop" pop;
      Hashtbl.add list_func_table "append" append;
      Hashtbl.add list_func_table "copy" copy;
      Hashtbl.add list_func_table "clear" clear;
      Hashtbl.add list_func_table "reverse" reverse;
      Hashtbl.add list_func_table "sort" sort;

      Hashtbl.add std_func_table "int" int;
      Hashtbl.add std_func_table "len" len;
      Hashtbl.add std_func_table "print" print;
      Hashtbl.add std_func_table "range" range;
      Hashtbl.add std_func_table "randint" randint;
      Hashtbl.add std_func_table "slice" slice;

  end


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
      Pprinter.const v1 Pprinter.const v2

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
  let main = match prog_main with None -> state.prog.main | Some prog -> prog in
  let brk = match prog_brk with None -> state.prog.brk | Some prog -> prog in
  let cont = match prog_cont with None -> state.prog.cont | Some prog -> prog in
  let ret = match prog_ret with None -> state.prog.ret | Some prog -> prog in
  let env = match env with None -> state.env | Some env -> env in
  let prog = {main; brk; cont; ret} in
  {stack; prog; env}

let mk_Dstmt stmt_desc ~loc =
  Dstmt {stmt_desc; stmt_loc=loc}

let mk_stmt stmt_desc ~loc =
  {stmt_desc; stmt_loc=loc}

let mk_expr expr_desc ~loc =
  {expr_desc; expr_loc=loc}

let get_current_env state =
  match state.env with
  | env::_ -> env
  | [] -> assert false

let append_to_current_stack state f =
  match state.stack with
  | [] -> [[f]]
  | stack::rest -> (f::stack)::rest

let concat_to_current_stack state fl =
  match state.stack with
  | [] -> [fl]
  | stack::rest -> (fl@stack)::rest

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
    | [] -> state
    | []::stack -> state
    | (f::k)::rest ->
      let app = f match_value in
      mk_state state ~stack:(k::rest) ~prog_main:(app@state.prog.main)
    end

  | Elist l ->
    begin match l with
    | [] ->
        let vec = Econst (Evector (Vector.create ~capacity:0 ~dummy:Enone)) in
        let dstmt = mk_Dstmt (Seval (mk_expr vec ~loc)) ~loc in
        mk_state state ~prog_main:(dstmt::state.prog.main)
    | _  ->
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
        let expr = mk_expr (Econst (Evector !r)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in

      let l = List.map (fun e -> mk_Dstmt (Seval e) ~loc:e.expr_loc) l in
      mk_state state ~stack:(concat_to_current_stack state (stack@[f])) ~prog_main:(l@state.prog.main)
    end

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
      | c1, c2, b -> Loc.errorm ~loc
          "TypeError: unsupported operand type(s) for %a: '%a' and '%a'"
          Pprinter.binop b Pprinter.type_const c1 Pprinter.type_const c2
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
        mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
      end
    | _e1, _e2 ->
      let f e1 =
        let expr = mk_expr (Ebinop (b, e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc:e1.expr_loc in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
    end

  | Eunop (u, e) ->
    begin match u, e.expr_desc with
    | Uneg, Econst (Eint n)  ->
      let n = BigInt.of_string n in
      let expr = mk_expr (Econst (Eint (BigInt.minus n |> BigInt.to_string))) ~loc in
      let stmt = mk_Dstmt (Seval expr) ~loc in
      mk_state state ~prog_main:(stmt::state.prog.main)
    | Uneg, Econst c ->
      Loc.errorm ~loc "TypeError: bad operand type for unary %a: '%a'"
        Pprinter.unop u Pprinter.type_const c
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
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
    end

  | Eident (x: Why3.Ptree.ident)  ->
      begin try
        let env = get_current_env state in
        let e = Hashtbl.find env.vars x.id_str in
        let stmt = mk_Dstmt (Seval e) ~loc in
        mk_state state ~prog_main:(stmt::state.prog.main)
      with Not_found ->
        Loc.errorm ~loc "NameError: name '%a' is not defined" Pprinter.ident x
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
      | _ -> Loc.errorm ~loc
        "TypeError: can't multiply sequence by non-int of type '%a'" Pprinter.type_const c2

      end
    | Econst _c, _e2 ->
      let f e2 =
        let expr = mk_expr (Emake (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e2) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)

    | _e1, _e2 ->
      let f e1 =
        let expr = mk_expr (Emake (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
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
        with Invalid_argument _ -> Loc.errorm ~loc "IndexError: list index out of range" end
      | Evector v, non_int ->
        Loc.errorm ~loc
          "TypeError: list indices must be integers or slices, not %a"
          Pprinter.type_const non_int
      | non_list, _e ->
        Loc.errorm ~loc
          "TypeError: '%a' object is not subscriptable" Pprinter.type_const non_list
      end
    | Econst _c, _e2 ->
      let f e2 =
        let expr = mk_expr (Eget (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e2) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)

    | _e1, _e2 ->
      let f e1 =
        let expr = mk_expr (Eget (e1, e2)) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
    end

  | Ecall (id, el) ->
    let not_const () =
      let f e =
        let expr = mk_expr (Ecall(id, [e])) ~loc in
        [mk_Dstmt (Seval expr) ~loc]
      in
      let expr = mk_expr (Elist el) ~loc in
      let stmt = mk_Dstmt (Seval expr) ~loc in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(stmt::state.prog.main)
    in

    if id.id_str = "input" then
      match el with
        | [{expr_desc=Econst (Evector params)}] ->
          Primitives.input ~loc (Primitives.vector_to_list params) state;
          continue := false;
          state
        | [] ->
          Primitives.input ~loc [] state;
          continue := false;
          state
        | _ -> not_const ()
    else

      begin try
      let f = Hashtbl.find Primitives.std_func_table id.id_str in
      match el with
        | [{expr_desc=Econst (Evector params)}] ->
          let expr = mk_expr (Econst (f ~loc (Primitives.vector_to_list params))) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog_main:(stmt::state.prog.main)
        | [] ->
          let expr = mk_expr (Econst (f ~loc [])) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog_main:(stmt::state.prog.main)
        | _ -> not_const ()
      with Not_found ->
      begin try

        let params_id, b = Hashtbl.find (get_current_env state).funcs id.id_str in
        let none_expr = mk_expr (Econst Enone) ~loc in
        let ret_none = mk_Dstmt (Sreturn none_expr) ~loc in
        let b = b@[ret_none] in

        begin match el with
          | [{expr_desc=Econst (Evector params)}] ->
            let envf = {vars = Hashtbl.create 10; funcs = (get_current_env state).funcs} in
            let idx = ref 0 in
            if List.length params_id <> Vector.length params
            then
              Loc.errorm ~loc
                "TypeError: %a() takes %d positional argument but %d were given"
                Pprinter.ident id (List.length params_id) (Vector.length params)
            else
              List.iter
                (fun id ->
                  Hashtbl.add envf.vars id (mk_expr (Econst (Vector.get params !idx)) ~loc);
                  incr idx)
                params_id;
              mk_state state
                ~prog_main:(b@state.prog.main)
                ~prog_ret:(state.prog.main::state.prog.ret)
                ~env:(envf::state.env)
                ~stack:([]::state.stack)
          | [] ->
            if List.length params_id <> 0 then
              Loc.errorm ~loc
                "TypeError: %a() takes %d positional argument but 0 were given"
                Pprinter.ident id (List.length params_id)
            else

            let envf = {vars = Hashtbl.create 10; funcs = (get_current_env state).funcs} in
            mk_state state
              ~prog_main:(b@state.prog.main)
              ~prog_ret:(state.prog.main::state.prog.ret)
              ~env:(envf::state.env)
              ~stack:([]::state.stack)
          | _ -> not_const ()
        end
      with Not_found ->
        Loc.errorm ~loc "NameError: name '%a' is not defined" Pprinter.ident id end
      end

  | Edot (l, id, params) ->
    begin try
      let f = Hashtbl.find Primitives.list_func_table id.id_str in
      begin match l.expr_desc, params with
        | Econst (Evector _v as l), [{expr_desc=Econst (Evector params)}] ->
          let params = l::(Primitives.vector_to_list params) in
          let expr = mk_expr (Econst (f ~loc params)) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog_main:(stmt::state.prog.main)
        | Econst (Evector v), [] ->
          let expr = mk_expr (Econst (f ~loc [])) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~prog_main:(stmt::state.prog.main)
        | _ ->
          let f e =
            begin match e.expr_desc with
              | Econst (Evector v) ->
                let l, params = get_hd_tl_vec ~loc:e.expr_loc v in
                let expr = mk_expr (Edot(l, id, [params])) ~loc in
                [mk_Dstmt (Seval expr) ~loc]
              | _ -> assert false
            end
          in
          let expr = mk_expr (Elist (l::params)) ~loc in
          let stmt = mk_Dstmt (Seval expr) ~loc in
          mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(stmt::state.prog.main)
      end
    with Not_found ->
      Loc.errorm ~loc "AttributeError: 'list' object has no attribute '%a'" Pprinter.ident id
    end

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
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(stmt::state.prog.main)
    end

  | Sassign (id, e) ->
    let f e =
      let env = get_current_env state in
      Hashtbl.replace env.vars id.id_str e;
      []
    in
    let e = mk_Dstmt (Seval e) ~loc in
    mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)

  | Sfor (id, e, _inv, b) ->

    let hd =
      match get_hd state.prog.cont with
      | Dstmt m::_ -> Some m
      | _          -> None
    in

    let first =
      match hd with
      | Some {stmt_desc=Sfor(_, _, _, b');_} -> not (b' == b)
      | _      -> true in

    let prog_brk =
      if first then
        state.prog.main::state.prog.brk
      else
        state.prog.brk
    in

    begin match e.expr_desc with
    | Econst (Evector v) ->
        begin
            try
              let hd_vec = mk_expr (Econst (Vector.pop v)) ~loc in
              let tl_vec = mk_expr (Econst (Evector v)) ~loc in

              let env = (get_current_env state).vars in
              Hashtbl.replace env id.id_str hd_vec;
              let stmt = mk_Dstmt (Sfor(id, tl_vec, _inv, b)) ~loc in
              let prog_main = b@stmt::state.prog.main in

              let prog_cont =
                match state.prog.cont with
                | [] -> assert false
                | hd::tl ->
                    if not first then (stmt::state.prog.main)::tl
                  else (stmt::state.prog.main)::state.prog.cont
              in

              mk_state state ~prog_main ~prog_brk ~prog_cont
            with Vector.Empty ->
              let prog_brk, prog_cont = loop_out (state.prog.brk, state.prog.cont) in
              mk_state state ~prog_brk ~prog_cont
        end
    | Econst c ->
      Loc.errorm ~loc:e.expr_loc "TypeError: '%a' object is not iterable" Pprinter.const c
    | _v ->
      let f e =
        match e.expr_desc with
        | Econst x ->
          let _ = Primitives.reverse [x] ~loc in
          [mk_Dstmt (Sfor(id, e, _inv, b)) ~loc]
        | _ -> assert false
      in
      let e = mk_Dstmt (Seval e) ~loc in
      let prog_cont = (Dstmt match_value::state.prog.main)::state.prog.cont in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main) ~prog_brk ~prog_cont
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
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main) ~prog_brk ~prog_cont
    end

  | Sset (e1, e2, e3) ->
    begin match e1.expr_desc, e2.expr_desc, e3.expr_desc with
    | Econst (Evector v), Econst (Eint i), Econst c ->
      let i = BigInt.of_string i |> transform_idx v |> BigInt.to_int in
      begin try
        set_vec v i c;
        state
      with Invalid_argument _ ->
        Loc.errorm ~loc "IndexError: list index out of range"
      end
    | Econst (Evector v), Econst non_int, Econst c ->
        Loc.errorm ~loc:e2.expr_loc
          "TypeError: list indices must be integers or slices, not %a"
          Pprinter.type_const non_int
    | Econst (Evector _v), _e2, Econst _c ->
      let f e2 =
        [mk_Dstmt (Sset (e1, e2, e3)) ~loc]
      in
      let e = mk_Dstmt (Seval e2) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
    | Econst non_vec, Econst _, Econst c ->
      Loc.errorm ~loc:e1.expr_loc
        "TypeError: '%a' object is not subscriptable" Pprinter.type_const non_vec
    | _e1, _e2, Econst _c ->
      let f e1 =
        [mk_Dstmt (Sset (e1, e2, e3)) ~loc]
      in
      let e = mk_Dstmt (Seval e1) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
    | _e1, _e2, _e3 ->
      let f e3 =
        [mk_Dstmt (Sset (e1, e2, e3)) ~loc]
      in
      let e = mk_Dstmt (Seval e3) ~loc; in
      mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(e::state.prog.main)
    end

  | Sreturn e ->
    begin match e.expr_desc with
      | Econst _c ->
        let env = match state.env with
        | _::[] -> Loc.errorm ~loc "SyntaxError: 'return' outside function"
        | _::env -> env
        | _ -> assert false
        in

        let stack = match state.stack with
          | [] -> Loc.errorm ~loc "SyntaxError: 'return' outside function"
          | _::stack -> stack
        in

        let stmt = mk_Dstmt (Seval e) ~loc in
        let prog_main, prog_ret =
          match state.prog.ret with
            | ret::tr -> (stmt::ret), tr
            | [] -> Loc.errorm ~loc "SyntaxError: 'return' outside function"
        in
        mk_state state ~prog_main ~prog_ret ~env ~stack
      | _ ->
        let f e =
          [mk_Dstmt (Sreturn e) ~loc]
        in
        let stmt = mk_Dstmt (Seval e) ~loc in
        mk_state state ~stack:(append_to_current_stack state f) ~prog_main:(stmt::state.prog.main)
    end

  | Sbreak ->
    begin match state.prog.brk, state.prog.cont with
    | [], [] -> Loc.errorm ~loc "SyntaxError: 'break' outside loop"
    | e1::k1, _e2::k2 -> mk_state state ~prog_main:e1 ~prog_brk:k1 ~prog_cont:k2
    | _ -> assert false
    end

  | Scontinue ->
    begin match state.prog.cont with
    | [] -> Loc.errorm ~loc "SyntaxError: 'continue' outside loop"
    | e::_ -> mk_state state ~prog_main:e
    end

  | Sassert _ | Slabel _ -> state

and block (state: state) match_value =
  match match_value with
    | Dstmt x -> stmt state x
    | Ddef (id, params, _, b) ->
      Hashtbl.replace (get_current_env state).funcs id.id_str ((List.map (fun (e: Py_ast.ident) -> e.id_str) params), b);
      state
    | _ -> state

let step (state: state): state =
  match state.prog.main with
  | [] -> assert false
  | s::k ->
      let state = mk_state state ~prog_main:k in
      block state s

let interpreter (code:string) (input: string -> state -> unit) (print: string -> unit): unit =
  print_ref := print;
  input_ref := input;
  let file = Py_lexer.parse_str code in
  let prog = {main=file; brk=[]; ret=[]; cont=[]} in
  let state = ref {stack=[[]]; prog=prog; env=[mk_new_env ()]} in
  while (!state.stack <> [[]] || !state.prog.main <> []) && !continue do
  (* let _ = read_line () in
    Printf.printf "-----Pile %d------\n%s\n-----------"
      (List.length !state.stack)
      (asprintf "%a" Pprinter.decl (List.hd !state.prog.main)); *)
    state := step !state;
  done

let read_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let () =
  let input = fun s state -> () in
  let print = fun s -> Printf.printf "%s" s in
  let code = read_file Sys.argv.(1) in
  interpreter code input print
