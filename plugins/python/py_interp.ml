
open Why3
open Py_ast

let () = Random.self_init ()
(* let input = ref (fun _ -> failwith "todo")
let print = ref (fun _ -> failwith "todo") *)

type value =
  | Vnone
  | Vbool   of bool
  | Vint    of BigInt.t
  | Vlist   of value Vector.t
  | Vstring of string

let rec type_to_string = function
  | Vnone     -> "NoneType"
  | Vbool _   -> "bool"
  | Vint _    -> "int"
  | Vstring _ -> "str"
  | Vlist _   -> "list"

let binop_to_string = function
  | Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "*"
  | Bdiv -> "//"
  | Bmod -> "%"
  | Beq  -> "=="
  | Bneq -> "!="
  | Blt  -> "<"
  | Ble  -> "<="
  | Bgt  -> ">"
  | Bge  -> ">="
  | Band -> "and"
  | Bor ->  "or"

let unop_to_string = function
  | Uneg -> "-"
  | Unot -> "not"

let rec value_to_string ftm = function
  | Vnone       -> "None"
  | Vbool true  -> "True"
  | Vbool false -> "False"
  | Vint n      -> BigInt.to_string n
  | Vstring s   -> s
  | Vlist v     -> Format.sprintf "[%a]" list_content_str (v, 0)

and list_content_str ftm (vec, i) =
  if i = Vector.length vec then ""
  else if i + 1 = Vector.length vec
  then Format.sprintf "%a" value_to_string (Vector.get vec i)
  else Format.sprintf "%a, %a" value_to_string (Vector.get vec i) list_content_str (vec, (i+1))

type var = (string, value) Hashtbl.t
type func = (string, string list * block) Hashtbl.t
type env = { vars: var; funcs: func; }

let mk_new_env () =
  { vars = Hashtbl.create 10; funcs = Hashtbl.create 10 }

exception Break
exception Continue
exception Return of value

let transform_idx v idx =
  if BigInt.sign idx < 0 then BigInt.add (BigInt.of_int (Vector.length v)) idx else idx

let print_env e =
  Printf.printf "ENV VARS: [\n";
  (* Hashtbl.iter (fun s v -> Format.sprintf "  %s := %a@." s value_to_string v) e.vars;
  Printf.printf "]\n";
  Printf.printf "ENV FUNCS: [\n";
  Hashtbl.iter (fun s (sl, _) -> Printf.printf "  %s(%s)\n" s (String.concat "," sl)) e.funcs; *)
  Printf.printf "]\n"

let py_div_mod n1 n2 =
  let q, r = BigInt.euclidean_div_mod n1 n2 in
  if BigInt.sign n2 >= 0 then (q, r)
  else
    let q = if BigInt.sign r > 0 then BigInt.sub q BigInt.one else q in
    let r = if BigInt.sign r > 0 then BigInt.add r n2 else r in
    (q, r)

let py_div n1 n2 = fst (py_div_mod n1 n2)
let py_mod n1 n2 = snd (py_div_mod n1 n2)

let rec py_compare v1 v2 ~loc =
  match v1, v2 with
  | Vbool b1,   Vbool b2   -> Bool.compare b1 b2
  | Vint n1,    Vint n2    -> BigInt.compare n1 n2
  | Vstring s1, Vstring s2 -> String.compare s1 s2
  | Vlist l1, Vlist l2 ->
        let vtol v =
          let rec aux acc = function
            | -1 -> acc
            | i -> aux (Vector.get v i :: acc) (i-1)
          in aux [] (Vector.length v - 1) in
        List.compare (py_compare ~loc) (vtol l1) (vtol l2)
  | _ ->
      Loc.errorm ~loc
        "TypeError: comparison not supported between instances of '%s' and '%s'"
        (type_to_string v1) (type_to_string v2)

let binop_op = function
  | Badd -> BigInt.add
  | Bsub -> BigInt.sub
  | Bmul -> BigInt.mul
  | Bdiv -> py_div
  | Bmod -> py_mod
  | _    -> assert false

let binop_comp ~loc = function
  | Beq  -> fun e1 e2 -> py_compare ~loc e1 e2 =  0
  | Bneq -> fun e1 e2 -> py_compare ~loc e1 e2 <> 0
  | Blt  -> fun e1 e2 -> py_compare ~loc e1 e2 <  0
  | Ble  -> fun e1 e2 -> py_compare ~loc e1 e2 <= 0
  | Bgt  -> fun e1 e2 -> py_compare ~loc e1 e2 >  0
  | Bge  -> fun e1 e2 -> py_compare ~loc e1 e2 >= 0
  | _    -> assert false

let binop_logic = function
  | Band -> (&&)
  | Bor ->  (||)
  | _    -> assert false

module Primitives =
  struct

    type t = (string, loc:Loc.position -> value list -> value) Hashtbl.t
    let list_func_table:t = Hashtbl.create 6
    let std_func_table:t = Hashtbl.create 6

    let input ~loc vl =
      let aux s =
        Printf.printf "%s" s;
        read_line ()
      in
      match vl with
        | [v] -> Vstring (aux (Format.sprintf "%a" value_to_string v))
        | []  -> Vstring (aux "")
        | l   -> Loc.errorm ~loc
            "TypeError: input expected at most 1 argument, got %d" (List.length l)

    let int ~loc = function
      | [Vint i] -> Vint i
      | [Vbool b] ->
          if b then Vint (BigInt.one)
          else Vint (BigInt.zero)
      | [Vstring s] ->
          begin try Vint (BigInt.of_string s)
          with Failure _ ->
            Loc.errorm ~loc
            "ValueError: invalid literal for int() with base 10: '%s'" s
          end
      | [v] -> Loc.errorm ~loc
          "int() argument must be a string, a number or a bool, not '%s'"
          (type_to_string v)
      | l -> Loc.errorm ~loc "TypeError: int expected 1 argument, got %d" (List.length l)

    let print ~loc vl =
      let rec aux vl =
        match vl with
          | [v] -> Format.sprintf "%a" value_to_string v
          | v::lv -> Format.sprintf "%a %s" value_to_string v (aux lv)
          | _ -> ""
      in
      Format.printf "%s\n" (aux vl);
      Vnone

    let randint ~loc = function
      | [Vint lo; Vint hi] ->
          let lo = BigInt.to_int lo in
          let hi = BigInt.to_int hi in
          if hi < lo then Loc.errorm ~loc "ValueError: empty range for randint(%d, %d)" lo hi;
          Vint (BigInt.of_int (Random.int (hi + 1) + lo))
      | [v1; v2] -> Loc.errorm ~loc
          "TypeError: randint() arguments must be int, not '%s' and '%s'"
          (type_to_string v1) (type_to_string v2)
      | l -> Loc.errorm ~loc "TypeError: randint expected 2 arguments, got %d" (List.length l)

  let range ~loc vl =
      let aux lo hi =
        let lo = BigInt.to_int lo in
        let hi = BigInt.to_int hi in
        if lo > hi then Loc.errorm ~loc "ValueError: empty range for range(%d, %d)" lo hi
        else
          let v = Vector.make (hi - lo) (Vint BigInt.zero) in
          for i=lo to hi-1 do
            Vector.set v (i - lo) (Vint (BigInt.of_int i));
          done;
          Vlist v
      in
      match vl with
        | [Vint hi] ->
            aux BigInt.zero hi
        | [v] ->
            Loc.errorm ~loc "TypeError: range() arguments must be int, not '%s'" (type_to_string v)
        | [Vint lo; Vint hi] ->
            aux lo hi
        | [v1; v2] ->
            Loc.errorm ~loc
              "TypeError: range() arguments must be int, not '%s' and '%s'"
              (type_to_string v1) (type_to_string v2)
        | [Vint le; Vint ri; Vint step] ->
            let le = BigInt.to_int le in
            let ri = BigInt.to_int ri in
            let step = BigInt.to_int step in
            if (le > ri || step <= 0) && (ri > le || step >= 0) then
              Loc.errorm ~loc "ValueError: empty range for range(%d, %d)" le ri step
            else
              let len = (ri - le) / step + if (ri -le) mod step <> 0 then 1 else 0 in
              let v = Vector.make len (Vint BigInt.zero) in
              for i=0 to len-1 do
                Vector.set v i (Vint (BigInt.of_int (le + i * step)));
              done;
              Vlist v
        | [v1; v2; v3] ->
            Loc.errorm ~loc
              "TypeError: range() arguments must be int, not '%s', '%s' and '%s'"
              (type_to_string v1) (type_to_string v2) (type_to_string v3)
        | [] ->
            Loc.errorm ~loc "TypeError: range expected at least 1 argument, got 0"
        | l ->
            Loc.errorm ~loc
              "TypeError: range expected at most 3 arguments, got %d"
              (List.length l)

    let type_error m args i =
      Format.sprintf "TypeError: list.%s() takes exactly %s argument (%d given)" m args i

    let attribute_error t m =
      Format.sprintf "AttributeError: '%s' object has no attribute '%s'" (type_to_string t) m

    let pop ~loc = function
      | [Vlist v] ->
          begin try Vector.pop v
          with Vector.Empty ->
            Loc.errorm ~loc "IndexError: pop from empty list"
          end
      | Vlist v::l ->
          Loc.errorm ~loc "%s" (type_error "pop" "zero" (List.length l))
      | v::l ->
          Loc.errorm ~loc "%s" (attribute_error v "pop")
      | [] -> assert false

    let append ~loc = function
      | [Vlist v; x] -> Vector.push v x; Vnone
      | Vlist v::l -> Loc.errorm ~loc "%s" (type_error "append" "one" (List.length l))
      | v::l -> Loc.errorm ~loc "%s" (attribute_error v "append")
      | [] -> assert false

    let copy ~loc = function
      | [Vlist l] -> Vlist (Vector.copy l)
      | Vlist v::l -> Loc.errorm ~loc "%s" (type_error "copy" "zero" (List.length l))
      | v::l -> Loc.errorm ~loc "%s" (attribute_error v "copy")
      | [] -> assert false

    let clear ~loc = function
      | [Vlist l] -> Vector.clear l; Vnone
      | Vlist v::l -> Loc.errorm ~loc "%s" (type_error "clear" "zero" (List.length l))
      | v::l -> Loc.errorm ~loc "%s" (attribute_error v "clear")
      | [] -> assert false

    let reverse ~loc = function
      | [Vlist l] ->
          let len = Vector.length l in
          let n = (len / 2) - 1 in
          for i=0 to n do
            let temp = Vector.get l i in
            Vector.set l i (Vector.get l (len - i - 1));
            Vector.set l (len - i - 1) temp
          done;
          Vnone
      | Vlist v::l -> Loc.errorm ~loc "%s" (type_error "reverse" "zero" (List.length l))
      | v::l -> Loc.errorm ~loc "%s" (attribute_error v "reverse")
      | [] -> assert false

    let sort ~loc = function
      | [Vlist l] ->
          Vector.sort (py_compare ~loc) l;
          Vnone
      | Vlist v::l ->
          Loc.errorm ~loc "%s" (type_error "sort" "zero" (List.length l))
      | v::l ->
          Loc.errorm ~loc "%s" (attribute_error v "sort")
      | [] -> assert false

    let slice ~loc vl =
      let aux lo hi l =
        if lo < 0 then assert false
        else if hi > Vector.length l then 
          Loc.errorm ~loc "ValueError: empty range for list[%d:%d]" lo hi
        else if hi < lo then
          Loc.errorm ~loc "ValueError: empty range for list[%d:%d]" lo hi
        else
          let len = hi - lo in
          Vlist (Vector.sub l lo len)
      in
      match vl with
        | [Vlist l; Vnone; Vnone] ->
            aux 0 (Vector.length l) l
        | [Vlist l; Vnone; Vint hi] ->
            aux 0 (transform_idx l hi |> BigInt.to_int) l
        | [Vlist l; Vint lo; Vnone] ->
            aux (transform_idx l lo |> BigInt.to_int) (Vector.length l) l
        | [Vlist l; Vint lo; Vint hi] ->
            let lo = transform_idx l lo |> BigInt.to_int in
            let hi = transform_idx l hi |> BigInt.to_int in
            aux lo hi l
        | Vlist v::l ->
            Loc.errorm ~loc "%s" (type_error "slice" "two" (List.length l))
        | v::l ->
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
      Hashtbl.add std_func_table "print" print;
      Hashtbl.add std_func_table "range" range;
      Hashtbl.add std_func_table "input" input;
      Hashtbl.add std_func_table "randint" randint;
      Hashtbl.add std_func_table "slice" slice;

  end

let rec expr (env: env) (e: expr): value =
  match e.expr_desc with
  | Enone     -> Vnone
  | Ebool b   -> Vbool b
  | Eint s    -> Vint (BigInt.of_string s)
  | Estring s -> Vstring s
  | Eident x  ->
      begin try
        Hashtbl.find env.vars x.id_str
      with Not_found ->
        Loc.errorm ~loc:e.expr_loc "NameError: name '%s' is not defined" x.id_str
      end
  | Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as b, e1, e2) ->
      begin match expr env e1, expr env e2 with
      | Vint n1, Vint n2 -> let b = binop_op b in Vint (b n1 n2)
      | v1, v2 ->
          let t1 = type_to_string v1 in
          let t2 = type_to_string v2 in
          let b = binop_to_string b in
          Loc.errorm ~loc:e.expr_loc
            "TypeError: unsupported operand type(s) for %s: '%s' and '%s'"
            b t1 t2
      end
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as b, e1, e2) ->
      let e1 = expr env e1 in
      let e2 = expr env e2 in
      let b = binop_comp b in
      Vbool (b ~loc:e.expr_loc e1 e2)
  | Ebinop (Band | Bor as b, e1, e2) ->
      begin match expr env e1, expr env e2 with
      | Vbool v1, Vbool v2 -> let b = binop_logic b in Vbool (b v1 v2)
      | v1, v2 ->
          let t1 = type_to_string v1 in
          let t2 = type_to_string v2 in
          let b = binop_to_string b in
          Loc.errorm ~loc:e.expr_loc
            "TypeError: unsupported operand type(s) for %s: '%s' and '%s'"
            b t1 t2
      end
  | Eunop (u, e) ->
      let v = expr env e in
      begin match u, v with
      | Uneg, Vint n  -> Vint (BigInt.minus n)
      | Unot, Vbool b -> Vbool (not b)
      | _ ->
          let t = type_to_string v in
          let u = unop_to_string u in
          Loc.errorm ~loc:e.expr_loc
            "TypeError: bad operand type for unary %s: '%s'" u t
      end
  | Ecall (id, params) ->
      begin try
        let f = Hashtbl.find Primitives.std_func_table id.id_str in
        f (List.map (fun e -> expr env e) params) ~loc:e.expr_loc
      with Not_found ->
        begin try
          let id_params, b = Hashtbl.find env.funcs id.id_str in
          let envf = {vars = Hashtbl.create 10; funcs = env.funcs} in
          begin try
            List.iter2 (fun id e -> Hashtbl.add envf.vars id (expr env e)) id_params params;
            begin try block envf b; Vnone
            with Return v -> v end
          with Invalid_argument _ ->
            Loc.errorm ~loc:e.expr_loc
              "TypeError: %s() takes %d positional argument but %d were given"
              id.id_str (List.length id_params) (List.length params)
          end
        with Not_found ->
          Loc.errorm ~loc:e.expr_loc "NameError: name '%s' is not defined" id.id_str
        end
      end
  | Edot (e, id, params) ->
      begin try
        let f = Hashtbl.find Primitives.list_func_table id.id_str in
        let params = List.map (expr env) (e::params) in
        f params ~loc:e.expr_loc
      with Not_found ->
          Loc.errorm ~loc:e.expr_loc
            "AttributeError: 'list' object has no attribute '%s'" id.id_str
      end
  | Elist l ->
      let v = Vector.create ~dummy:Vnone ~capacity:0 in
      List.iter (fun e -> Vector.push v (expr env e)) l;
      Vlist v
  | Emake (e1, e2) ->
      let e1 = expr env e1 in
      let e2 = expr env e2 in
      let n = match e2 with
        | Vint n -> BigInt.to_int n
        | _ -> Loc.errorm ~loc:e.expr_loc
            "TypeError: can't multiply sequence by non-int of type '%s'" (type_to_string e2)
      in
      Vlist (Vector.make ~dummy:Vnone n e1)
  | Eget (e1, e2) ->
      begin match expr env e1, expr env e2 with
        | Vlist v, Vint i ->
          begin try
            let idx = transform_idx v i |> BigInt.to_int in
            let res = Vector.get v idx in
            Printf.printf "%s\n" (string_of_int idx);
            Printf.printf "taille = %d\n" (Vector.length v);
            print_endline (Format.sprintf "%a@." value_to_string res);
            res
          with Invalid_argument _ ->
            Loc.errorm ~loc:e.expr_loc "IndexError: list index out of range"
          end
        | Vlist _, non_int ->
            Loc.errorm ~loc:e.expr_loc
              "TypeError: list indices must be integers or slices, not %s"
              (type_to_string non_int)
        | x, _ ->
            Loc.errorm ~loc:e.expr_loc
              "TypeError: '%s' object is not subscriptable" (type_to_string x)
      end

and stmt (env: env) (s: stmt): unit =
  match s.stmt_desc with
  | Sblock b ->
      block env b
  | Sif (e, b1, b2) ->
      if bool env e then block env b1
      else block env b2
  | Sreturn e ->
      let e = expr env e in
      raise (Return e)
  | Sassign (id, e) ->
      let e = expr env e in
      Hashtbl.remove env.vars id.id_str;
      Hashtbl.add env.vars id.id_str e
  | Swhile (e, _, _, b) ->
      begin try
        while bool env e do
          begin try block env b
          with Continue -> () end
        done;
      with Break -> () end
  | Sfor (id, e, _, b) ->
      begin match expr env e with
      | Vlist l ->
          begin try
            Vector.iter (fun li ->
              Hashtbl.add env.vars id.id_str li;
              try block env b
              with Continue -> ()
            ) l
          with Break -> () end
      | non_list -> Loc.errorm ~loc:e.expr_loc
          "TypeError: '%s' object is not iterable"
          (type_to_string non_list)
      end;
  | Seval e -> let _ = expr env e in ()
  | Sset (e1, e2, e3) ->
    let e1 = expr env e1 in
    let e2 = expr env e2 in
    let e3 = expr env e3 in
    begin match e1, e2, e3 with
      | Vlist v, Vint i, e ->
          begin try
            Vector.set v (transform_idx v i |> BigInt.to_int) e
          with Invalid_argument _ ->
            Loc.errorm ~loc:s.stmt_loc "IndexError: list index out of range"
          end
        | Vlist _, non_int, _ ->
            Loc.errorm ~loc:s.stmt_loc
              "TypeError: list indices must be integers or slices, not %s"
              (type_to_string non_int)
        | x, _, _ ->
            Loc.errorm ~loc:s.stmt_loc
              "TypeError: '%s' object is not subscriptable" (type_to_string x)
    end
  | Sbreak -> raise Break
  | Scontinue -> raise Continue
  | Sassert _ | Slabel _ -> ()

and block (env: env) (b: block): unit =
  match b with
  | [] -> ()
  | e::k ->
      begin match e with
      | Dstmt s -> stmt env s
      | Ddef (id, params, _, b) ->
        Hashtbl.remove env.funcs id.id_str;
        Hashtbl.add env.funcs id.id_str (List.map (fun (e: Py_ast.ident) -> e.id_str) params, b)
      | Dlogic _ | Dimport _ -> ()
      end;
      block env k

and bool (env: env) (e: expr): bool =
  match expr env e with
  | Vbool b  -> b
  | non_bool -> Loc.errorm ~loc:e.expr_loc
      "TypeError: conditions must be booleans, not %s"
      (type_to_string non_bool)

let interp file =
  let env = mk_new_env () in
  block env file
  (* print_env env *)

let () =
  let file = Sys.argv.(1) in
  let c = open_in file in
  let file = Py_lexer.parse file c in
  interp file
