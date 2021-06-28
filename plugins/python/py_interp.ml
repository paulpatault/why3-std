
open Why3
open Py_ast

(* let input = ref (fun _ -> failwith "todo")
let print = ref (fun _ -> failwith "todo") *)

type value =
  | Vnone
  | Vbool   of bool
  | Vint    of BigInt.t
  | Vlist   of value Vector.t
  | Vstring of string

let rec print_value = function
  | Vnone       -> Format.printf "None"
  | Vbool true  -> Format.printf "True"
  | Vbool false -> Format.printf "False"
  | Vint n      -> Format.printf "%s" (BigInt.to_string n)
  | Vstring s   -> Format.printf "%s" s
  | Vlist v ->
    let len = Vector.length v in
    Format.printf "[";
    for i = 0 to len-1 do
      print_value (Vector.get v i);
      if i < len-1 then Format.printf ", "
    done;
    Format.printf "]"

type var = (string, value) Hashtbl.t
type func = (string, string list * block) Hashtbl.t
type env = { vars: var; funcs: func; }


let py_div n1 n2 =
  let q = BigInt.euclidean_div n1 n2 in
  if BigInt.sign n2 >= 0 then q
  else
    let m = BigInt.euclidean_mod n1 n2 in
    if BigInt.sign m >= 0 then BigInt.sub q BigInt.one
    else q

let py_mod n1 n2 =
  let r = BigInt.euclidean_mod n1 n2 in
  if BigInt.sign n2 >= 0 then r
  else
    if BigInt.sign r > 0 then BigInt.add r n2
    else r

let binop_op = function
  | Badd -> BigInt.add
  | Bsub -> BigInt.sub
  | Bmul -> BigInt.mul
  | Bdiv -> py_div
  | Bmod -> py_mod
  | _    -> assert false

let binop_comp = function
  | Beq  -> (=)
  | Bneq -> (<>)
  | Blt  -> (<)
  | Ble  -> (<=)
  | Bgt  -> (>)
  | Bge  -> (>=)
  | _    -> assert false

let binop_logic = function
  | Band -> (&&)
  | Bor ->  (||)
  | _    -> assert false

let rec expr (env: env) (e: expr): value =
  match e.expr_desc with
  | Enone     -> Vnone
  | Ebool b   -> Vbool b
  | Eint s    -> Vint (BigInt.of_string s)
  | Estring s -> Vstring s
  | Eident x  ->
      begin try Hashtbl.find env.vars x.id_str
      with Not_found -> assert false end
  | Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod as b, e1, e2) ->
      begin match expr env e1, expr env e2 with
      | Vint n1, Vint n2 -> let b = binop_op b in Vint (b n1 n2)
      | _ -> assert false end
  | Ebinop (Beq | Bneq | Blt | Ble | Bgt | Bge as b, e1, e2) ->
      begin match expr env e1, expr env e2 with
      | Vint n1, Vint n2 -> let b = binop_comp b in Vbool (b n1 n2)
      | _ -> assert false end
  | Ebinop (Band | Bor as b, e1, e2) ->
      begin match expr env e1, expr env e2 with
      | Vbool v1, Vbool v2 -> let b = binop_logic b in Vbool (b v1 v2)
      | _ -> assert false end
  | Eunop (u, e) ->
      let v = expr env e in
      begin match u, v with
      | Uneg, Vint n  -> Vint (BigInt.minus n)
      | Unot, Vbool b -> Vbool (not b)
      | _ -> assert false end
  | Ecall (id, params) ->
      begin try
        let _f = Hashtbl.find env.funcs id.id_str in
        assert false
      with Not_found -> assert false end
  | Edot (e, id, params) ->
      assert false
  | Elist l ->
      let v = Vector.create ~dummy:Vnone ~capacity:0 in
      List.iter (fun e -> Vector.push v (expr env e)) l;
      Vlist v
  | Emake (e1, e2) ->
      let e1 = expr env e1 in
      let e2 = expr env e2 in
      let n = match e2 with
      | Vint n -> BigInt.to_int n
      | _ -> assert false in
      let v = Vector.make ~dummy:Vnone n e1 in
      Vlist v

  | Eget (e1, e2) ->
      begin match expr env e1, expr env e2 with
        | Vlist v, Vint i  -> 
          let i = if BigInt.sign i < 0 then BigInt.add (BigInt.of_int (Vector.length v)) i else i in
          begin try Vector.get v (BigInt.to_int i)
          with Invalid_argument _s -> assert false end
        | _ -> assert false
      end

and stmt (env: env) (s: stmt): unit =
  match s.stmt_desc with
  | Sblock b ->
      block env b
  | Sif (e, b1, b2) ->
      begin match expr env e with
      | Vbool true  -> block env b1
      | Vbool false -> block env b2
      | _ -> assert false
      end
  | Sreturn e -> assert false
  | Sassign (id, e) -> assert false
  | Swhile (e, _, _, b) -> assert false
  | Sfor (id, e, _, b) -> assert false
  | Seval e -> expr env e |> print_value; Format.printf "\n"
  | Sset (e1, e2, e3) -> assert false
  | Sassert _ -> assert false (* of Expr.assertion_kind * Ptree.term *)
  | Sbreak -> assert false
  | Scontinue -> assert false
  | Slabel id -> assert false

and block (env: env) (b: block): unit =
  match b with
  | [] -> ()
  | e::k ->
      begin match e with
      | Dstmt s -> stmt env s
      | Ddef (id, params, _, b) -> assert false
      | Dlogic _ | Dimport _ -> ()
      end;
      block env k

let interp file =
  let vars = Hashtbl.create 10 in
  let funcs = Hashtbl.create 10 in
  let env = { vars;funcs } in
  block env file
  (* Format.printf "42@." *)

let () =
  let file = Sys.argv.(1) in
  let c = open_in file in
  let file = Py_lexer.parse file c in
  interp file
