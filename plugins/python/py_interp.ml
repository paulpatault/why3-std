
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

let rec value_to_string = function
  | Vnone       -> Format.sprintf "None"
  | Vbool true  -> Format.sprintf "True"
  | Vbool false -> Format.sprintf "False"
  | Vint n      -> Format.sprintf "%s" (BigInt.to_string n)
  | Vstring s   -> Format.sprintf "%s" s
  | Vlist v ->
    let len = Vector.length v in
    let res = ref "[" in
    for i = 0 to len-1 do
      res := !res ^ value_to_string (Vector.get v i);
      if i < len-1 then res := !res ^ ", "
    done;
    res := !res ^ "]"; !res

type var = (string, value) Hashtbl.t
type func = (string, string list * block) Hashtbl.t
type env = { vars: var; funcs: func; }

let print_env e =
  Printf.printf "ENV: [\n";
  Hashtbl.iter (fun s v -> Printf.printf "  %s := %s\n" s (value_to_string v)) e.vars;
  Printf.printf "]\n"

let transform_idx v idx = 
  if BigInt.sign idx < 0 then BigInt.add (BigInt.of_int (Vector.length v)) idx else idx

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
  | Beq  -> BigInt.eq
  | Bneq -> fun e1 e2 -> not (BigInt.eq e1 e2)
  | Blt  -> BigInt.lt
  | Ble  -> BigInt.le
  | Bgt  -> BigInt.gt
  | Bge  -> BigInt.ge
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
      | Vint n1, Vint n2 ->
          let b = binop_comp b in Vbool (b n1 n2)
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
      let n =
        match e2 with
        | Vint n -> BigInt.to_int n
        | _ -> assert false in
      Vlist (Vector.make ~dummy:Vnone n e1)
  | Eget (e1, e2) ->
      begin match expr env e1, expr env e2 with
        | Vlist v, Vint i  ->
          begin try Vector.get v (transform_idx v i |> BigInt.to_int)
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
  | Sassign (id, e) ->
      let e = expr env e in
      Hashtbl.remove env.vars id.id_str;
      Hashtbl.add env.vars id.id_str e
  | Swhile (e, _, _, b) ->
      begin match expr env e with
      | Vbool true  -> block env b; stmt env s
      | Vbool false -> ()
      | _ -> assert false
      end
  | Sfor (id, e, _, b) -> assert false
  | Seval e -> Printf.printf "%s\n" (value_to_string (expr env e)); Format.printf "\n"
  | Sset (e1, e2, e3) ->
    let e1 = expr env e1 in
    let e2 = expr env e2 in
    let e3 = expr env e3 in
    begin match e1, e2, e3 with
      | Vlist v, Vint i, e ->
      begin try Vector.set v (transform_idx v i |> BigInt.to_int) e
      with Invalid_argument s -> assert false end
      | _ -> assert false
    end
  | Sassert _ -> () (* of Expr.assertion_kind * Ptree.term *)
  | Sbreak -> assert false
  | Scontinue -> assert false
  | Slabel _ -> ()

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

let interp file =
  let vars = Hashtbl.create 10 in
  let funcs = Hashtbl.create 10 in
  let env = { vars;funcs } in
  block env file

let () =
  let file = Sys.argv.(1) in
  let c = open_in file in
  let file = Py_lexer.parse file c in
  interp file
