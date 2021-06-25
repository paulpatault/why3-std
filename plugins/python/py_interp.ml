
open Why3
open Py_ast

let input = ref (fun _ -> failwith "todo")
let print = ref (fun _ -> failwith "todo")

type value =
  | Vnone
  | Vint    of BigInt.t
  | Vbool   of bool
  | Vlist   of value Vector.t
  | Vstring of string

type var = (string, value) Hashtbl.t
type func = (string, string list * block) Hashtbl.t
type env = { var: var; func: func; }

let rec expr (env: env) (e: expr): value =
  match e.expr_desc with
  | _ -> failwith "??"

and stmt (env: env) (s: stmt): unit =
  match s.stmt_desc with
  | _ -> failwith "??"

and block (env: env) (b: block): unit =
  match b with
  | _ -> failwith "??"

let interp _file =
  Format.printf "42@."

let () =
  let file = Sys.argv.(1) in
  let c = open_in file in
  let file = Py_lexer.parse file c in
  interp file
