(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3

let usage_msg = sprintf
  "Usage: %s [options] <file> <module>.<ident>...\n\
   Run the interpreter on the given module symbols.\n"
  (Filename.basename Sys.argv.(0))

let opt_file = ref None
let opt_exec = Queue.create ()

let add_opt x =
  if !opt_file = None then opt_file := Some x else
  match Strings.split '.' x with
  | [m;i] -> Queue.push (m,i) opt_exec
  | _ ->
    Format.eprintf "extra arguments must be of the form 'module.ident'@.";
    exit 1

(* Used for real numbers approximation *)
let prec = ref None

let opt_parser = ref None

let enable_rac = ref false

let option_list =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    KLong "real", Hnd1 (APair (',', AInt, APair (',', AInt, AInt)),
      fun (i1, (i2, i3)) -> prec := Some (i1, i2, i3)),
    "<emin>,<emax>,<prec> set format used for real computations\n\
     (e.g., -148,128,24 for float32)";
    KLong "rac", Hnd0 (fun () -> enable_rac := true),
    " enable runtime basic runtime assertion checking"
  ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None then Whyconf.Args.exit_with_usage option_list usage_msg

let do_input f =
  let format = !opt_parser in
  let mm = match f with
    | "-" ->
        Env.read_channel Pmodule.mlw_language ?format env "stdin" stdin
    | file ->
        let (mlw_files, _) =
          Env.read_file Pmodule.mlw_language ?format env file in
        mlw_files
  in
  let do_exec (mod_name, fun_name) =
    try
      let open Pinterp in
      let {Pmodule.mod_known= known}, rs = find_global_symbol mm ~mod_name ~fun_name in
      let locals, body = find_global_fundef known rs in
      Opt.iter init_real !prec;
      ( try
          let res = eval_global_fundef ~rac:!enable_rac env known locals body in
          printf "%a@." (report_eval_result ~mod_name ~fun_name body) res;
          exit (match res with Pinterp.Normal _, _ -> 0 | _ -> 1);
        with Contr (ctx, term) ->
          printf "%a@." (report_cntr ~mod_name ~fun_name body) (ctx, term) ;
          exit 1 )
    with Not_found ->
      exit 1 in
  Queue.iter do_exec opt_exec

let () =
  try
    Opt.iter do_input !opt_file
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
