(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(** Task transformation *)

type 'a trans = task -> 'a
type 'a tlist = 'a list trans

let identity   x = x
let identity_l x = [x]

let conv_res c f x = c (f x)

let singleton f x = [f x]

let compose f g x = g (f x)

let compose_l f g x = list_apply g (f x)

let apply f x = f x

module WHtask = Hashweak.Make (struct
  type t = task_hd
  let tag t = t.task_tag
end)

let store fn = WHtask.memoize_option 63 fn

let fold fn v =
  let h = WHtask.create 63 in
  let rewind acc task =
    let acc = fn task acc in
    WHtask.set h task acc;
    acc
  in
  let current task =
    try Some (WHtask.find h task)
    with Not_found -> None
  in
  let rec accum todo = function
    | None -> List.fold_left rewind v todo
    | Some task -> begin match current task with
        | Some v -> List.fold_left rewind v todo
        | None   -> accum (task::todo) task.task_prev
      end
  in
  accum []

let fold_l fn v = fold (fun task -> list_apply (fn task)) [v]

let fold_map   fn v t = conv_res snd                (fold   fn (v, t))
let fold_map_l fn v t = conv_res (List.rev_map snd) (fold_l fn (v, t))

let map   fn = fold   (fun t1 t2 -> fn t1 t2)
let map_l fn = fold_l (fun t1 t2 -> fn t1 t2)

module WHdecl = Hashweak.Make (struct
  type t = decl
  let tag d = d.d_tag
end)

let gen_decl add fn =
  let fn = WHdecl.memoize 63 fn in
  let fn task acc = match task.task_decl.td_node with
    | Decl d -> List.fold_left add acc (fn d)
    | _ -> add_tdecl acc task.task_decl
  in
  map fn

let gen_decl_l add fn =
  let fn = WHdecl.memoize 63 fn in
  let fn task acc = match task.task_decl.td_node with
    | Decl d -> List.rev_map (List.fold_left add acc) (fn d)
    | _ -> [add_tdecl acc task.task_decl]
  in
  map_l fn

let decl    = gen_decl   add_decl
let decl_l  = gen_decl_l add_decl
let tdecl   = gen_decl   add_tdecl
let tdecl_l = gen_decl_l add_tdecl

let rewrite fnT fnF = decl (fun d -> [decl_map fnT fnF d])

