(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Ity
open Expr
open Pdecl

(** *)

type prog_symbol =
  | PV of pvsymbol
  | RS of rsymbol

type namespace = {
  ns_ts : itysymbol   Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_xs : xsymbol     Mstr.t;  (* exception symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ps = Mstr.empty;
  ns_xs = Mstr.empty;
  ns_ns = Mstr.empty;
}

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vn else
  raise (ClashSymbol x)

let psym_equal p1 p2 = match p1,p2 with
  | PV p1, PV p2 -> pv_equal p1 p2
  | RS p1, RS p2 -> rs_equal p1 p2
  | _, _ -> false

let rec merge_ns chk ns1 ns2 =
  if ns1 == ns2 then ns1 else
  let join eq x n o = Some (ns_replace eq chk x o n) in
  let ns_union eq m1 m2 =
    if m1 == m2 then m1 else Mstr.union (join eq) m1 m2 in
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ts = ns_union its_equal ns1.ns_ts ns2.ns_ts;
    ns_ps = ns_union psym_equal ns1.ns_ps ns2.ns_ps;
    ns_xs = ns_union xs_equal ns1.ns_xs ns2.ns_xs;
    ns_ns = Mstr.union fusion ns1.ns_ns ns2.ns_ns; }

let add_ns chk x ns m = Mstr.change (function
  | Some os -> Some (merge_ns chk ns os)
  | None    -> Some ns) x m

let ns_add eq chk x vn m = Mstr.change (function
  | Some vo -> Some (ns_replace eq chk x vo vn)
  | None    -> Some vn) x m

let add_xs chk x xs ns = { ns with ns_xs = ns_add xs_equal   chk x xs ns.ns_xs }
let add_ts chk x ts ns = { ns with ns_ts = ns_add its_equal  chk x ts ns.ns_ts }
let add_ps chk x ps ns = { ns with ns_ps = ns_add psym_equal chk x ps ns.ns_ps }
let add_ns chk x nn ns = { ns with ns_ns = add_ns            chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_prog_symbol = ns_find (fun ns -> ns.ns_ps)
let ns_find_ns          = ns_find (fun ns -> ns.ns_ns)
let ns_find_xs          = ns_find (fun ns -> ns.ns_xs)
let ns_find_its         = ns_find (fun ns -> ns.ns_ts)

let ns_find_pv ns s = match ns_find_prog_symbol ns s with
  | PV pv -> pv | _ -> raise Not_found

let ns_find_rs ns s = match ns_find_prog_symbol ns s with
  | RS rs -> rs | _ -> raise Not_found

(** {2 Module} *)

type pmodule = {
  mod_theory : theory;        (* pure theory *)
  mod_units  : mod_unit list; (* module declarations *)
  mod_export : namespace;     (* exported namespace *)
  mod_known  : known_map;     (* known identifiers *)
  mod_local  : Sid.t;         (* locally declared idents *)
  mod_used   : Sid.t;         (* used modules *)
}

and mod_unit =
  | Udecl  of pdecl
  | Uuse   of pmodule
  | Uclone of mod_inst
  | Umeta  of meta * meta_arg list
  | Uscope of string * bool * mod_unit list

and mod_inst = {
  mi_mod : pmodule;
  mi_ty  : ity Mts.t;
  mi_ts  : itysymbol Mts.t;
  mi_ls  : lsymbol Mls.t;
  mi_pr  : prsymbol Mpr.t;
  mi_pv  : pvsymbol Mvs.t;
  mi_rs  : rsymbol Mrs.t;
  mi_xs  : xsymbol Mexn.t;
}

(** {2 Module under construction} *)

type pmodule_uc = {
  muc_theory : theory_uc;
  muc_units  : mod_unit list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
  muc_env    : Env.env;
}

let empty_module env n p = {
  muc_theory = create_theory ~path:p n;
  muc_units  = [];
  muc_import = [empty_ns];
  muc_export = [empty_ns];
  muc_known  = Mid.empty;
  muc_local  = Sid.empty;
  muc_used   = Sid.empty;
  muc_env    = env;
}

let close_module, restore_module =
  let h = Hid.create 17 in
  (fun uc ->
     let th = close_theory uc.muc_theory in (* catches errors *)
     let m = { mod_theory = th;
               mod_units  = List.rev uc.muc_units;
               mod_export = List.hd uc.muc_export;
               mod_known  = uc.muc_known;
               mod_local  = uc.muc_local;
               mod_used   = uc.muc_used; } in
     Hid.add h th.th_name m;
     m),
  (fun th -> Hid.find h th.th_name)

let open_scope uc s = match uc.muc_import with
  | ns :: _ -> { uc with
      muc_theory = Theory.open_scope uc.muc_theory s;
      muc_units  = [Uscope (s, false, uc.muc_units)];
      muc_import =       ns :: uc.muc_import;
      muc_export = empty_ns :: uc.muc_export; }
  | [] -> assert false

let close_scope uc ~import =
  let th = Theory.close_scope uc.muc_theory ~import in
  match List.rev uc.muc_units, uc.muc_import, uc.muc_export with
  | [Uscope (_,_,ul1)], _ :: sti, _ :: ste -> (* empty scope *)
      { uc with muc_theory = th;  muc_units  = ul1;
                muc_import = sti; muc_export = ste; }
  | Uscope (s,_,ul1) :: ul0, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with
          muc_theory = th;
          muc_units  = Uscope (s, import, ul0) :: ul1;
          muc_import = i1 :: sti;
          muc_export = e1 :: ste; }
  | _ -> assert false

let use_export uc ({mod_theory = mth} as m) =
  let th = Theory.use_export uc.muc_theory mth in
  let uc = if Sid.mem mth.th_name uc.muc_used then uc
    else { uc with
      muc_known = merge_known uc.muc_known m.mod_known;
      muc_used  = Sid.add mth.th_name uc.muc_used } in
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_theory = th;
      muc_units  = Uuse m :: uc.muc_units;
      muc_import = merge_ns false m.mod_export i0 :: sti;
      muc_export = merge_ns true  m.mod_export e0 :: ste; }
  | _ -> assert false

let add_meta uc m al = { uc with
  muc_theory = Theory.add_meta uc.muc_theory m al;
  muc_units  = Umeta (m,al) :: uc.muc_units; }

let store_path, store_module, restore_path =
  let id_to_path = Wid.create 17 in
  let store_path {muc_theory = uc} path id =
    (* this symbol already belongs to some theory *)
    if Wid.mem id_to_path id then () else
    let prefix = List.rev (id.id_string :: path @ uc.uc_prefix) in
    Wid.set id_to_path id (uc.uc_path, uc.uc_name.id_string, prefix) in
  let store_module {mod_theory = {th_name = id} as th} =
    (* this symbol is already a module *)
    if Wid.mem id_to_path id then () else
    Wid.set id_to_path id (th.th_path, id.id_string, []) in
  let restore_path id = Wid.find id_to_path id in
  store_path, store_module, restore_path

let close_module uc =
  let m = close_module uc in
  store_module m;
  m

let count_regions {muc_known = kn} {pv_ity = ity} mr =
  let add_reg r mr = Mreg.change (fun n -> Some (n <> None)) r mr in
  let meet mr1 mr2 = Mreg.union (fun _ x y -> Some (x || y)) mr1 mr2 in
  let join mr1 mr2 = Mreg.union (fun _ _ _ -> Some true) mr1 mr2 in
  let rec down mr ity = if ity.ity_imm then mr else
    match ity.ity_node with
    | Ityreg r -> fields (add_reg r mr) r.reg_its r.reg_args r.reg_regs
    | Ityapp (s,tl,rl) -> fields mr s tl rl
    | Ityvar _ -> assert false
  and fields mr s tl rl =
    if s.its_private && rl = [] then mr else
    let isb = its_match_regs s tl rl in
    let add_ity mr ity = down mr (ity_full_inst isb ity) in
    let add_proj mr f = add_ity mr f.rs_cty.cty_result in
    let add_field mr v = add_ity mr v.pv_ity in
    let d = find_its_defn kn s in
    if d.itd_constructors = [] then
      List.fold_left add_proj mr d.itd_fields
    else
      join mr (List.fold_left (fun mr c ->
        meet mr (List.fold_left add_field Mreg.empty c.rs_cty.cty_args))
        Mreg.empty d.itd_constructors) in
  down mr ity

let add_symbol add id v uc =
  store_path uc [] id;
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_import = add false id.id_string v i0 :: sti;
      muc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_pdecl_no_logic uc d =
  let uc = { uc with
    muc_units = Udecl d :: uc.muc_units;
    muc_known = known_add_decl uc.muc_known d;
    muc_local = Sid.union uc.muc_local d.pd_news } in
  let add_rs uc s = add_symbol add_ps s.rs_name (RS s) uc in
  let add_rs_noalias uc s = match s.rs_logic with
    | RLls _ | RLlemma ->
        let sv = s.rs_cty.cty_effect.eff_reads in
        let mr = Spv.fold (count_regions uc) sv Mreg.empty in
        Mreg.iter (fun _ n ->
          if n then Loc.errorm ?loc:s.rs_name.id_loc
            "The type of this function contains an alias") mr;
        add_rs uc s
    | _ -> add_rs uc s in
  let add_rd uc d = add_rs_noalias uc d.rec_sym in
  match d.pd_node with
  | PDtype tdl ->
      let add uc d =
        let uc = List.fold_left add_rs uc d.itd_fields in
        let uc = List.fold_left add_rs uc d.itd_constructors in
        add_symbol add_ts d.itd_its.its_ts.ts_name d.itd_its uc in
      List.fold_left add uc tdl
  | PDlet (LDvar (v,_)) -> add_symbol add_ps v.pv_vs.vs_name (PV v) uc
  | PDlet (LDsym (s,_)) -> add_rs_noalias uc s
  | PDlet (LDrec l) -> List.fold_left add_rd uc l
  | PDexn xs -> add_symbol add_xs xs.xs_name xs uc
  | PDpure -> uc

let add_pdecl uc d =
  let uc = add_pdecl_no_logic uc d in
  let th = List.fold_left (add_decl ~warn:true) uc.muc_theory d.pd_pure in
  { uc with muc_theory = th }

(** {2 Builtin symbols} *)

let dummy_env = Env.create_env []

let builtin_module =
  let uc = empty_module dummy_env (id_fresh "BuiltIn") ["why3";"BuiltIn"] in
  let uc = add_pdecl_no_logic uc pd_int in
  let uc = add_pdecl_no_logic uc pd_real in
  let uc = add_pdecl_no_logic uc pd_equ in
  let m = close_module uc in
  { m with mod_theory = builtin_theory }

let bool_module =
  let uc = empty_module dummy_env (id_fresh "Bool") ["why3";"Bool"] in
  let uc = add_pdecl_no_logic uc pd_bool in
  let m = close_module uc in
  { m with mod_theory = bool_theory }

let highord_module =
  let uc = empty_module dummy_env (id_fresh "HighOrd") ["why3";"HighOrd"] in
  let uc = use_export uc bool_module in
  let uc = add_pdecl_no_logic uc pd_func in
  let uc = add_pdecl_no_logic uc pd_func_app in
  let m = close_module uc in
  { m with mod_theory = highord_theory }

let tuple_module = Hint.memo 17 (fun n ->
  let nm = "Tuple" ^ string_of_int n in
  let uc = empty_module dummy_env (id_fresh nm) ["why3";nm] in
  let uc = add_pdecl_no_logic uc (pd_tuple n) in
  let m = close_module uc in
  { m with mod_theory = tuple_theory n })

let unit_module =
  let uc = empty_module dummy_env (id_fresh "Unit") ["why3";"Unit"] in
  let uc = use_export uc (tuple_module 0) in
  let td = create_alias_decl (id_fresh "unit") [] ity_unit in
  close_module (add_pdecl uc (create_type_decl [td]))

let create_module env ?(path=[]) n =
  let m = empty_module env n path in
  let m = use_export m builtin_module in
  let m = use_export m bool_module in
  let m = use_export m unit_module in
  m

let add_use uc d = Sid.fold (fun id uc ->
  if id_equal id ts_func.ts_name then
    use_export uc highord_module
  else match is_ts_tuple_id id with
  | Some n -> use_export uc (tuple_module n)
  | None -> uc) (Mid.set_diff d.pd_syms uc.muc_known) uc

let add_pdecl ~vc uc d =
  let uc = add_use uc d in
  let dl = if vc then Vc.vc uc.muc_env uc.muc_known d else [] in
  (* verification conditions might contain built-in symbols which
     do not occur in the original declaration, so we call add_use.
     However, we expect int.Int or any other library theory to
     be in the context: importing them automatically seems to be
     too invasive for the namespace. *)
  let uc = List.fold_left (fun uc d -> add_pdecl (add_use uc d) d) uc dl in
  add_pdecl uc d

(** {2 Cloning} *)

type clones = {
  cl_local : Sid.t;
  mutable ty_table : ity Mts.t;
  mutable ts_table : itysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
  mutable rn_table : region Mreg.t;
  mutable fd_table : pvsymbol Mpv.t;
  mutable pv_table : pvsymbol Mvs.t;
  mutable rs_table : rsymbol Mrs.t;
  mutable xs_table : xsymbol Mexn.t;
}

let empty_clones m = {
  cl_local = m.mod_local;
  ty_table = Mts.empty;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
  rn_table = Mreg.empty;
  fd_table = Mpv.empty;
  pv_table = Mvs.empty;
  rs_table = Mrs.empty;
  xs_table = Mexn.empty;
}

(* populate the clone structure *)

let rec sm_trans_ty tym tsm ty = match ty.ty_node with
  | Tyapp (s, tl) ->
      let tl = List.map (sm_trans_ty tym tsm) tl in
      begin match Mts.find_opt s tsm with
      | Some its -> ty_app its.its_ts tl
      | None -> begin match Mts.find_opt s tym with
      | Some ity -> ty_inst (ts_match_args s tl) (ty_of_ity ity)
      | None -> ty_app s tl
      end end
  | Tyvar _ -> ty

let clone_ty cl ty = sm_trans_ty cl.ty_table cl.ts_table ty

let cl_find_its cl its =
  if not (Sid.mem its.its_ts.ts_name cl.cl_local) then its
  else Mts.find its.its_ts cl.ts_table

let cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then ts
  else (Mts.find ts cl.ts_table).its_ts

let rec clone_ity cl ity = match ity.ity_node with
  | Ityreg r ->
      ity_reg (clone_reg cl r)
  | Ityapp (s, tl, rl) ->
      let tl = List.map (clone_ity cl) tl in
      let rl = List.map (clone_ity cl) rl in
      begin match Mts.find_opt s.its_ts cl.ts_table with
      | Some its -> ity_app_pure its tl rl
      | None -> (* creative indentation *)
      begin match Mts.find_opt s.its_ts cl.ty_table with
      | Some ity -> ity_full_inst (its_match_regs s tl rl) ity
      | None -> ity_app_pure s tl rl
      end end
  | Ityvar _ -> ity

and clone_reg cl reg =
  (* FIXME: what about top-level non-instantiated regions?
     We cannot check in cl.cl_local to see if they are there.
     Instead, we should prefill cl.pv_table and cl.rn_table
     with all top-level pvsymbols (local or external) before
     descending into a let_defn. *)
  try Mreg.find reg cl.rn_table with Not_found ->
  let id = id_clone reg.reg_vs.vs_name in
  let tl = List.map (clone_ity cl) reg.reg_args in
  let rl = List.map (clone_ity cl) reg.reg_regs in
  let r = match Mts.find_opt reg.reg_its.its_ts cl.ts_table with
    | Some its -> create_region id its tl rl
    | None -> (* creative indentation *)
    begin match Mts.find_opt reg.reg_its.its_ts cl.ty_table with
    | Some {ity_node = Ityreg r} ->
        let sbs = its_match_regs reg.reg_its tl rl in
        let tl = List.map (ity_full_inst sbs) r.reg_args in
        let rl = List.map (ity_full_inst sbs) r.reg_regs in
        create_region id r.reg_its tl rl
    | Some _ -> assert false
    | None -> create_region id reg.reg_its tl rl
    end in
  cl.rn_table <- Mreg.add reg r cl.rn_table;
  r

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls
  else Mls.find ls cl.ls_table

let clone_term cl mv t = t_gen_map (clone_ty cl) (cl_find_ls cl) mv t

let clone_fmla cl f = clone_term cl Mvs.empty f (* for closed terms *)

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else Mpr.find pr cl.pr_table

let cl_find_pv cl pv =
  if not (Sid.mem pv.pv_vs.vs_name cl.cl_local) then pv
  else Mvs.find pv.pv_vs cl.pv_table

let cl_find_rs cl rs =
  if not (Sid.mem rs.rs_name cl.cl_local) then rs
  else Mrs.find rs cl.rs_table

let cl_find_xs cl xs =
  if not (Sid.mem xs.xs_name cl.cl_local) then xs
  else Mexn.find xs cl.xs_table

let clone_ls inst cl ls =
  if Mls.mem ls inst.inst_ls then raise (CannotInstantiate ls.ls_name);
  let constr = ls.ls_constr in
  let id = id_clone ls.ls_name in
  let at = List.map (clone_ty cl) ls.ls_args in
  let vt = Opt.map (clone_ty cl) ls.ls_value in
  let ls' = create_lsymbol ~constr id at vt in
  cl.ls_table <- Mls.add ls ls' cl.ls_table;
  ls'

let cl_init_ty cl ({ts_name = id} as ts) ty =
  let its = restore_its ts and ity = ity_of_ty ty in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let stv = Stv.of_list ts.ts_args in
  if not (Stv.subset (ity_freevars Stv.empty ity) stv &&
    its_pure its && ity_immutable ity) then raise (BadInstance id);
  cl.ty_table <- Mts.add ts ity cl.ty_table

let cl_init_ts cl ({ts_name = id} as ts) ts' =
  let its = restore_its ts and its' = restore_its ts' in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  if not (List.length ts.ts_args = List.length ts'.ts_args &&
    its_pure its && its_pure its') then raise (BadInstance id);
  cl.ts_table <- Mts.add its.its_ts its' cl.ts_table

let cl_init_ls cl ({ls_name = id} as ls) ls' =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let mtch sb ty ty' = try ty_match sb ty' (clone_ty cl ty)
    with TypeMismatch _ -> raise (BadInstance id) in
  let sbs = match ls.ls_value,ls'.ls_value with
    | Some ty, Some ty' -> mtch Mtv.empty ty ty'
    | None, None -> Mtv.empty
    | _ -> raise (BadInstance id) in
  ignore (try List.fold_left2 mtch sbs ls.ls_args ls'.ls_args
    with Invalid_argument _ -> raise (BadInstance id));
  cl.ls_table <- Mls.add ls ls' cl.ls_table

let cl_init_pr cl {pr_name = id} _ =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id)

let cl_init m inst =
  let cl = empty_clones m in
  Mts.iter (cl_init_ty cl) inst.inst_ty;
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Mpr.iter (cl_init_pr cl) inst.inst_pr;
  cl

(* clone declarations *)

let clone_decl inst cl uc d = match d.d_node with
  | Dtype _ | Ddata _ -> assert false (* impossible *)
  | Dparam ls ->
      if Mls.mem ls inst.inst_ls then uc else
      let d = create_param_decl (clone_ls inst cl ls) in
      add_pdecl ~vc:false uc (create_pure_decl d)
  | Dlogic ldl ->
      let get_ls (ls,_) = ignore (clone_ls inst cl ls) in
      let get_logic (_,ld) =
        Opt.get (ls_defn_of_axiom (clone_fmla cl (ls_defn_axiom ld))) in
      List.iter get_ls ldl;
      let d = create_logic_decl (List.map get_logic ldl) in
      add_pdecl ~vc:false uc (create_pure_decl d)
  | Dind (s, idl) ->
      let get_ls (ls,_) = clone_ls inst cl ls in
      let get_case (pr,f) =
        if Mpr.mem pr inst.inst_pr then raise (CannotInstantiate pr.pr_name);
        let pr' = create_prsymbol (id_clone pr.pr_name) in
        cl.pr_table <- Mpr.add pr pr' cl.pr_table;
        pr', clone_fmla cl f in
      let get_ind ls (_,la) = ls, List.map get_case la in
      let lls = List.map get_ls idl in
      let d = create_ind_decl s (List.map2 get_ind lls idl) in
      add_pdecl ~vc:false uc (create_pure_decl d)
  | Dprop (k,pr,f) ->
      let skip, k' = match k, Mpr.find_opt pr inst.inst_pr with
        | Pgoal, _ -> true, Pgoal
        | Plemma, Some Pgoal -> true, Pgoal
        | Plemma, _ -> false, Plemma
        | Paxiom, Some k -> false, k
        | Paxiom, None -> false, Paxiom (* TODO: Plemma *) in
      if skip then uc else
      let pr' = create_prsymbol (id_clone pr.pr_name) in
      cl.pr_table <- Mpr.add pr pr' cl.pr_table;
      let d = create_prop_decl k' pr' (clone_fmla cl f) in
      add_pdecl ~vc:false uc (create_pure_decl d)

let cl_save_ls cl s s' =
  cl.ls_table <- Mls.add_new (CannotInstantiate s.ls_name) s s' cl.ls_table

let cl_save_rs cl s s' =
  cl.rs_table <- Mrs.add s s' cl.rs_table;
  begin match s.rs_field, s'.rs_field with
  | Some v, Some v' -> cl.fd_table <- Mpv.add v v' cl.fd_table
  | None, _ -> () (* can instantiate a non-field with a field *)
  | _ -> assert false (* but not vice versa *)
  end;
  match s.rs_logic, s'.rs_logic with
  | RLls s, RLls s' -> cl_save_ls cl s s'
  | RLlemma, RLlemma -> () (* TODO: update cl.pr_table? *)
  | RLnone, RLnone -> ()
  | _ -> assert false

let clone_type_decl inst cl tdl =
  let def =
    List.fold_left (fun m d -> Mits.add d.itd_its d m) Mits.empty tdl in
  let htd = Hits.create 5 in

  let rec visit alg ({its_ts = {ts_name = id} as ts} as s) d =
    if not (Hits.mem htd s) then
    let alg = Sits.add s alg in
    let id' = id_clone id in
    let cloned = Mts.mem ts inst.inst_ts || Mts.mem ts inst.inst_ty in
    let conv_pj v = create_pvsymbol
      (id_clone v.pv_vs.vs_name) ~ghost:v.pv_ghost (conv_ity alg v.pv_ity) in
    let save_itd itd =
      List.iter2 (cl_save_rs cl) d.itd_constructors itd.itd_constructors;
      List.iter2 (cl_save_rs cl) d.itd_fields itd.itd_fields;
      Hits.add htd s (Some itd) in
    (* alias *)
    if s.its_def <> None then begin
      if cloned then raise (CannotInstantiate id);
      let def = conv_ity alg (Opt.get s.its_def) in
      let itd = create_alias_decl id' ts.ts_args def in
      cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
      save_itd itd
    end else
    (* abstract *)
    if d.itd_fields = [] && d.itd_constructors = [] &&
                            d.itd_invariant = [] then begin
      if cloned then Hits.add htd s None else begin
        let itd = create_plain_record_decl id' ts.ts_args
          ~priv:s.its_private ~mut:s.its_mutable [] [] in
        cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
        save_itd itd
      end
    end else
    (* variant *)
    if not s.its_mutable && d.itd_constructors <> [] &&
                            d.itd_invariant = [] then begin
      if cloned then raise (CannotInstantiate id);
      let conv_fd m fd =
        let v = Opt.get fd.rs_field in Mpv.add v (conv_pj v) m in
      let fldm = List.fold_left conv_fd Mpv.empty d.itd_fields in
      let conv_pj pj = match Mpv.find_opt pj fldm with
        | Some pj' -> true, pj' | None -> false, conv_pj pj in
      let conv_cs cs =
        id_clone cs.rs_name, List.map conv_pj cs.rs_cty.cty_args in
      let csl = List.map conv_cs d.itd_constructors in
      match Mts.find_opt ts cl.ts_table with
      | Some s' ->
          let itd = create_rec_variant_decl s' csl in
          save_itd itd
      | None ->
          let itd = create_plain_variant_decl id' ts.ts_args csl in
          cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
          save_itd itd
    end else begin
    (* flat record *)
      if cloned then raise (CannotInstantiate id);
      let mfld = Spv.of_list s.its_mfields in
      let pjl = List.map (fun fd -> Opt.get fd.rs_field) d.itd_fields in
      let fdl = List.map (fun v -> Spv.mem v mfld, conv_pj v) pjl in
      let inv =
        if d.itd_invariant = [] then [] else
        let add mv u (_,v) = Mvs.add u.pv_vs v.pv_vs mv in
        let mv = List.fold_left2 add Mvs.empty pjl fdl in
        List.map (clone_term cl mv) d.itd_invariant in
      let itd = create_plain_record_decl id' ts.ts_args
        ~priv:s.its_private ~mut:s.its_mutable fdl inv in
      cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
      save_itd itd
    end

  and conv_ity alg ity =
    let rec down ity = match ity.ity_node with
      | Ityreg {reg_its = s; reg_args = tl}
      | Ityapp (s,tl,_) ->
          if Sits.mem s alg then begin
            if not (Mts.mem s.its_ts cl.ts_table) then
            let id = id_clone s.its_ts.ts_name in
            let s = create_itysymbol_rec id s.its_ts.ts_args in
            cl.ts_table <- Mts.add s.its_ts s cl.ts_table
          end else Opt.iter (visit alg s) (Mits.find_opt s def);
          List.iter down tl
      | Ityvar _ -> () in
    down ity;
    clone_ity cl ity in

  Mits.iter (visit Sits.empty) def;
  Lists.map_filter (fun d -> Hits.find htd d.itd_its) tdl

type smap = {
  sm_vs : vsymbol Mvs.t;
  sm_pv : pvsymbol Mvs.t;
  sm_rs : rsymbol Mrs.t;
}

let sm_of_cl cl = {
  sm_vs = Mvs.map (fun v -> v.pv_vs) cl.pv_table;
  sm_pv = cl.pv_table;
  sm_rs = cl.rs_table }

let sm_save_vs sm v v' = {
  sm_vs = Mvs.add v v'.pv_vs sm.sm_vs;
  sm_pv = Mvs.add v v' sm.sm_pv;
  sm_rs = sm.sm_rs }

let sm_save_pv sm v v' = {
  sm_vs = Mvs.add v.pv_vs v'.pv_vs sm.sm_vs;
  sm_pv = Mvs.add v.pv_vs v' sm.sm_pv;
  sm_rs = sm.sm_rs }

let sm_save_rs cl sm s s' =
  let sm = { sm with sm_rs = Mrs.add s s' sm.sm_rs } in
  match s.rs_logic, s'.rs_logic with
  | RLls s, RLls s' -> cl_save_ls cl s s'; sm
  | RLpv v, RLpv v' -> sm_save_pv sm v v'
  | _ -> sm

let sm_find_pv sm v = Mvs.find_def v v.pv_vs sm.sm_pv
  (* non-instantiated global variables are not in sm *)

let clone_pv cl {pv_vs = vs; pv_ity = ity; pv_ghost = ghost} =
  create_pvsymbol (id_clone vs.vs_name) ~ghost (clone_ity cl ity)

let clone_invl cl sm invl =
  List.map (fun t -> clone_term cl sm.sm_vs t) invl

let clone_varl cl sm varl = List.map (fun (t,r) ->
  clone_term cl sm.sm_vs t, Opt.map (cl_find_ls cl) r) varl

let clone_cty cl sm cty =
  let args = List.map (clone_pv cl) cty.cty_args in
  let sm_args = List.fold_left2 sm_save_pv sm cty.cty_args args in
  let add_old o n (sm, olds) = let o' = clone_pv cl o in
    sm_save_pv sm o o', Mpv.add o' (sm_find_pv sm_args n) olds in
  let sm_olds, olds = Mpv.fold add_old cty.cty_oldies (sm_args, Mpv.empty) in
  let pre = clone_invl cl sm_args cty.cty_pre in
  let post = clone_invl cl sm_olds cty.cty_post in
  let xpost = Mexn.fold (fun xs fl q ->
    let xs = cl_find_xs cl xs in
    let fl = clone_invl cl sm_olds fl in
    Mexn.add xs fl q) cty.cty_xpost Mexn.empty in
  let add_read v s = Spv.add (sm_find_pv sm_args v) s in
  let reads = Spv.fold add_read cty.cty_effect.eff_reads Spv.empty in
  let reads = Spv.union reads (Mpv.map ignore olds) in
  let add_write reg fs m =
    let add_fd fd s = Spv.add (Mpv.find_def fd fd cl.fd_table) s in
    Mreg.add (clone_reg cl reg) (Spv.fold add_fd fs Spv.empty) m in
  let writes = Mreg.fold add_write cty.cty_effect.eff_writes Mreg.empty in
  let add_reset reg s = Sreg.add (clone_reg cl reg) s in
  let resets = Sreg.fold add_reset cty.cty_effect.eff_resets Sreg.empty in
  let eff = eff_reset (eff_write reads writes) resets in
  let eff = eff_ghostify cty.cty_effect.eff_ghost eff in
  let add_raise xs eff = eff_raise eff (cl_find_xs cl xs) in
  let eff = Sexn.fold add_raise cty.cty_effect.eff_raises eff in
  let eff = if cty.cty_effect.eff_oneway then eff_diverge eff else eff in
  create_cty args pre post xpost olds eff (clone_ity cl cty.cty_result)

let sm_save_args sm c c' =
  List.fold_left2 sm_save_pv sm c.cty_args c'.cty_args

let sm_save_olds sm c c' =
  let revs = Mpv.fold (fun o n m -> Mpv.add n o m) c'.cty_oldies Mpv.empty in
  let add_old o n sm = sm_save_pv sm o (Mpv.find (sm_find_pv sm n) revs) in
  Mpv.fold add_old c.cty_oldies sm

let rs_kind s = match s.rs_logic with
  | RLnone -> RKnone
  | RLpv _ -> RKlocal
  | RLls { ls_value = None } -> RKpred
  | RLls _ -> RKfunc
  | RLlemma -> RKlemma

let clone_ppat cl sm ~ghost pp =
  let rec conv_pat p = match p.pat_node with
    | Term.Pwild -> PPwild
    | Term.Pvar v -> PPvar (id_clone v.vs_name)
    | Term.Por (p1,p2) -> PPor (conv_pat p1, conv_pat p2)
    | Term.Pas (p,v) -> PPas (conv_pat p, id_clone v.vs_name)
    | Term.Papp (s,pl) ->
        PPapp (restore_rs (cl_find_ls cl s), List.map conv_pat pl) in
  let pre = conv_pat pp.pp_pat in
  (* FIXME: if we clone pp using its own ghost status pp.pp_ghost,
     we may ghostify too many variables. This may happen if we have
     a match over a non-ghost expression with a single branch with
     a ghostifying pattern (= some ghost subvalue is deep-matched).
     Since there is only one branch, this match will be non-ghost,
     and all non-ghost variables in the pattern must stay so, too.

     To avoid the problem, we pass to create_prog_pattern the ghost
     status of the matched expression. This, however, may also break,
     if someone created a match over a non-ghost expression with a
     single branch with an artificially ghostified pattern (that is,
     by calling create_prog_pattern ~ghost:true). In this case, we
     may not ghostify some variables which were ghost in the original
     pattern, and perform unnecessary computations in the cloned code.
     This exploit is only possible via API, since Dexpr always passes
     to create_prog_pattern the ghost status of the matched expr. *)
  let vm, pp' = create_prog_pattern pre ~ghost pp.pp_ity in
  let save v sm = sm_save_vs sm v (Mstr.find v.vs_name.id_string vm) in
  Svs.fold save pp.pp_pat.pat_vars sm, pp'

let rec clone_expr cl sm e = e_label_copy e (e_ghostify (e_ghost e)
  (match e.e_node with
  | Evar v -> e_var (sm_find_pv sm v)
  | Econst c -> e_const c
  | Eexec c -> e_exec (clone_cexp cl sm c)
  | Eassign asl ->
      let conv (r,f,v) =
        e_var (sm_find_pv sm r), cl_find_rs cl f, e_var (sm_find_pv sm v) in
      e_assign (List.map conv asl)
  | Elet (ld, e) ->
      let sm, ld = clone_let_defn cl sm ld in
      e_let ld (clone_expr cl sm e)
  | Eif (e1, e2, e3) ->
      e_if (clone_expr cl sm e1) (clone_expr cl sm e2) (clone_expr cl sm e3)
  | Ecase (d, bl) ->
      let ghost = e_ghost d in
      let conv_br (pp, e) =
        let sm, pp = clone_ppat cl sm ~ghost pp in
        pp, clone_expr cl sm e in
      e_case (clone_expr cl sm d) (List.map conv_br bl)
  | Ewhile (c,invl,varl,e) ->
      e_while (clone_expr cl sm c) (clone_invl cl sm invl)
              (clone_varl cl sm varl) (clone_expr cl sm e)
  | Efor (i, (f,dir,t), invl, e) ->
      let i' = clone_pv cl i in
      let ism = sm_save_pv sm i i' in
      e_for i'
        (e_var (sm_find_pv sm f)) dir (e_var (sm_find_pv sm t))
        (clone_invl cl ism invl) (clone_expr cl ism e)
  | Etry (d, xl) ->
      let conv_br (xs, v, e) =
        let v' = clone_pv cl v in
        cl_find_xs cl xs, v', clone_expr cl (sm_save_pv sm v v') e in
      e_try (clone_expr cl sm d) (List.map conv_br xl)
  | Eraise (xs, e) ->
      e_raise (cl_find_xs cl xs) (clone_expr cl sm e) (clone_ity cl e.e_ity)
  | Eassert (k, f) ->
      e_assert k (clone_term cl sm.sm_vs f)
  | Epure t ->
      e_pure (clone_term cl sm.sm_vs t)
  | Eabsurd -> e_absurd (clone_ity cl e.e_ity)))

and clone_cexp cl sm c = c_ghostify (cty_ghost c.c_cty) (match c.c_node with
  | Capp (s,vl) ->
      let vl = List.map (fun v -> sm_find_pv sm v) vl in
      let al = List.map (fun v -> clone_ity cl v.pv_ity) c.c_cty.cty_args in
      let res = clone_ity cl c.c_cty.cty_result in
      c_app (Mrs.find_def s s sm.sm_rs) vl al res
  | Cpur (s,vl) ->
      let vl = List.map (fun v -> sm_find_pv sm v) vl in
      let al = List.map (fun v -> clone_ity cl v.pv_ity) c.c_cty.cty_args in
      let res = clone_ity cl c.c_cty.cty_result in
      c_pur (cl_find_ls cl s) vl al res
  | Cfun e ->
      let cty = clone_cty cl sm c.c_cty in
      let sm = sm_save_args sm c.c_cty cty in
      let sm = sm_save_olds sm c.c_cty cty in
      c_fun cty.cty_args cty.cty_pre cty.cty_post
        cty.cty_xpost cty.cty_oldies (clone_expr cl sm e)
  | Cany ->
      c_any (clone_cty cl sm c.c_cty))

and clone_let_defn cl sm ld = match ld with
  | LDvar (v,e) ->
      let e' = clone_expr cl sm e in
      let ld, v' = let_var (id_clone v.pv_vs.vs_name) ~ghost:v.pv_ghost e' in
      sm_save_pv sm v v', ld
  | LDsym (s,c) ->
      let c' = clone_cexp cl sm c in
      let ld, s' = let_sym (id_clone s.rs_name)
        ~ghost:(rs_ghost s) ~kind:(rs_kind s) c' in
      sm_save_rs cl sm s s', ld
  | LDrec rdl ->
      let conv_rs mrs {rec_rsym = rs} =
        let rs' = create_rsymbol (id_clone rs.rs_name)
          ~ghost:(rs_ghost rs) (clone_cty cl sm rs.rs_cty) in
        Mrs.add rs rs' mrs, rs' in
      let mrs, rsyml = Lists.map_fold_left conv_rs sm.sm_rs rdl in
      let rsm = { sm with sm_rs = mrs } in
      let conv_rd ({rec_fun = c} as rd) ({rs_cty = cty} as rs) =
        let pre = if rd.rec_varl = [] then cty.cty_pre
          else List.tl cty.cty_pre (* remove DECR *) in
        let rsm = sm_save_args rsm c.c_cty cty in
        let varl = clone_varl cl rsm rd.rec_varl in
        let rsm = sm_save_olds rsm c.c_cty cty in
        let e = match c.c_node with
          | Cfun e -> clone_expr cl rsm e
          | _ -> assert false (* can't be *) in
        let c = c_fun cty.cty_args pre
          cty.cty_post cty.cty_xpost cty.cty_oldies e in
        rs, c, varl, rs_kind rd.rec_sym in
      let ld, rdl' = let_rec (List.map2 conv_rd rdl rsyml) in
      let sm = List.fold_left2 (fun sm d d' ->
        sm_save_rs cl sm d.rec_sym d'.rec_sym) sm rdl rdl' in
      sm, ld

let clone_pdecl inst cl uc d = match d.pd_node with
  | PDtype tdl ->
      let tdl = clone_type_decl inst cl tdl in
      if tdl = [] then uc else
      add_pdecl ~vc:false uc (create_type_decl tdl)
  | PDlet ld ->
      let reads = match ld with
        | LDvar (_,e) -> e.e_effect.eff_reads
        | LDsym (_,c) -> cty_reads c.c_cty
        | LDrec rdl -> List.fold_left (fun spv {rec_rsym = s} ->
            Spv.union spv (cty_reads s.rs_cty)) Spv.empty rdl in
      let frz = Spv.fold (fun v isb ->
        if Sid.mem v.pv_vs.vs_name cl.cl_local then isb
        else ity_freeze isb v.pv_ity) reads isb_empty in
      let frz = Mreg.map (fun ity -> match ity.ity_node with
        | Ityreg r -> r | _ -> assert false) frz.isb_reg in
      cl.rn_table <- Mreg.set_union cl.rn_table frz;
      let sm, ld = clone_let_defn cl (sm_of_cl cl) ld in
      cl.pv_table <- sm.sm_pv; cl.rs_table <- sm.sm_rs;
      add_pdecl ~vc:false uc (create_let_decl ld)
  | PDexn xs ->
      let ity = clone_ity cl xs.xs_ity in
      let xs' = create_xsymbol (id_clone xs.xs_name) ity in
      cl.xs_table <- Mexn.add xs xs' cl.xs_table;
      add_pdecl ~vc:false uc (create_exn_decl xs')
  | PDpure ->
      List.fold_left (clone_decl inst cl) uc d.pd_pure

let theory_add_clone = Theory.add_clone_internal ()

let add_clone uc mi =
  let sm = {
    sm_ty = Mts.map ty_of_ity mi.mi_ty;
    sm_ts = Mts.map (fun s -> s.its_ts) mi.mi_ts;
    sm_ls = mi.mi_ls;
    sm_pr = mi.mi_pr } in
  { uc with
      muc_theory = theory_add_clone uc.muc_theory mi.mi_mod.mod_theory sm;
      muc_units  = Uclone mi :: uc.muc_units }

let clone_export uc m inst =
  let cl = cl_init m inst in
  let rec add_unit uc u = match u with
    | Udecl d -> clone_pdecl inst cl uc d
    | Uuse m -> use_export uc m
    | Uclone mi ->
        begin try add_clone uc { mi_mod = mi.mi_mod;
          mi_ty = Mts.map (clone_ity cl) mi.mi_ty;
          mi_ts = Mts.map (cl_find_its cl) mi.mi_ts;
          mi_ls = Mls.map (cl_find_ls cl) mi.mi_ls;
          mi_pr = Mpr.map (cl_find_pr cl) mi.mi_pr;
          mi_pv = Mvs.map (cl_find_pv cl) mi.mi_pv;
          mi_rs = Mrs.map (cl_find_rs cl) mi.mi_rs;
          mi_xs = Mexn.map (cl_find_xs cl) mi.mi_xs}
        with Not_found -> uc end
    | Umeta (m,al) ->
        begin try add_meta uc m (List.map (function
          | MAty ty -> MAty (clone_ty cl ty)
          | MAts ts -> MAts (cl_find_ts cl ts)
          | MAls ls -> MAls (cl_find_ls cl ls)
          | MApr pr -> MApr (cl_find_pr cl pr)
          | a -> a) al)
        with Not_found -> uc end
    | Uscope (n,import,ul) ->
        let uc = open_scope uc n in
        let uc = List.fold_left add_unit uc ul in
        close_scope ~import uc in
  let uc = List.fold_left add_unit uc m.mod_units in
  let mi = {
    mi_mod = m;
    mi_ty  = cl.ty_table;
    mi_ts  = cl.ts_table;
    mi_ls  = cl.ls_table;
    mi_pr  = cl.pr_table;
    mi_pv  = cl.pv_table;
    mi_rs  = cl.rs_table;
    mi_xs  = cl.xs_table} in
  add_clone uc mi

(** {2 WhyML language} *)

type mlw_file = pmodule Mstr.t

let convert mm =
  let convert m = m.mod_theory in
  if Mstr.is_empty mm then Mstr.empty else
  match (snd (Mstr.choose mm)).mod_theory.th_path with
  | "why3" :: path ->
      begin try Env.base_language_builtin path
      with Not_found -> Mstr.map convert mm end
  | _ -> Mstr.map convert mm

let mlw_language = Env.register_language Env.base_language convert

module Hpath = Exthtbl.Make(struct
  type t = Env.pathname
  let hash = Hashtbl.hash
  let equal = (=)
end)

let mlw_language_builtin =
  let builtin s =
    if s = unit_module.mod_theory.th_name.id_string then unit_module else
    if s = builtin_theory.th_name.id_string then builtin_module else
    if s = highord_theory.th_name.id_string then highord_module else
    if s = bool_theory.th_name.id_string then bool_module else
    match tuple_theory_name s with
    | Some n -> tuple_module n
    | None -> raise Not_found in
  Hpath.memo 7 (function
    | [s] -> Mstr.singleton s (builtin s)
    | _   -> raise Not_found)

let () = Env.add_builtin mlw_language mlw_language_builtin

exception ModuleNotFound of Env.pathname * string

let read_module env path s =
  let path = if path = [] then ["why3"; s] else path in
  let mm = Env.read_library mlw_language env path in
  Mstr.find_exn (ModuleNotFound (path,s)) s mm

(* pretty-printing *)

let print_path fmt sl =
  Pp.print_list (Pp.constant_string ".") Format.pp_print_string fmt sl

let print_mname fmt {mod_theory = th} =
  List.iter (fun s ->
    Format.pp_print_string fmt s;
    Format.pp_print_char fmt '.') th.th_path;
  Format.pp_print_string fmt th.th_name.id_string

let rec print_unit fmt = function
  | Udecl d -> Pdecl.print_pdecl fmt d
  | Uuse m -> Format.fprintf fmt "use export %a" print_mname m
  | Uclone mi -> Format.fprintf fmt "clone export %a with ..."
      print_mname mi.mi_mod
  | Umeta (m,al) -> Format.fprintf fmt "@[<hov 2>meta %s %a@]"
      m.meta_name (Pp.print_list Pp.comma Pretty.print_meta_arg) al
  | Uscope (s,i,[Uuse m]) -> Format.fprintf fmt "use%s %a%s"
      (if i then " import" else "") print_mname m
      (if s = m.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,i,[Uclone mi]) -> Format.fprintf fmt "clone%s %a%s with ..."
      (if i then " import" else "") print_mname mi.mi_mod
      (if s = mi.mi_mod.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,i,ul) -> Format.fprintf fmt "@[<hov 2>scope%s %s@\n%a@]@\nend"
      (if i then " import" else "") s (Pp.print_list Pp.newline2 print_unit) ul

let print_module fmt m = Format.fprintf fmt
  "@[<hov 2>module %s@\n%a@]@\nend" m.mod_theory.th_name.id_string
  (Pp.print_list Pp.newline2 print_unit) m.mod_units

let () = Exn_printer.register (fun fmt e -> match e with
  | ModuleNotFound (sl,s) -> Format.fprintf fmt
      "Module %s not found in library %a" s print_path sl
  | _ -> raise e)
