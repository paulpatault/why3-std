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
open Ity
open Expr

(** Program types *)

type dity =
  | Dvar of dvar ref          (* destructible "fresh" type variable *)
  | Dutv of tvsymbol          (* undestructible "user" type variable *)
  | Durg of dity * region     (* undestructible "user" region *)
  | Dapp of itysymbol * dity list * dity list

and dvar =
  | Dval of dity              (* i am equal to dity *)
  | Dpur of dity              (* i am equal to the purified dity *)
  | Dsim of dity * tvsymbol   (* our purified types are equal *)
  | Dreg of dity * tvsymbol   (* unassigned region *)
  | Dtvs of        tvsymbol   (* unassigned variable *)

(* In Dreg and Durg, the dity field is a Dapp of the region's type. *)

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

let dity_of_dvty (argl,res) =
  List.fold_right (fun a d -> Dapp (its_func, [a;d], [])) argl res

let dity_fresh () =
  Dvar (ref (Dtvs (create_tvsymbol (id_fresh "mu"))))

let dity_reg d =
  Dvar (ref (Dreg (d, create_tvsymbol (id_fresh "rho"))))

let rec dity_sim = function
  | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) -> dity_sim d
  | d -> Dvar (ref (Dsim (d, create_tvsymbol (id_fresh "eta"))))

let rec dity_pur = function
  | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) -> dity_pur d
  | d -> Dvar (ref (Dpur d))

let app_map fn s tl rl = Dapp (s, List.map fn tl, List.map fn rl)

let dity_of_ity ity =
  let hr = Hreg.create 3 in
  let rec dity ity = match ity.ity_node with
    | Ityvar (v,false) -> Dutv v
    | Ityvar (v,true)  -> dity_pur (Dutv v)
    | Ityapp (s,tl,rl) -> app_map dity s tl rl
    | Ityreg ({reg_its = s; reg_args = tl; reg_regs = rl} as r) ->
        try Hreg.find hr r with Not_found ->
        let d = dity_reg (app_map dity s tl rl) in
        Hreg.add hr r d; d in
  dity ity

let rec ity_of_dity = function
  | Dutv v -> ity_var v
  | Durg (_,r) -> ity_reg r
  | Dvar {contents = Dval d} -> ity_of_dity d
  | Dvar {contents = Dpur d} -> ity_purify (ity_of_dity d)
  | Dvar ({contents = Dsim (d,_)} as r) ->
      let rec refresh ity = match ity.ity_node with
        | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
            ity_app s (List.map refresh tl) []
        | Ityvar (v,_) -> ity_var v in
      let rec dity ity = match ity.ity_node with
        | Ityreg r ->
            Durg (app_map dity r.reg_its r.reg_args r.reg_regs, r)
        | Ityapp (s,tl,rl) -> app_map dity s tl rl
        | Ityvar (v,true)  -> dity_pur (Dutv v)
        | Ityvar (v,false) -> Dutv v in
      let t = refresh (ity_of_dity d) in
      r := Dval (dity t); t
  | Dvar ({contents = Dreg (Dapp (s,tl,rl) as d,_)} as r) ->
      let reg = create_region (id_fresh "rho") s
        (List.map ity_of_dity tl) (List.map ity_of_dity rl) in
      r := Dval (Durg (d, reg)); ity_reg reg
  | Dvar r ->
      let v = create_tvsymbol (id_fresh "xi") in
      r := Dval (Dutv v); ity_var v
  | Dapp (s,tl,rl) ->
      ity_app_pure s (List.map ity_of_dity tl) (List.map ity_of_dity rl)

(** Destructive type unification *)

let rec occur_check v = function
  | Dvar {contents = (Dval d|Dpur d)} | Durg (d,_) ->
      occur_check v d
  | Dvar {contents = (Dsim (d,u)|Dreg (d,u))} ->
      if tv_equal u v then raise Exit else occur_check v d
  | Dvar {contents = Dtvs u} | Dutv u ->
      if tv_equal u v then raise Exit
  | Dapp (_,dl,_) ->
      List.iter (occur_check v) dl

let rec dity_unify_weak d1 d2 = match d1,d2 with
  | Dvar {contents = (Dval d1|Dpur d1|Dsim (d1,_)|Dreg (d1,_))}, d2
  | d1, Dvar {contents = (Dval d2|Dpur d2|Dsim (d2,_)|Dreg (d2,_))}
  | Durg (d1,_), d2 | d1, Durg (d2,_) ->
      dity_unify_weak d1 d2
  | Dvar {contents = Dtvs u},
    Dvar {contents = Dtvs v} when tv_equal u v ->
      ()
  | Dvar ({contents = Dtvs v} as r), d
  | d, Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      r := Dsim (d,v)
  | Dutv u, Dutv v when tv_equal u v ->
      ()
  | Dapp (s1,dl1,_), Dapp (s2,dl2,_) when its_equal s1 s2 ->
      List.iter2 dity_unify_weak dl1 dl2
  | _ -> raise Exit

let rec dity_refresh = function
  | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) -> dity_refresh d
  | Dutv _ as d -> d
  | Dvar {contents = Dtvs _} -> dity_fresh ()
  | Dapp (s,dl,_) ->
      let dl = List.map dity_refresh dl in
      let mv = List.fold_right2 Mtv.add s.its_ts.ts_args dl Mtv.empty in
      let hr = Hreg.create 3 in
      let rec ity_inst ity = match ity.ity_node with
        | Ityreg r -> reg_inst r
        | Ityvar (v, false) -> Mtv.find v mv
        | Ityvar (v, true) -> dity_pur (Mtv.find v mv)
        | Ityapp (s,tl,rl) -> app_map ity_inst s tl rl
      and reg_inst ({reg_its = s; reg_args = tl; reg_regs = rl} as r) =
        try Hreg.find hr r with Not_found ->
        let d = dity_reg (app_map ity_inst s tl rl) in
        Hreg.replace hr r d; d in
      let d = Dapp (s, dl, List.map reg_inst s.its_regions) in
      if its_immutable s then d else dity_reg d

let rec dity_unify_asym d1 d2 = match d1,d2 with
  | Durg _, _ | Dutv _, _ -> raise Exit (* we cannot be pure then *)
  | d1, Dvar {contents = (Dval d2|Dpur d2|Dsim (d2,_)|Dreg (d2,_))}
  | d1, Durg (d2,_)
  | Dvar {contents = Dval d1}, d2 ->
      dity_unify_asym d1 d2
  | Dvar {contents = Dpur d1}, d2 ->
      dity_unify_weak d1 d2
  | Dvar ({contents = Dsim (d1,_)} as r), d2 ->
      dity_unify_weak d1 d2;
      r := Dpur d1
  | Dvar ({contents = Dreg (d1,_)} as r), d2 ->
      dity_unify_asym d1 d2;
      r := Dval d1
  | Dvar ({contents = Dtvs u} as r),
    Dvar {contents = Dtvs v} when tv_equal u v ->
      r := Dpur (dity_fresh ())
  | Dvar ({contents = Dtvs v} as r), d ->
      occur_check v d;
      r := Dpur d
  | d (* not a Dvar! *), Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      let d2 = dity_refresh d in
      dity_unify_asym d d2;
      r := Dval d2
  | Dapp (s1,dl1,rl1), Dapp (s2,dl2,rl2) when its_equal s1 s2 ->
      List.iter2 dity_unify_asym dl1 dl2;
      List.iter2 dity_unify_asym rl1 rl2
  | _ -> raise Exit

let rec dity_unify d1 d2 = match d1,d2 with
  | Dvar {contents = Dval d1}, d2 | d1, Dvar {contents = Dval d2} ->
      dity_unify d1 d2
  | Dvar ({contents = Dpur d2}), d1 (* yes, it's d2 on the left *)
  | d1, Dvar ({contents = Dpur d2}) ->
      dity_unify_asym d1 d2
  | Dvar ({contents = Dsim (_,u)}),
    Dvar ({contents = Dsim (_,v)}) when tv_equal u v ->
      ()
  | Dvar ({contents = Dsim (d1,v)} as r), d
  | d, Dvar ({contents = Dsim (d1,v)} as r) ->
      occur_check v d; (* not necessary? *)
      dity_unify_weak d1 d;
      r := Dval d
  | Dvar {contents = Dreg (_,u)},
    Dvar {contents = Dreg (_,v)} when tv_equal u v ->
      ()
  | Dvar ({contents = Dreg (d1,v)} as r),
    ((Dapp _ as d2 | Durg (d2,_) | Dvar {contents = Dreg (d2,_)}) as d)
  | ((Dapp _ as d1 | Durg (d1,_)) as d),
    Dvar ({contents = Dreg (d2,v)} as r) ->
      occur_check v d; (* not necessary! *)
      dity_unify d1 d2;
      r := Dval d
  | Dvar ({contents = Dtvs u}),
    Dvar ({contents = Dtvs v}) when tv_equal u v ->
      ()
  | Dvar ({contents = Dtvs v} as r), d
  | d, Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      r := Dval d
  | Dutv u, Dutv v when tv_equal u v ->
      ()
  | Durg (_,r1), Durg (_,r2) when reg_equal r1 r2 ->
      ()
  | Dapp (s1,dl1,rl1), Dapp (s2,dl2,rl2) when its_equal s1 s2 ->
      List.iter2 dity_unify dl1 dl2;
      List.iter2 dity_unify rl1 rl2
  | _ -> raise Exit

(** Built-in types *)

let dity_int  = Dapp (its_int,  [], [])
let dity_real = Dapp (its_real, [], [])
let dity_bool = Dapp (its_bool, [], [])
let dity_unit = Dapp (its_unit, [], [])

let dvty_int  = [], dity_int
let dvty_real = [], dity_real
let dvty_bool = [], dity_bool
let dvty_unit = [], dity_unit

(** Pretty-printing *)

let rprinter =
  let sanitizer = Ident.sanitizer Ident.char_to_lalpha Ident.char_to_alnumus in
  Ident.create_ident_printer [] ~sanitizer

let print_args pr fmt tl = if tl <> [] then
  Format.fprintf fmt "@ %a" (Pp.print_list Pp.space pr) tl

let print_regs pr fmt rl = if rl <> [] then
  Format.fprintf fmt "@ <%a>" (Pp.print_list Pp.comma pr) rl

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_dity pur pri fmt = function
  | Dvar {contents = Dval d} ->
      print_dity pur pri fmt d
  | Dvar {contents = (Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) when pur ->
      print_dity pur pri fmt d
  | Dvar {contents = Dtvs v} | Dutv v ->
      Pretty.print_tv fmt v
  | Dvar {contents = Dpur d} ->
      Format.fprintf fmt "{%a}" (print_dity true 0) d
  | Dvar {contents = Dsim (d,_)} ->
      Format.fprintf fmt "[%a]" (print_dity true 0) d
  | Dvar {contents = Dreg (Dapp (s,tl,rl),{tv_name = id})}
  | Durg (Dapp (s,tl,rl),{reg_name = id}) ->
      Format.fprintf fmt
        (protect_on (pri > 1 && (tl <> [] || rl <> [])) "%a%a%a@ @@%s")
        Pretty.print_ts s.its_ts (print_args (print_dity pur 2)) tl
          (print_regs (print_dity pur 0)) rl (Ident.id_unique rprinter id)
  | Dvar {contents = Dreg _} | Durg _ -> assert false
  | Dapp (s,[t1;t2],[]) when its_equal s its_func ->
      Format.fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_dity pur 1) t1 (print_dity pur 0) t2
  | Dapp (s,tl,[]) when is_ts_tuple s.its_ts ->
      Format.fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_dity pur 0)) tl
  | Dapp (s,tl,_) when pur ->
      Format.fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        Pretty.print_ts s.its_ts (print_args (print_dity pur 2)) tl
  | Dapp (s,tl,rl) when its_immutable s ->
      Format.fprintf fmt
        (protect_on (pri > 1 && (tl <> [] || rl <> [])) "%a%a%a")
        Pretty.print_ts s.its_ts (print_args (print_dity pur 2)) tl
          (print_regs (print_dity pur 0)) rl
  | Dapp (s,tl,rl) ->
      Format.fprintf fmt
        (protect_on (pri > 1 && (tl <> [] || rl <> [])) "{%a}%a%a")
        Pretty.print_ts s.its_ts (print_args (print_dity pur 2)) tl
          (print_regs (print_dity pur 0)) rl

let print_dity fmt d = print_dity false 0 fmt d

(* Specialization of symbols *)

let specialize_scheme tvs (argl,res) =
  let hv = Htv.create 3 in
  let rec spec_dity = function
    | Dvar {contents = Dval d} -> spec_dity d
    | Dvar {contents = Dpur d} -> dity_pur (spec_dity d)
    | Dvar {contents = Dsim (d,v)} ->
        (try Htv.find hv v with Not_found ->
        let nd = dity_sim (spec_dity d) in
        Htv.add hv v nd; nd)
    | Dvar {contents = Dreg (d,v)} ->
        (try Htv.find hv v with Not_found ->
        let nd = dity_reg (spec_dity d) in
        Htv.add hv v nd; nd)
    | Dvar {contents = Dtvs v} | Dutv v as d ->
        (try Htv.find hv v with Not_found ->
        (* even if v is frozen, it is polymorphic in its regions *)
        let nd = if Stv.mem v tvs then dity_fresh () else dity_sim d in
        Htv.add hv v nd; nd)
    | Dapp (s,dl,rl) -> app_map spec_dity s dl rl
    | Durg _ as d -> d in
  List.map spec_dity argl, spec_dity res

let spec_ity hv hr frz ity =
  let rec dity ity = match ity.ity_node with
    | Ityreg r ->
        (try Hreg.find hr r with Not_found ->
        let d = app_map dity r.reg_its r.reg_args r.reg_regs in
        let nd = if Mreg.mem r frz.isb_reg then Durg (d,r) else dity_reg d in
        Hreg.add hr r nd; nd)
    | Ityvar (v,pure) ->
        let nd = try Htv.find hv v with Not_found ->
          let nd =
            if Mtv.mem v frz.isb_var then Dutv v else
            if Mtv.mem v frz.isb_pur then dity_sim (Dutv v) else
            dity_fresh () in
          Htv.add hv v nd; nd in
        if pure then dity_pur nd else nd
    | Ityapp (s,tl,rl) -> app_map dity s tl rl in
  dity ity

let specialize_pv {pv_ity = ity} =
  spec_ity (Htv.create 3) (Hreg.create 3) (ity_freeze isb_empty ity) ity

let specialize_xs {xs_ity = ity} =
  spec_ity (Htv.create 3) (Hreg.create 3) (ity_freeze isb_empty ity) ity

let specialize_rs {rs_cty = cty} =
  let hv = Htv.create 3 and hr = Hreg.create 3 in
  let spec ity = spec_ity hv hr cty.cty_freeze ity in
  List.map (fun v -> spec v.pv_ity) cty.cty_args, spec cty.cty_result

let specialize_ls {ls_args = args; ls_value = res} =
  let hv = Htv.create 3 and hr = Hreg.create 3 in
  let spec_val _ ty = spec_ity hv hr isb_empty (ity_of_ty_pure ty) in
  let spec_arg ty = dity_sim (spec_val () ty) in
  List.map spec_arg args, Opt.fold spec_val dity_bool res

(** Patterns *)

type dpattern = {
  dp_pat  : pre_pattern;
  dp_dity : dity;
  dp_vars : dity Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid * bool
  | DPapp  of rsymbol * dpattern list
  | DPas   of dpattern * preid * bool
  | DPor   of dpattern * dpattern
  | DPcast of dpattern * ity

(** Specifications *)

type ghost = bool

type dbinder = preid option * ghost * dity

type register_old = pvsymbol -> string -> pvsymbol

type 'a later = pvsymbol Mstr.t -> register_old -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec_final = {
  ds_pre     : term list;
  ds_post    : (pvsymbol * term) list;
  ds_xpost   : (pvsymbol * term) list Mexn.t;
  ds_reads   : pvsymbol list;
  ds_writes  : term list;
  ds_diverge : bool;
  ds_checkrw : bool;
}

type dspec = ity -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

(** Expressions *)

type dinvariant = term list

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEpv of pvsymbol
  | DErs of rsymbol
  | DEls of lsymbol
  | DEconst of Number.constant
  | DEapp of dexpr * dexpr
  | DEfun of dbinder list * mask * dspec later * dexpr
  | DEany of dbinder list * mask * dspec later * dity
  | DElet of dlet_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEnot of dexpr
  | DEand of dexpr * dexpr
  | DEor of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEcase of dexpr * (dpattern * dexpr) list
  | DEassign of (dexpr * rsymbol * dexpr) list
  | DEwhile of dexpr * dinvariant later * variant list later * dexpr
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEraise of xsymbol * dexpr
  | DEghost of dexpr
  | DEassert of assertion_kind * term later
  | DEpure of term later
  | DEabsurd
  | DEtrue
  | DEfalse
  | DEmark of preid * dexpr
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dlet_defn = preid * ghost * rs_kind * dexpr

and drec_defn = { fds : dfun_defn list }

and dfun_defn = preid * ghost * rs_kind *
  dbinder list * mask * dspec later * variant list later * dexpr

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (Stv.t option * dvty) Mstr.t;
}

let denv_empty = { frozen = []; locals = Mstr.empty }

let is_frozen frozen v =
  try List.iter (occur_check v) frozen; false with Exit -> true

let freeze_dvty frozen (argl,res) =
  let rec add l = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> add l d
    | Dvar {contents = Dtvs _}
    | Dutv _ as d -> d :: l
    | Dapp (_,tl,_) -> List.fold_left add l tl in
  List.fold_left add (add frozen res) argl

let free_vars frozen (argl,res) =
  let rec add s = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> add s d
    | Dvar {contents = Dtvs v} | Dutv v ->
        if is_frozen frozen v then s else Stv.add v s
    | Dapp (_,tl,_) -> List.fold_left add s tl in
  List.fold_left add (add Stv.empty res) argl

let denv_add_mono { frozen = frozen; locals = locals } id dvty =
  let locals = Mstr.add id.pre_name (None, dvty) locals in
  { frozen = freeze_dvty frozen dvty; locals = locals }

let denv_add_poly { frozen = frozen; locals = locals } id dvty =
  let ftvs = free_vars frozen dvty in
  let locals = Mstr.add id.pre_name (Some ftvs, dvty) locals in
  { frozen = frozen; locals = locals }

let denv_add_rec_mono { frozen = frozen; locals = locals } id dvty =
  let locals = Mstr.add id.pre_name (Some Stv.empty, dvty) locals in
  { frozen = freeze_dvty frozen dvty; locals = locals }

let denv_add_rec_poly { frozen = frozen; locals = locals } frozen0 id dvty =
  let ftvs = free_vars frozen0 dvty in
  let locals = Mstr.add id.pre_name (Some ftvs, dvty) locals in
  { frozen = frozen; locals = locals }

let denv_add_rec denv frozen0 id ((argl,res) as dvty) =
  let rec is_explicit = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> is_explicit d
    | Dvar {contents = Dtvs _} -> false
    | Dutv _ -> true
    | Dapp (_,tl,_) -> List.for_all is_explicit tl in
  if List.for_all is_explicit argl && is_explicit res
  then denv_add_rec_poly denv frozen0 id dvty
  else denv_add_rec_mono denv id dvty

let denv_add_var denv id dity = denv_add_mono denv id ([], dity)

let denv_add_let denv (id,_,_,({de_dvty = dvty} as de)) =
  if fst dvty = [] then denv_add_mono denv id dvty else
  let rec is_value de = match de.de_node with
    | DEghost de | DEuloc (de,_) | DElabel (de,_) -> is_value de
    | DEvar _ | DErs _ | DEls _ | DEfun _ | DEany _ -> true
    | _ -> false in
  if is_value de
  then denv_add_poly denv id dvty
  else denv_add_mono denv id dvty

let denv_add_args { frozen = frozen; locals = locals } bl =
  let l = List.fold_left (fun l (_,_,t) -> t::l) frozen bl in
  let add s (id,_,t) = match id with
    | Some {pre_name = n} ->
        Mstr.add_new (Dterm.DuplicateVar n) n (None, ([],t)) s
    | None -> s in
  let s = List.fold_left add Mstr.empty bl in
  { frozen = l; locals = Mstr.set_union s locals }

let denv_add_pat { frozen = frozen; locals = locals } dp =
  let l = Mstr.fold (fun _ t l -> t::l) dp.dp_vars frozen in
  let s = Mstr.map (fun t -> None, ([], t)) dp.dp_vars in
  { frozen = l; locals = Mstr.set_union s locals }

let mk_node n = function
  | Some tvs, dvty -> DEvar (n, specialize_scheme tvs dvty)
  | None,     dvty -> DEvar (n, dvty)

let denv_get denv n =
  mk_node n (Mstr.find_exn (Dterm.UnboundVar n) n denv.locals)

let denv_get_opt denv n =
  Opt.map (mk_node n) (Mstr.find_opt n denv.locals)

(** Unification tools *)

let dity_unify_app ls fn (l1: 'a list) (l2: dity list) =
  try List.iter2 fn l1 l2 with Invalid_argument _ ->
    raise (BadArity (ls, List.length l1))

let dpat_expected_type {dp_dity = dp_dity; dp_loc = loc} dity =
  try dity_unify dp_dity dity with Exit -> Loc.errorm ?loc
    "This pattern has type %a,@ but is expected to have type %a"
    print_dity dp_dity print_dity dity

let dexpr_expected_type {de_dvty = dvty; de_loc = loc} dity =
  let res = dity_of_dvty dvty in
  try dity_unify res dity with Exit -> Loc.errorm ?loc
    "This expression has type %a,@ but is expected to have type %a"
    print_dity res print_dity dity

let dexpr_expected_type_weak {de_dvty = dvty; de_loc = loc} dity =
  let res = dity_of_dvty dvty in
  try dity_unify_weak res dity with Exit -> Loc.errorm ?loc
    "This expression has type %a,@ but is expected to have type %a"
    print_dity res print_dity dity

(** Generation of letrec blocks *)

type pre_fun_defn = preid * ghost * rs_kind * dbinder list *
  dity * mask * (denv -> dspec later * variant list later * dexpr)

exception DupId of preid

let drec_defn denv0 prel =
  if prel = [] then invalid_arg "Dexpr.drec_defn: empty function list";
  let add s (id,_,_,_,_,_,_) = Sstr.add_new (DupId id) id.pre_name s in
  let _ = try List.fold_left add Sstr.empty prel with DupId id ->
    Loc.errorm ?loc:id.pre_loc "duplicate function name %s" id.pre_name in
  let add denv (id,_,_,bl,res,_,_) =
    if bl = [] then invalid_arg "Dexpr.drec_defn: empty argument list";
    let argl = List.map (fun (_,_,t) -> t) bl in
    denv_add_rec denv denv0.frozen id (argl,res) in
  let denv1 = List.fold_left add denv0 prel in
  let parse (id,gh,pk,bl,res,msk,pre) =
    let dsp, dvl, de = pre (denv_add_args denv1 bl) in
    dexpr_expected_type de res;
    (id,gh,pk,bl,msk,dsp,dvl,de) in
  let fdl = List.map parse prel in
  let add denv (id,_,_,bl,_,_,_,{de_dvty = dvty}) =
    (* just in case we linked some polymorphic type var to the outer context *)
    let check tv = if is_frozen denv0.frozen tv then Loc.errorm ?loc:id.pre_loc
      "This function is expected to be polymorphic in type variable %a"
      Pretty.print_tv tv in
    begin match Mstr.find_opt id.pre_name denv1.locals with
    | Some (Some tvs, _) -> Stv.iter check tvs
    | Some (None, _) | None -> assert false
    end;
    let argl = List.map (fun (_,_,t) -> t) bl in
    denv_add_poly denv id (argl, dity_of_dvty dvty) in
  List.fold_left add denv0 fdl, { fds = fdl }

(** Constructors *)

let dpattern ?loc node =
  let mk_dpat pre dity vars =
    { dp_pat = pre; dp_dity = dity; dp_vars = vars; dp_loc = loc } in
  let dpat = function
    | DPwild ->
        mk_dpat PPwild (dity_fresh ()) Mstr.empty
    | DPvar (id,gh) ->
        let dity = dity_fresh () in
        mk_dpat (PPvar (id,gh)) dity (Mstr.singleton id.pre_name dity)
    | DPapp ({rs_logic = RLls ls} as rs, dpl) when ls.ls_constr > 0 ->
        let argl, res = specialize_rs rs in
        dity_unify_app ls dpat_expected_type dpl argl;
        let join n _ _ = raise (Dterm.DuplicateVar n) in
        let add acc dp = Mstr.union join acc dp.dp_vars in
        let vars = List.fold_left add Mstr.empty dpl in
        let ppl = List.map (fun dp -> dp.dp_pat) dpl in
        mk_dpat (PPapp (rs, ppl)) res vars
    | DPapp (rs,_) ->
        raise (ConstructorExpected rs);
    | DPor (dp1,dp2) ->
        dpat_expected_type dp2 dp1.dp_dity;
        let join n dity1 dity2 = try dity_unify dity1 dity2; Some dity1
          with Exit -> Loc.errorm ?loc
            "Variable %s has type %a,@ but is expected to have type %a"
            n print_dity dity1 print_dity dity2 in
        let vars = Mstr.union join dp1.dp_vars dp2.dp_vars in
        mk_dpat (PPor (dp1.dp_pat, dp2.dp_pat)) dp1.dp_dity vars
    | DPas (dp, ({pre_name = n} as id), gh) ->
        let { dp_pat = pat; dp_dity = dity; dp_vars = vars } = dp in
        let vars = Mstr.add_new (Dterm.DuplicateVar n) n dity vars in
        mk_dpat (PPas (pat, id, gh)) dity vars
    | DPcast (dp, ity) ->
        dpat_expected_type dp (dity_of_ity ity);
        dp
  in
  Loc.try1 ?loc dpat node

let dexpr ?loc node =
  let get_dvty = function
    | DEvar (_,dvty) ->
        dvty
    | DEpv pv ->
        [], specialize_pv pv
    | DErs rs ->
        specialize_rs rs
    | DEls ls ->
        specialize_ls ls
    | DEconst (Number.ConstInt _) ->
        dvty_int
    | DEconst (Number.ConstReal _) ->
        dvty_real
    | DEapp ({de_dvty = (arg::argl, res)}, de2) ->
        dexpr_expected_type de2 arg;
        argl, res
    | DEapp ({de_dvty = ([],res)} as de1, de2) ->
        let f,a,r = match specialize_rs rs_func_app with
          | [f;a],r -> f,a,r | _ -> assert false in
        begin try dity_unify res f with Exit ->
          let rec down n de = match de.de_node with
            | DEapp (de,_) -> down (succ n) de
            | _ when n = 0 -> Loc.errorm ?loc:de.de_loc
                "This expression has type %a,@ it cannot be applied"
                print_dity (dity_of_dvty de.de_dvty)
            | _ -> Loc.errorm ?loc:de.de_loc
                "This expression has type %a,@ but is applied to %d arguments"
                print_dity (dity_of_dvty de.de_dvty) (succ n) in
          down 0 de1
        end;
        dexpr_expected_type de2 a;
        [], r
    | DEfun (bl,_,_,de) ->
        List.map (fun (_,_,t) -> t) bl, dity_of_dvty de.de_dvty
    | DEany (bl,_,_,res) ->
        List.map (fun (_,_,t) -> t) bl, res
    | DElet (_,de)
    | DErec (_,de) ->
        de.de_dvty
    | DEnot de ->
        dexpr_expected_type de dity_bool;
        dvty_bool
    | DEand (de1,de2)
    | DEor (de1,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_bool;
        dvty_bool
    | DEif (de1,de2,de3) ->
        let res = dity_fresh () in
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 res;
        dexpr_expected_type de3 res;
        [], res
    | DEcase (_,[]) ->
        invalid_arg "Dexpr.dexpr: empty branch list in DEcase"
    | DEcase (de,bl) ->
        let ety = dity_fresh () in
        let res = dity_fresh () in
        dexpr_expected_type de ety;
        List.iter (fun (dp,de) ->
          dpat_expected_type dp ety;
          dexpr_expected_type de res) bl;
        [], res
    | DEassign al ->
        List.iter (fun (de1,rs,de2) ->
          let argl, res = specialize_rs rs in
          let ls = match rs.rs_logic with RLls ls -> ls
            | _ -> invalid_arg "Dexpr.dexpr: not a field" in
          dity_unify_app ls dexpr_expected_type [de1] argl;
          dexpr_expected_type_weak de2 res) al;
        dvty_unit
    | DEwhile (de1,_,_,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_unit;
        dvty_unit
    | DEfor (_,de_from,_,de_to,_,de) ->
        dexpr_expected_type de_from dity_int;
        dexpr_expected_type de_to dity_int;
        dexpr_expected_type de dity_unit;
        dvty_unit
    | DEtry (_,[]) ->
        invalid_arg "Dexpr.dexpr: empty branch list in DEtry"
    | DEtry (de,bl) ->
        let res = dity_fresh () in
        dexpr_expected_type de res;
        List.iter (fun (xs,dp,de) ->
          dpat_expected_type dp (specialize_xs xs);
          dexpr_expected_type de res) bl;
        [], res
    | DEraise (xs,de) ->
        dexpr_expected_type de (specialize_xs xs);
        [], dity_fresh ()
    | DEghost de ->
        de.de_dvty
    | DEassert _ ->
        dvty_unit
    | DEpure _
    | DEabsurd ->
        [], dity_fresh ()
    | DEtrue
    | DEfalse ->
        dvty_bool
    | DEcast (de,ity) ->
        dexpr_expected_type de (dity_of_ity ity);
        de.de_dvty
    | DEmark (_,de)
    | DEuloc (de,_)
    | DElabel (de,_) ->
        de.de_dvty in
  let dvty = Loc.try1 ?loc get_dvty node in
  { de_node = node; de_dvty = dvty; de_loc = loc }

(** Final stage *)

(** Binders *)

let binders bl =
  let sn = ref Sstr.empty in
  let binder (id, ghost, dity) =
    let id = match id with
      | Some ({pre_name = n} as id) ->
          let exn = match id.pre_loc with
            | Some loc -> Loc.Located (loc, Dterm.DuplicateVar n)
            | None -> Dterm.DuplicateVar n in
          sn := Sstr.add_new exn n !sn; id
      | None -> id_fresh "_" in
    create_pvsymbol id ~ghost (ity_of_dity dity) in
  List.map binder bl

(** Specifications *)

let to_fmla f = match f.t_ty with
  | None -> f
  | Some ty when ty_equal ty ty_bool -> t_equ f t_bool_true
  | _ -> Loc.error ?loc:f.t_loc Dterm.FmlaExpected

let create_assert = to_fmla

let create_invariant pl = List.map to_fmla pl

let create_post ity ql = List.map (fun (v,f) ->
  ity_equal_check ity v.pv_ity; Ity.create_post v.pv_vs (to_fmla f)) ql

let create_xpost xql = Mexn.mapi (fun xs ql -> create_post xs.xs_ity ql) xql

(** User effects *)

let rec effect_of_term t =
  let quit () = Loc.errorm ?loc:t.t_loc "unsupported effect expression" in
  match t.t_node with
  | Tapp (fs, [ta]) ->
      let v, ity, fa = effect_of_term ta in
      let ity = match fa with
        | Some {rs_cty = {cty_args = [arg]; cty_result = res}} ->
            ity_full_inst (ity_match isb_empty arg.pv_ity ity) res
        | Some _ -> assert false
        | None -> ity in
      begin try match ity.ity_node, restore_rs fs with
        | Ityreg {reg_its = ts}, ({rs_field = Some f} as rs)
          when List.exists (pv_equal f) ts.its_mfields -> v, ity, Some rs
        | _, {rs_cty={cty_args=[arg]; cty_result=res; cty_freeze=frz}} ->
            v, ity_full_inst (ity_match frz arg.pv_ity ity) res, None
        | _ -> quit () with Not_found -> quit () end
  | Tvar v ->
      let v = try restore_pv v with Not_found -> quit () in
      v, v.pv_ity, None
  | _ -> quit ()

let effect_of_dspec dsp =
  let pvs = Spv.of_list dsp.ds_reads in
  let add_write (l,eff) t = match effect_of_term t with
    | v, {ity_node = Ityreg reg}, fd ->
        let fs = match fd with
          | Some fd -> Spv.singleton (Opt.get fd.rs_field)
          | None -> Spv.of_list reg.reg_its.its_mfields in
        if not reg.reg_its.its_private && Spv.is_empty fs then
          Loc.errorm ?loc:t.t_loc "mutable expression expected";
        let rd = Spv.singleton v and wr = Mreg.singleton reg fs in
        let e = Loc.try2 ?loc:t.t_loc eff_write rd wr in
        (e,t)::l, eff_union_par eff e
    | _ ->
        Loc.errorm ?loc:t.t_loc "mutable expression expected" in
  let wl, eff = List.fold_left add_write ([], eff_read pvs) dsp.ds_writes in
  let eff = Mexn.fold (fun xs _ eff -> eff_raise eff xs) dsp.ds_xpost eff in
  let eff = if dsp.ds_diverge then eff_diverge eff else eff in
  wl, eff

(* TODO: add warnings for empty postconditions (anywhere)
    and empty exceptional postconditions (toplevel). *)
let check_spec dsp ecty e =
  let bad_write weff eff = not (Mreg.submap (fun _ s1 s2 -> Spv.subset s1 s2)
                                            weff.eff_writes eff.eff_writes) in
  let bad_raise xeff eff = not (Sexn.subset xeff.eff_raises eff.eff_raises) in
  (* computed effect vs user effect *)
  let check_rw = dsp.ds_checkrw in
  let uwrl, ue = effect_of_dspec dsp in
  let ucty = create_cty ecty.cty_args ecty.cty_pre ecty.cty_post
    ecty.cty_xpost ecty.cty_oldies ue ecty.cty_result in
  let ueff = ucty.cty_effect and eeff = ecty.cty_effect in
  let urds = ueff.eff_reads and erds = eeff.eff_reads in
  (* check that every user effect actually happens *)
  if not (Spv.subset urds erds) then Loc.errorm ?loc:e.e_loc
    "variable@ %a@ does@ not@ occur@ in@ this@ expression"
    Pretty.print_vs (Spv.choose (Spv.diff urds erds)).pv_vs;
  if bad_write ueff eeff then List.iter (fun (weff,t) ->
    if bad_write weff eeff then Loc.errorm ?loc:t.t_loc
      "this@ write@ effect@ does@ not@ happen@ in@ the@ expression") uwrl;
  if bad_raise ueff eeff then Loc.errorm ?loc:e.e_loc
    "this@ expression@ does@ not@ raise@ exception@ %a"
    print_xs (Sexn.choose (Sexn.diff ueff.eff_raises eeff.eff_raises));
  if ueff.eff_oneway && not eeff.eff_oneway then Loc.errorm ?loc:e.e_loc
    "this@ expression@ does@ not@ diverge";
  (* check that every computed effect is listed *)
  if check_rw && not (Spv.subset erds urds) then Spv.iter (fun v ->
    Loc.errorm ?loc:e.e_loc
      "this@ expression@ depends@ on@ variable@ %a@ left@ out@ in@ \
      the@ specification" Pretty.print_vs v.pv_vs) (Spv.diff erds urds);
  if check_rw && bad_write eeff ueff then
    Loc.errorm ?loc:(e_locate_effect (fun eff -> bad_write eff ueff) e)
      "this@ expression@ produces@ an@ unlisted@ write@ effect";
  if ecty.cty_args <> [] && bad_raise eeff ueff then Sexn.iter (fun xs ->
    Loc.errorm ?loc:(e_locate_effect (fun eff -> Sexn.mem xs eff.eff_raises) e)
      "this@ expression@ raises@ unlisted@ exception@ %a"
      print_xs xs) (Sexn.diff eeff.eff_raises ueff.eff_raises);
  if eeff.eff_oneway && not ueff.eff_oneway then
    Loc.errorm ?loc:(e_locate_effect (fun eff -> eff.eff_oneway) e)
      "this@ expression@ may@ diverge,@ but@ this@ is@ not@ \
        stated@ in@ the@ specification"

let check_aliases recu c =
  let rds_regs = c.cty_freeze.isb_reg in
  let report r _ _ =
    if Mreg.mem r rds_regs then let spv = Spv.filter
        (fun v -> ity_r_occurs r v.pv_ity) (cty_reads c) in
      Loc.errorm "The type of this function contains an alias with \
        external variable %a" print_pv (Spv.choose spv)
    else Loc.errorm "The type of this function contains an alias" in
  (* we allow the value in a non-recursive function to contain
     regions coming the function's arguments, but not from the
     context. It is sometimes useful to write a function around
     a constructor or a projection. For recursive functions, we
     impose the full non-alias discipline, to ensure the safety
     of region polymorphism (see add_rec_mono). We do not track
     aliases inside the type of an argument or a result, which
     may break the type inference, but we have a safety net
     type checking in Expr. *)
  let add_ity regs ity =
    let frz = ity_freeze isb_empty ity in
    Mreg.union report regs frz.isb_reg in
  let add_arg regs v = add_ity regs v.pv_ity in
  let regs = List.fold_left add_arg rds_regs c.cty_args in
  ignore (add_ity (if recu then regs else rds_regs) c.cty_result)

let check_fun rsym dsp e =
  let c,e = match e with
    | { c_node = Cfun e; c_cty = c } -> c,e
    | _ -> invalid_arg "Dexpr.check_fun" in
  let c = match rsym with
    | Some s -> s.rs_cty
    | None -> c in
  check_spec dsp c e;
  check_aliases (rsym <> None) c

(** Environment *)

type env = {
  rsm : rsymbol Mstr.t;
  pvm : pvsymbol Mstr.t;
  old : (pvsymbol Mstr.t * (let_defn * pvsymbol) Hpv.t) Mstr.t;
}

let env_empty = {
  rsm = Mstr.empty;
  pvm = Mstr.empty;
  old = Mstr.empty;
}

exception UnboundLabel of string

let find_old pvm (ovm,old) v =
  if v.pv_ity.ity_imm then v else
  let n = v.pv_vs.vs_name.id_string in
  (* if v is top-level, both ov and pv are None.
     If v is local, ov and pv must be equal to v.
     If they are not equal, then v is defined under the label,
     so we return v and do not register an "oldie" for it. *)
  let ov = Mstr.find_opt n ovm in
  let pv = Mstr.find_opt n pvm in
  if not (Opt.equal pv_equal ov pv) then v
  else match Hpv.find_opt old v with
    | Some (_,o) -> o
    | None ->
        let e = e_pure (t_var v.pv_vs) in
        let id = id_clone v.pv_vs.vs_name in
        let ld = let_var id ~ghost:true e in
        Hpv.add old v ld; snd ld

let register_old env v l =
  find_old env.pvm (Mstr.find_exn (UnboundLabel l) l env.old) v

let get_later env later = later env.pvm (register_old env)

let add_label ({pvm = pvm; old = old} as env) l =
  let ht = Hpv.create 3 in
  { env with old = Mstr.add l (pvm, ht) old }, ht

let rebase_old {pvm = pvm} preold old fvs =
  let rebase v (_,{pv_vs = o}) sbs =
    if not (Mvs.mem o fvs) then sbs else match preold with
      | Some preold ->
          Mvs.add o (t_var (find_old pvm preold v).pv_vs) sbs
      | None -> raise (UnboundLabel "0") in
  Hpv.fold rebase old Mvs.empty

let rebase_pre env preold old pl =
  let pl = List.map to_fmla pl in
  let fvs = List.fold_left t_freevars Mvs.empty pl in
  let sbs = rebase_old env preold old fvs in
  List.map (t_subst sbs) pl

let rebase_variant env preold old varl =
  let add s (t,_) = t_freevars s t in
  let fvs = List.fold_left add Mvs.empty varl in
  let sbs = rebase_old env preold old fvs in
  let conv (t,rel) = t_subst sbs t, rel in
  List.map conv varl

let get_oldies old =
  Hpv.fold (fun v (_,o) sbs -> Mpv.add o v sbs) old Mpv.empty

let add_rsymbol ({rsm = rsm; pvm = pvm} as env) rs =
  let n = rs.rs_name.id_string in
  let pvm = match rs.rs_logic with
    | RLpv pv -> Mstr.add n pv pvm
    | _ -> pvm in
  { env with rsm = Mstr.add n rs rsm; pvm = pvm }

let add_pvsymbol ({pvm = pvm} as env) pv =
  let n = pv.pv_vs.vs_name.id_string in
  { env with pvm = Mstr.add n pv pvm }

let add_pv_map ({pvm = pvm} as env) vm =
  { env with pvm = Mstr.set_union vm pvm }

let add_binders env pvl = List.fold_left add_pvsymbol env pvl

(** Abstract values *)

let cty_of_spec env bl mask dsp dity =
  let ity = ity_of_dity dity in
  let bl = binders bl in
  let env = add_binders env bl in
  let preold = Mstr.find_opt "0" env.old in
  let env, old = add_label env "0" in
  let dsp = get_later env dsp ity in
  let _, eff = effect_of_dspec dsp in
  let eff = eff_reset_overwritten eff in
  let eff = eff_reset eff (ity_freeregs Sreg.empty ity) in
  let p = rebase_pre env preold old dsp.ds_pre in
  let q = create_post ity dsp.ds_post in
  let xq = create_xpost dsp.ds_xpost in
  create_cty ~mask bl p q xq (get_oldies old) eff ity

(** Expressions *)

let warn_unused s loc =
  if s = "" || s.[0] <> '_' then
  Warning.emit ?loc "unused variable %s" s

let check_used_pv e pv = if not (Spv.mem pv e.e_effect.eff_reads) then
  warn_unused pv.pv_vs.vs_name.id_string pv.pv_vs.vs_name.id_loc

let e_let_check ld e = match ld with
  | LDvar (v,_) -> check_used_pv e v; e_let ld e
  | _           -> e_let ld e

let rec strip uloc labs de = match de.de_node with
  | DEcast (de,_) -> strip uloc labs de
  | DEuloc (de,loc) -> strip (Some (Some loc)) labs de
  | DElabel (de,s) -> strip uloc (Slab.union labs s) de
  | _ -> uloc, labs, de

let get_pv env n = Mstr.find_exn (Dterm.UnboundVar n) n env.pvm
let get_rs env n = Mstr.find_exn (Dterm.UnboundVar n) n env.rsm

let proxy_labels = Slab.singleton proxy_label

let rec expr uloc env ({de_loc = loc} as de) =
  let uloc, labs, de = strip uloc Slab.empty de in
  let e = Loc.try3 ?loc try_expr uloc env de in
  let loc = Opt.get_def loc uloc in
  if loc = None && Slab.is_empty labs
  then e else e_label_push ?loc labs e

and cexp uloc env ghost ({de_loc = loc} as de) vl =
  let uloc, labs, de = strip uloc Slab.empty de in
  if not (Slab.is_empty labs) then Warning.emit ?loc
    "Ignoring labels over a higher-order expression";
  Loc.try5 ?loc try_cexp uloc env ghost de vl

and try_cexp uloc env ghost ({de_dvty = argl,res} as de0) vl =
  let rec drop vl al = match vl, al with
    | _::vl, _::al -> drop vl al | _ -> al in
  let apply app s =
    let argl = List.map ity_of_dity (drop vl argl) in
    let c = app s vl argl (ity_of_dity res) in
    ghost || c_ghost c, [], c in
  let add_ld   ld (gh,l,c) = gh, ld :: l, c in
  let add_ldl ldl (gh,l,c) = gh, ldl @ l, c in
  let proxy c =
    if vl = [] then ghost || c_ghost c,[],c else
    let loc = Opt.get_def de0.de_loc uloc in
    let id = id_fresh ?loc ~label:proxy_labels "h" in
    let ld, s = let_sym id ~ghost c in
    add_ld ld (apply c_app s) in
  match de0.de_node with
  | DEvar (n,_) -> apply c_app (get_rs env n)
  | DErs s -> apply c_app s
  | DEls s -> apply c_pur s
  | DEapp (de1,de2) ->
      let e2 = expr uloc env de2 in
      begin match e2.e_node with
        | Evar v when Slab.is_empty e2.e_label ->
            cexp uloc env ghost de1 (v::vl)
        | _ ->
            let id = id_fresh ?loc:e2.e_loc ~label:proxy_labels "o" in
            let ld, v = let_var id (e_ghostify ghost e2) in
            add_ld ld (cexp uloc env ghost de1 (v::vl))
      end
  | DEghost de ->
      cexp uloc env true de vl
  | DEfun (bl,msk,dsp,de) ->
      let dvl _ _ = [] in
      let c, dsp, _ = lambda uloc env (binders bl) msk dsp dvl de in
      check_fun None dsp c;
      proxy c
  | DEany (bl,msk,dsp,dity) ->
      proxy (c_any (cty_of_spec env bl msk dsp dity))
  | DElet ((_,_,_,{de_dvty = ([],_)}) as dldf,de) ->
      let ld, env = var_defn uloc env ghost dldf in
      add_ld ld (cexp uloc env ghost de vl)
  | DElet (dldf,de) ->
      let ldl0, env = sym_defn uloc env ghost dldf in
      add_ldl ldl0 (cexp uloc env ghost de vl)
  | DErec (drdf,de) ->
      let ld, env = rec_defn uloc env ghost drdf in
      add_ld ld (cexp uloc env ghost de vl)
  | DEmark _ ->
      Loc.errorm "Marks are not allowed over higher-order expressions"
  | DEpv _ | DEconst _ | DEnot _ | DEand _ | DEor _ | DEif _ | DEcase _
  | DEassign _ | DEwhile _ | DEfor _ | DEtry _ | DEraise _ | DEassert _
  | DEpure _ | DEabsurd | DEtrue | DEfalse -> assert false (* expr-only *)
  | DEcast _ | DEuloc _ | DElabel _ -> assert false (* already stripped *)

and try_expr uloc env ({de_dvty = argl,res} as de0) =
  match de0.de_node with
  | DEvar (n,_) when argl = [] ->
      e_var (get_pv env n)
  | DEpv v ->
      e_var v
  | DEconst c ->
      e_const c
  | DEapp ({de_dvty = ([],_)} as de1, de2) ->
      let e1 = expr uloc env de1 in
      let e2 = expr uloc env de2 in
      e_app rs_func_app [e1; e2] [] (ity_of_dity res)
  | DEvar _ | DErs _ | DEls _ | DEapp _ | DEfun _ | DEany _ ->
      let cgh,ldl,c = try_cexp uloc env false de0 [] in
      let e = e_ghostify cgh (e_exec c) in
      List.fold_right e_let_check ldl e
  | DElet ((_,_,_,{de_dvty = ([],_)}) as dldf,de) ->
      let ld, env = var_defn uloc env false dldf in
      let e2 = expr uloc env de in
      e_let ld e2
  | DElet (dldf,de) ->
      let ldl, env = sym_defn uloc env false dldf in
      List.fold_right e_let_check ldl (expr uloc env de)
  | DErec (drdf,de) ->
      let ld, env = rec_defn uloc env false drdf in
      e_let ld (expr uloc env de)
  | DEnot de ->
      e_not (expr uloc env de)
  | DEand (de1,de2) ->
      e_and (expr uloc env de1) (expr uloc env de2)
  | DEor (de1,de2) ->
      e_or (expr uloc env de1) (expr uloc env de2)
  | DEif (de1,de2,de3) ->
      e_if (expr uloc env de1) (expr uloc env de2) (expr uloc env de3)
  | DEcase (de1,bl) ->
      let e1 = expr uloc env de1 in
      let mk_branch (dp,de) =
        let vm, pat = create_prog_pattern dp.dp_pat e1.e_ity e1.e_mask in
        let e = expr uloc (add_pv_map env vm) de in
        Mstr.iter (fun _ v -> check_used_pv e v) vm;
        pat, e in
      let bl = List.rev_map mk_branch bl in
      let pl = List.rev_map (fun (p,_) -> [p.pp_pat]) bl in
      let v = create_vsymbol (id_fresh "x") (ty_of_ity e1.e_ity) in
      (* TODO: this is the right place to show the missing patterns,
         but we do not have access to the current known_map to do that *)
      let bl = if Pattern.is_exhaustive [t_var v] pl then bl else begin
        if List.length bl > 1 then Warning.emit ?loc:de0.de_loc
          "Non-exhaustive pattern matching, asserting `absurd'";
        let _,pp = create_prog_pattern PPwild e1.e_ity e1.e_mask in
        (pp, e_absurd (ity_of_dity res)) :: bl end in
      e_case e1 (List.rev bl)
  | DEassign al ->
      let conv (de1,f,de2) = expr uloc env de1, f, expr uloc env de2 in
      e_assign (List.map conv al)
  | DEwhile (de1,dinv,dvarl,de2) ->
      let e1 = expr uloc env de1 in
      let e2 = expr uloc env de2 in
      let inv = get_later env dinv in
      let varl = get_later env dvarl in
      e_while e1 (create_invariant inv) varl e2
  | DEfor (id,de_from,dir,de_to,dinv,de) ->
      let e_from = expr uloc env de_from in
      let e_to = expr uloc env de_to in
      let v = create_pvsymbol id ity_int in
      let env = add_pvsymbol env v in
      let e = expr uloc env de in
      let inv = get_later env dinv in
      e_for v e_from dir e_to (create_invariant inv) e
  | DEtry (de1,bl) ->
      let e1 = expr uloc env de1 in
      let add_branch m (xs,dp,de) =
        let vm, pat = create_prog_pattern dp.dp_pat xs.xs_ity xs.xs_mask in
        let e = expr uloc (add_pv_map env vm) de in
        Mstr.iter (fun _ v -> check_used_pv e v) vm;
        Mexn.add xs ((pat, e) :: Mexn.find_def [] xs m) m in
      let xsm = List.fold_left add_branch Mexn.empty bl in
      let is_simple p = match p.pat_node with
        | Papp (fs,[]) -> is_fs_tuple fs
        | Pvar _ | Pwild -> true | _ -> false in
      let conv_simple p (ity,ghost) = match p.pat_node with
        | Pvar v -> Ity.restore_pv v
        | _ -> create_pvsymbol (id_fresh "_") ~ghost ity in
      let mk_branch xs = function
        | [{ pp_pat = { pat_node = Pvar v }}, e] ->
            [Ity.restore_pv v], e
        | [{ pp_pat = { pat_node = (Pwild | Papp (_,[])) }}, e]
          when ity_equal xs.xs_ity ity_unit ->
            [], e
        | [{ pp_pat = { pat_node = Pwild }}, e] ->
            let ghost = mask_ghost xs.xs_mask in
            [create_pvsymbol (id_fresh "_") ~ghost xs.xs_ity], e
        | [{ pp_pat = { pat_node = Papp (fs,(_::_::_ as pl)) }}, e]
          when is_fs_tuple fs && List.for_all is_simple pl ->
            let tyl = match xs.xs_ity.ity_node with (* tuple *)
              | Ityapp (_,tyl,_) -> tyl | _ -> assert false in
            let ghl = match xs.xs_mask with
              | MaskTuple ml -> List.map mask_ghost ml
              | MaskVisible -> List.map Util.ffalse pl
              | MaskGhost -> List.map Util.ttrue pl in
            List.map2 conv_simple pl (List.combine tyl ghl), e
        | bl ->
            let id = id_fresh "q" in
            let vl = match xs.xs_mask with
              | _ when ity_equal xs.xs_ity ity_unit -> []
              | MaskGhost -> [create_pvsymbol id ~ghost:true xs.xs_ity]
              | MaskVisible -> [create_pvsymbol id ~ghost:false xs.xs_ity]
              | MaskTuple ml ->
                  let mk_var ity m =
                    create_pvsymbol id ~ghost:(mask_ghost m) ity in
                  let tyl = match xs.xs_ity.ity_node with (* tuple *)
                    | Ityapp (_,tyl,_) -> tyl | _ -> assert false in
                  List.map2 mk_var tyl ml in
            let t, e = match vl with
              | [] -> t_void, e_void | [v] -> t_var v.pv_vs, e_var v
              | vl -> t_tuple (List.map (fun v -> t_var v.pv_vs) vl),
                      e_tuple (List.map e_var vl) in
            let pl = List.rev_map (fun (p,_) -> [p.pp_pat]) bl in
            let bl = if Pattern.is_exhaustive [t] pl then bl else
              let _,pp = create_prog_pattern PPwild xs.xs_ity xs.xs_mask in
              (pp, e_raise xs e (ity_of_dity res)) :: bl in
            vl, e_case e (List.rev bl) in
      e_try e1 (Mexn.mapi mk_branch xsm)
  | DEraise (xs,de) ->
      e_raise xs (expr uloc env de) (ity_of_dity res)
  | DEghost de ->
      e_ghostify true (expr uloc env de)
  | DEassert (ak,f) ->
      e_assert ak (create_assert (get_later env f))
  | DEpure t ->
      e_pure (get_later env t)
  | DEabsurd ->
      e_absurd (ity_of_dity res)
  | DEtrue ->
      e_true
  | DEfalse ->
      e_false
  | DEmark ({pre_name = l},de) ->
      let env, old = add_label env l in
      let put _ (ld,_) e = e_let ld e in
      Hpv.fold put old (expr uloc env de)
  | DEcast _ | DEuloc _ | DElabel _ ->
      assert false (* already stripped *)

and var_defn uloc env ghost (id,gh,kind,de) =
  let e = match kind with
    | RKlemma -> Loc.errorm ?loc:id.pre_loc
        "Lemma-functions must have parameters"
    | RKfunc | RKpred | RKlocal | RKnone ->
        e_ghostify ghost (expr uloc env de) in
  let ld, v = let_var id ~ghost:gh e in
  ld, add_pvsymbol env v

and sym_defn uloc env ghost (id,gh,kind,de) =
  let ghost, ldl, c = cexp uloc env ghost de [] in
  let ld, s = let_sym id ~ghost:(gh || ghost) ~kind c in
  ldl @ [ld], add_rsymbol env s

and rec_defn uloc env ghost {fds = dfdl} =
  let step1 env (id, gh, kind, bl, mask, dsp, dvl, ({de_dvty = dvty} as de)) =
    let pvl = binders bl in
    let ity = Loc.try1 ?loc:de.de_loc ity_of_dity (dity_of_dvty dvty) in
    let cty = create_cty ~mask pvl [] [] Mexn.empty Mpv.empty eff_empty ity in
    let rs = create_rsymbol id ~ghost:(gh || ghost) ~kind:RKnone cty in
    add_rsymbol env rs, (rs, kind, mask, dsp, dvl, de) in
  let env, fdl = Lists.map_fold_left step1 env dfdl in
  let step2 (rs, kind, mask, dsp, dvl, de) (fdl,dspl) =
    let {rs_name = {id_string = nm; id_loc = loc}; rs_cty = c} = rs in
    let lam, dsp, dvl = lambda uloc env c.cty_args mask dsp dvl de in
    if c_ghost lam && not (rs_ghost rs) then Loc.errorm ?loc
      "Function %s must be explicitly marked ghost" nm;
    if mask_spill lam.c_cty.cty_mask c.cty_mask then Loc.errorm ?loc
      "Function %s returns unexpected ghost results" nm;
    (rs, lam, dvl, kind)::fdl, dsp::dspl in
  (* check for unexpected aliases in case of trouble *)
  let fdl, dspl = try List.fold_right step2 fdl ([],[]) with
    | Loc.Located (_, Ity.TypeMismatch _) | Ity.TypeMismatch _ as exn ->
        List.iter (fun ({rs_name = {id_loc = loc}} as rs,_,_,_,_,_) ->
          Loc.try2 ?loc check_aliases true rs.rs_cty) fdl;
        raise exn in
  let ld, rdl = try let_rec fdl with
    | Loc.Located (_, Ity.TypeMismatch _) | Ity.TypeMismatch _ as exn ->
        List.iter (fun ({rs_name = {id_loc = loc}},lam,_,_) ->
          Loc.try2 ?loc check_aliases true lam.c_cty) fdl;
        raise exn in
  let add_fd env {rec_sym = s; rec_rsym = rs; rec_fun = c} dsp =
    Loc.try3 ?loc:rs.rs_name.id_loc check_fun (Some rs) dsp c;
    add_rsymbol env s in
  ld, List.fold_left2 add_fd env rdl dspl

and lambda uloc env pvl mask dsp dvl de =
  let env = add_binders env pvl in
  let preold = Mstr.find_opt "0" env.old in
  let env, old = add_label env "0" in
  let e = expr uloc env de in
  let dsp = get_later env dsp e.e_ity in
  let dvl = get_later env dvl in
  let dvl = rebase_variant env preold old dvl in
  let p = rebase_pre env preold old dsp.ds_pre in
  let q = create_post e.e_ity dsp.ds_post in
  let xq = create_xpost dsp.ds_xpost in
  c_fun ~mask pvl p q xq (get_oldies old) e, dsp, dvl

let rec_defn ?(keep_loc=true) drdf =
  let uloc = if keep_loc then None else Some None in
  fst (rec_defn uloc env_empty false drdf)

let rec mask_of_fun de = match de.de_node with
  | DEfun (_,msk,_,_) -> msk
  | DEghost de | DEcast (de,_)
  | DEuloc (de,_) | DElabel (de,_) -> mask_of_fun de
  | _ -> MaskGhost (* a safe default for checking *)

let let_defn ?(keep_loc=true) (id, ghost, kind, de) =
  let uloc = if keep_loc then None else Some None in
  let {pre_name = nm; pre_loc = loc} = id in
  match kind, de.de_dvty with
  | _, (_::_, _) ->
      let cgh, ldl, c = cexp uloc env_empty false de [] in
      if ldl <> [] then Loc.errorm ?loc:de.de_loc
        "Illegal top-level function definition";
      if cgh && not ghost then Loc.errorm ?loc
        "Function %s must be explicitly marked ghost" nm;
      let spl = mask_spill c.c_cty.cty_mask (mask_of_fun de) in
      if spl && not ghost then Loc.errorm ?loc
        "Function %s returns unexpected ghost results" nm;
      fst (let_sym id ~ghost ~kind c)
  | (RKfunc | RKpred), ([], _) ->
      (* FIXME: let ghost constant c = <effectful> *)
      let e = expr uloc env_empty de in
      if mask_ghost e.e_mask && not ghost then Loc.errorm ?loc
        "Function %s must be explicitly marked ghost" nm;
      let c = c_fun [] [] [] Mexn.empty Mpv.empty e in
      (* the rsymbol will carry a single postcondition "the result
         is equal to the logical constant". Any user-written spec
         will be checked once, in-place, under Eexec. Since kind
         guarantees the absence of effects and any external reads,
         this one-time check is sufficient, and we won't pollute
         the later WPs with the copies of the spec. When preparing
         the logical constant definition, we must extract that
         user-written specification from under Cfun, and put it
         into an axiom. *)
      fst (let_sym id ~ghost ~kind c)
  | RKnone, ([], _) ->
      let e = expr uloc env_empty de in
      if mask_ghost e.e_mask && not ghost then Loc.errorm ?loc
        "Variable %s must be explicitly marked ghost" nm;
      fst (let_var id ~ghost e)
  | RKlemma, ([], _) -> Loc.errorm ?loc
      "Lemma-functions must have parameters"
  | RKlocal, _ -> invalid_arg "Dexpr.let_defn"

let expr ?(keep_loc=true) de =
  let uloc = if keep_loc then None else Some None in
  expr uloc env_empty de

let () = Exn_printer.register (fun fmt e -> match e with
  | UnboundLabel s ->
      Format.fprintf fmt "unbound label %s" s
  | _ -> raise e)
