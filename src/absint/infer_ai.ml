
module type Inv_gen = sig
  val infer_loop_invariants:
    widening:int -> Env.env -> Pmodule.pmodule -> Pmodule.pmodule
end

module Make (D: Domain.DOMAIN) = struct

  open Pmodule
  open Pdecl
  open Expr
  open Ity

  let infer_loop_invariants ~widening env pmod =
    let module AI = Ai_cfg.Make (struct
        let env = env
        let pmod = pmod
        let widening = widening
        module D = D
      end)
    in

    let rec reconstruct_expr cfg context fixp e =
      let reconstruct = reconstruct_expr cfg context fixp in
      let expl = "expl:loop invariant via abstract interpretation" in
      match e.e_node with
      | Elet (LDvar (pv, e), e2) ->
        e_let (let_var_raw pv (reconstruct e)) (reconstruct e2)
      | Elet (LDsym _,_) ->
         Warning.emit "invariants are not yet generated for inner let functions";
         e
      | Elet (LDrec _, _) ->
         Warning.emit "invariants are not yet generated for inner let rec";
         e
      | Evar _ | Econst _ | Eassign _ | Eabsurd | Epure _
      | Eassert _ | Eexec _ -> e
      | Eif (e1, e2, e3) ->
         e_if (reconstruct e1) (reconstruct e2) (reconstruct e3)
      | Ematch (e,  pats, exns) ->
        let pats = List.map (fun (p, e) -> p, reconstruct e) pats in
        let exns = Mxs.map (fun (pvs, e) -> pvs, reconstruct e) exns in
        e_match (reconstruct e) pats exns
      | Eraise (x, e_) -> e_raise x (reconstruct e_) e.e_ity
      | Eghost e -> e_ghostify true (reconstruct e)
      | Ewhile (e_cond, inv, vari, e_loop) ->
          let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
          let t = AI.domain_to_term cfg context new_inv in
          let t = Term.t_attr_add (Ident.create_attribute expl) t in
          if Debug.test_flag Uf_domain.infer_debug then
            Pretty.print_term Format.std_formatter t;
          e_while (reconstruct e_cond) (t :: inv) vari (reconstruct e_loop)
      | Efor(pv, (f, d, to_), pv2, inv, e_loop) ->
         let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
         let t = AI.domain_to_term cfg context new_inv in
         let t = Term.t_attr_add (Ident.create_attribute expl) t in
         e_for pv (e_var f) d (e_var to_) pv2 (t :: inv) (reconstruct e_loop)
      | Eexn (xs,e) -> e_exn xs (reconstruct e)
    in


    let clone_infer_pdecl pdecl rssm =
      let open Ident in
      match pdecl.pd_node with
      | PDpure ->
         Format.eprintf "PDpure@.";
         (* TODO check how to do it. If a goal was generated by the
            VCgen that VC should be generated again, at a later stage,
            when the decl is added to the module. *)
         let is_not_vc d = not true in
         let open Decl in
         create_pure_decl_l (List.filter is_not_vc pdecl.pd_pure), rssm
      | PDlet (LDsym (rs1, {c_node = Capp (rs2,pvl)})) ->
         Format.eprintf "PDlet LDsym Capp %s" rs1.rs_name.id_string;
         List.iter (fun pv -> Format.eprintf "%a" print_pv pv) pvl;
         Format.eprintf "@.";
         (* TODO not sure what these pvl are. *)
         let rs2 = Mrs.find_def rs2 rs2 rssm in
         let ityl = List.map (fun pv -> pv.pv_ity) rs1.rs_cty.cty_args in
         let ity  = rs1.rs_cty.cty_result in
         let cexp = c_app rs2 pvl ityl ity in
         let id = id_clone rs1.rs_name in
         let let_defn, new_rs =
           let_sym id ~ghost:(rs_ghost rs1) ~kind:(rs_kind rs1) cexp in
         create_let_decl let_defn, Mrs.add rs1 new_rs rssm
      | PDlet (LDsym (rs, {c_node = Cpur (ls,pvl)})) ->
         Format.eprintf "PDlet LDsym Cpur %s@." rs.rs_name.id_string;
         pdecl, rssm
      | PDlet (LDsym (rs, ({c_node = Cfun e} as cexp))) ->
         Format.eprintf "PDlet LDsym Cfun %s@." rs.rs_name.id_string;
         let open Ity in
         let preconditions = cexp.c_cty.cty_pre in
         let cfg = AI.start_cfg rs in
         let context = AI.empty_context () in
         List.iter (AI.add_variable cfg context) cexp.c_cty.cty_args;
         if Debug.test_flag Uf_domain.infer_debug then
           Format.printf "%a@." Expr.print_expr e;
         ignore (AI.put_expr_with_pre cfg context e preconditions);
         (* will hold the diffrent file offsets (useful when writing
               multiple invariants) *)
         let fixp = AI.eval_fixpoints cfg context in
         let new_e = reconstruct_expr cfg context fixp e in
         let ce = c_fun cexp.c_cty.cty_args cexp.c_cty.cty_pre
                    cexp.c_cty.cty_post cexp.c_cty.cty_xpost
                    cexp.c_cty.cty_oldies new_e in
         (* let let_defn = let_sym_raw rs ce in *)
         let id = id_clone rs.rs_name in
         let ce = c_rs_subst rssm ce in
         let let_defn, new_rs =
           let_sym id ~ghost:(rs_ghost rs) ~kind:(rs_kind rs) ce in
         create_let_decl let_defn, Mrs.add rs new_rs rssm
      | PDlet (LDsym (rs, {c_node = Cany; c_cty})) ->
         Format.eprintf "PDlet LDsym Cany %s@." rs.rs_name.id_string;
         pdecl, rssm
      | PDlet (LDvar (pv, e)) ->
         Format.eprintf "PDlet LDvar %s@." pv.pv_vs.vs_name.id_string;
         (* TODO we need a substitution map for PVs *)
         let id = id_clone pv.pv_vs.vs_name in
         let e = e_rs_subst rssm e in
         let let_defn,_ = let_var id ~ghost:pv.pv_ghost e in
         create_let_decl let_defn, rssm
      | PDlet (LDrec lrd) ->
         Format.eprintf "PDlet LDrec@.";
         Warning.emit "invariants are not yet generated for let rec";
         let rec_defn {rec_sym;rec_rsym;rec_fun;rec_varl} =
           rec_rsym,c_rs_subst rssm rec_fun,rec_varl,rs_kind rec_rsym in
         let let_defn, new_lrd = let_rec (List.map rec_defn lrd) in
         let rssm = List.fold_left2 (fun rssm rd1 rd2 ->
                      Mrs.add rd1.rec_sym rd2.rec_sym rssm) rssm lrd new_lrd in
         create_let_decl let_defn, rssm
      | PDexn _ | PDtype _ -> pdecl, rssm
    in

    let rec add_to_pmod (pmod_uc,rssm) decl =
      match decl with
      | Udecl pdecl ->
         let cloned_pdecl, rssm = clone_infer_pdecl pdecl rssm in
         add_pdecl ~warn:true ~vc:true pmod_uc cloned_pdecl, rssm
      | Uclone mod_inst -> add_clone pmod_uc mod_inst, rssm
      | Umeta (m, margs) -> add_meta pmod_uc m margs, rssm
      | Uscope (s, mis) ->
         let pmod_uc = open_scope pmod_uc s in
         let (s,rssm) = List.fold_left add_to_pmod (pmod_uc, rssm) mis in
         close_scope s ~import:true, rssm
      | Uuse pmod -> use_export pmod_uc pmod, rssm
    in

    let theory = pmod.mod_theory in
    let preid = Ident.id_clone Theory.(theory.th_name) in
    let pmuc = create_module env preid in
    let pmuc,_ =
      List.fold_left add_to_pmod (pmuc,Mrs.empty) pmod.mod_units in
    if Debug.test_flag Uf_domain.infer_debug then
      Format.eprintf "Invariants inferred.@.";
    close_module pmuc

end


module InvGenPolyhedra : Inv_gen = Make (Domain.Polyhedra)
module InvGenBox       : Inv_gen = Make (Domain.Box)
module InvGenOct       : Inv_gen = Make (Domain.Oct)
