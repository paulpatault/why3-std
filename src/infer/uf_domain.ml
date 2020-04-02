open Domain
open Apron
open Term

module Make(S:sig
    module    Dom : DOMAIN
    val       env : Env.env
    val  th_known : Decl.known_map
    val mod_known : Pdecl.known_map
  end) : TERM_DOMAIN = struct

  module Dom = S.Dom

  module Ai_logic = Ai_logic.Make(struct
      let       env = S.env
      let  th_known = S.th_known
      let mod_known = S.mod_known
    end)
  open Ai_logic

  exception Not_handled of term
  let fun_id x = x

  (* utility function that make equivalent classes and
     sum the last component *)
  let sum_list l =
    let sl = List.sort (fun (i, _) (j, _) -> compare i j) l in
    let rec merge = function
      | [] -> []
      | [b] -> [b]
      | (a, b) :: (c, d) :: q ->
         if a = c then merge ((a, b + d) :: q)
         else (a, b) :: merge ((c, d) :: q)
    in merge sl

  module TermToVar   = O2oterm.Make(struct type t = Var.t end)
  module TermToClass = O2oterm.Make(struct type t = Union_find.t end)
  module VarPool     = Set.Make(struct type t = Var.t
                                       let compare = compare end)

  type uf_man = {
    variable_mapping: (Apron.Var.t, term) Hashtbl.t;
    mutable apron_mapping: Var.t Mterm.t;
    mutable region_mapping: (Ity.pvsymbol * term) list Ity.Mreg.t;
    mutable region_var: vsymbol list Ity.Mreg.t;
    mutable env: Environment.t;

    mutable defined_terms: unit Mterm.t;

    (* UF_QF *)
    mutable class_to_term: TermToClass.t;
  }

  type uf_t = {
    classes: Union_find.set;
    uf_to_var: TermToVar.t;
    var_pool: VarPool.t;
  }
  (* type invariant: (see invariant_uf function below)
     - intersection of uf_to_var and var_pool is empty;
     -  the union of uf_to_var and var_pool contain all Variables from
     the universe*)


  type man = Dom.man * uf_man (* Manager *)
  type env = unit
  type t   = Dom.t * uf_t     (* Abstract values *)

  let tmp_pool = ["$p1";"$p2"; "$p3"] |> List.map Var.of_string

  let build_var_pool n =
    let rec build_var_pool_aux = function
      | 0 -> []
      | n -> let v = Var.of_string (Format.sprintf "$%d" n) in
             v :: build_var_pool_aux (n - 1) in
    build_var_pool_aux n |> VarPool.of_list

  let npool = 10

  let create_manager () =
    let var_pool = build_var_pool npool in
    let vars = Array.of_list (VarPool.elements var_pool @ tmp_pool) in
    let uf_man = {
        variable_mapping = Hashtbl.create 512;
        apron_mapping = Mterm.empty;
        region_mapping = Ity.Mreg.empty;
        region_var = Ity.Mreg.empty;
        env = Environment.make vars [||];
        defined_terms = Mterm.empty;
        class_to_term = TermToClass.empty; } in
    Dom.create_manager (), uf_man

  let empty_uf_domain = {
    classes = Union_find.empty;
    uf_to_var = TermToVar.empty;
    var_pool = build_var_pool npool;
  }

  let bottom (man, uf_man) _ =
    Dom.bottom man uf_man.env, empty_uf_domain

  let top (man, uf_man) _ =
    Dom.top man uf_man.env, empty_uf_domain

  let canonicalize (man, _) (a, _) =
    Dom.canonicalize man a

  let is_bottom (man, _) (a, _) =
    Dom.is_bottom man a

  let get_class_for_term uf_man t =
    try TermToClass.to_t uf_man.class_to_term t with Not_found ->
      let c = Union_find.new_class () in
      uf_man.class_to_term <- TermToClass.add uf_man.class_to_term t c;
      c

  (* let get_equivs uf_man uf t =
   *   let tcl = TermToClass.to_t uf_man.class_to_term t in
   *   Union_find.get_class tcl uf |> List.map (TermToClass.to_term uf_man.class_to_term) *)

  let apply_equal (man, uf_man) (dom,uf_t) tl =
    List.fold_left (fun (dom, var) t ->
        try match var with
          | None -> dom, Some (TermToVar.to_t uf_t.uf_to_var t)
          | Some var ->
            let expr = Linexpr1.make uf_man.env in
            let var' = TermToVar.to_t uf_t.uf_to_var t in
            Linexpr1.set_coeff expr var (Coeff.s_of_int (-1));
            Linexpr1.set_coeff expr var' (Coeff.s_of_int 1);
            let lincons = Lincons1.make expr Lincons1.EQ in
            let lincons_array = Lincons1.array_make uf_man.env 1 in
            Lincons1.array_set lincons_array 0 lincons;
            let d = Dom.meet_lincons_array man dom lincons_array in
            d, Some var
        with Not_found -> dom, var
      ) (dom, None) tl
    |> fst

  exception Constant

  let t_z_const a =
    if a >= 0 then t_nat_const a
    else t_app min_u_int [t_nat_const (-a)] (Some Ty.ty_int)

 (* let engine = Reduction_engine0.create {compute_defs = true; compute_builtin = true; compute_def_set = Sls.empty; } env known_logical_ident*)

  (* we assume that there will be no overflow (oops) *)
  let rec eval_term t =
    let t = t (* Reduction_engine0.normalize ~limit:50 engine  t*) in
    if Ty.ty_equal (t_type t) Ty.ty_int then
      let rec eval_num t =
        let open Number in
        match t.t_node with
        | Tvar _ -> Some t, 0
        | Tconst (Constant.ConstInt n) ->
          (None, BigInt.to_int n.il_int)
        | Tapp (func, args) when ls_equal func ad_int ->
          List.fold_left (fun (acc_a, acc_b) arg ->
              let a, b = eval_num arg in
              match a, acc_a with
              | None, None -> None, acc_b + b
              | Some t, Some v ->
                 Some (t_app ad_int [v; t] (Some Ty.ty_int)), acc_b + b
              | Some t, None | None, Some t -> Some t, acc_b + b
            ) (None, 0) args
        | Tapp (func, [a;b]) when ls_equal func min_int ->
          let ta, ca = eval_num a in
          let tb, cb = eval_num b in
          begin
            match ta, tb with
            | None, None -> None, ca - cb
            | Some t, Some v -> Some (t_app_infer min_int [t; v]), ca - cb
            | Some t, None -> Some t, ca - cb
            | None, Some t -> Some (t_app_infer min_u_int [t]), ca - cb
          end
        | Tapp (func, [a]) when ls_equal func min_u_int ->
          let ta, ca = eval_num a in
          begin
            match ta with
            | None -> None, - ca
            | Some a -> Some (t_app min_u_int [a] (Some Ty.ty_int)), - ca
          end
        | Tapp (func, args) ->
          let t = t_app func (List.map eval_term args) (Some (t_type t)) in
          Some t, 0
        | _ -> Some t, 0 in
      match eval_num t with
      | Some t, 0 -> t
      | Some t, a -> t_app ad_int [t; t_z_const a] (Some Ty.ty_int)
      | None, _ -> raise Constant
    else t_map eval_term t

  let rec replaceby t1 t2 t3 =
    if t_equal t3 t1 then t2
    else t_map (replaceby t1 t2) t3

  let do_eq (man, uf_man) t1 t2 =
    if not (Ty.ty_equal (t_type t1) Ity.ty_unit) then
      fun (d, ud) ->
        let cla = get_class_for_term uf_man t1 in
        let clb = get_class_for_term uf_man t2 in
        let ud = { ud with classes = Union_find.union cla clb ud.classes; } in
        let all_values = Union_find.flat ud.classes in
        let all_terms =
          List.map (fun cl ->
              TermToClass.to_term uf_man.class_to_term cl, ()) all_values
        in
        let all_values = all_terms
                         |> Mterm.of_list in
        let all_terms = all_terms |> List.map fst in
        Mterm.fold (fun v () (d, ud) ->
            (* This is far from perfect. If there is a function f, then terms `f a` and `f b` will be marked as equal.
             * But if there is g: 'a -> 'b -> 'c, then `g a b` and `g b a` can not be marked as such. (As the replacement is global.)
             * However, it is unclear wether it is or it is not a limitation. *)
            let v' = replaceby t1 t2 v in
            let v'' = replaceby t2 t1 v in
            let v' = try eval_term v' with Constant -> v in
            let v'' = try eval_term v'' with Constant -> v in
            let v' = if List.exists (t_equal v') all_terms then v'
                     else v in
            let v'' = if List.exists (t_equal v'') all_terms then v''
                      else v in
            if t_equal v v' && t_equal v v'' then d, ud
            else
              begin
                let cl  = get_class_for_term uf_man v
                and cl' = get_class_for_term uf_man v'
                and cl'' = get_class_for_term uf_man v'' in
                let cl_cl' = Union_find.union cl cl' ud.classes in
                let ud = { ud with classes = Union_find.union cl cl'' cl_cl' } in
                let d =
                  if Ty.ty_equal (t_type v) Ty.ty_int then
                    Union_find.get_class cl ud.classes
                    |> List.map (TermToClass.to_term uf_man.class_to_term)
                    |> apply_equal (man, uf_man) (d,ud)
                  else d
                in d, ud
              end
          ) all_values (d, ud)
    else fun_id

  (* probably not clever enough, will not work with a complex CFG with exceptions etc *)
  let print fmt (a, _) = Dom.print fmt a

  let get_var_for_term _ ref_dom term =
    let uf_to_var = !ref_dom.uf_to_var in
    try TermToVar.to_t uf_to_var term with Not_found ->
      let apron_var = VarPool.choose !ref_dom.var_pool in
      let uf_to_var = TermToVar.add uf_to_var term apron_var in
      let var_pool = VarPool.remove apron_var !ref_dom.var_pool in
      ref_dom := { !ref_dom with var_pool; uf_to_var };
      apron_var

  let eq_var (man, uf_man) dom_t v1 v2 =
    if v1 <> v2 then
      let expr = Linexpr1.make uf_man.env in
      Linexpr1.set_coeff expr v1 (Coeff.s_of_int 1);
      Linexpr1.set_coeff expr v2 (Coeff.s_of_int (-1));
      let lincons = Lincons1.make expr Lincons1.EQ in
      let lincons_array = Lincons1.array_make uf_man.env 1 in
      Lincons1.array_set lincons_array 0 lincons;
      Dom.meet_lincons_array man dom_t lincons_array
    else dom_t

  (* Check uf_t invariant. All apron variables being used are not in
     the pool. *)
  let invariant_uf uf_t =
    let var_pool = ref VarPool.empty in
    try
      let t2v = ref uf_t.uf_to_var in
      while true do
        let _, v = TermToVar.choose !t2v in
        var_pool := VarPool.add v !var_pool;
        t2v := TermToVar.remove_t !t2v v;
      done;
    with Not_found ->
      assert (VarPool.is_empty (VarPool.inter uf_t.var_pool !var_pool));
      assert (VarPool.equal (VarPool.union uf_t.var_pool !var_pool)
                (build_var_pool npool))

  let join_uf (man, uf_man) uf_t1 uf_t2 dom_t =
    invariant_uf uf_t1;
    invariant_uf uf_t2;
    let classes = Union_find.join uf_t1.classes uf_t2.classes in
    let rc = ref dom_t in
    let vars_to_replace = ref [] in
    let tmp_pool = ref tmp_pool in
    let var_pool = ref uf_t2.var_pool in
    let f_term t _ v = vars_to_replace := (t, v) :: !vars_to_replace in
    let f_t v1 _ t =
      let var_tmp = List.hd !tmp_pool in
      tmp_pool := List.tl !tmp_pool;
      rc := eq_var (man, uf_man) !rc v1 var_tmp;
      rc := Dom.forget_array man !rc [|v1|] false;
      var_pool := VarPool.add v1 !var_pool;
      vars_to_replace := (t, var_tmp) :: !vars_to_replace;
      assert (
          try ignore (TermToVar.to_term uf_t2.uf_to_var var_tmp); false
          with Not_found -> true) in
    let uf_to_var =
      TermToVar.union uf_t2.uf_to_var uf_t1.uf_to_var f_t f_term in
    let var_pool = !var_pool in
    let var_pool = VarPool.inter uf_t1.var_pool var_pool in
    let rud = ref { classes; uf_to_var; var_pool } in
    List.iter (fun (t, v) ->
        try
          let new_var = get_var_for_term uf_man rud t in
          rc := eq_var (man, uf_man) !rc v new_var;
          if v <> new_var then rc := Dom.forget_array man !rc [|v|] false;
        with Not_found ->
          Format.eprintf "REACHED END OF THE POOL@.@.@.";
          rc := Dom.forget_array man !rc [|v|] false;
      ) !vars_to_replace;
    invariant_uf !rud;
    !rc, !rud

  (* Why3 terms and APRON variables must be kept consistent. So. First
     there is the case where two different terms are linked to the
     same APRON variable. One on them must be erased. *)
  (* And this takes care of one term linked to 2 variables. (They are
     made equal, and then forgotten.) *)
  let join (man, uf_man) (dom_t1, uf_t1) (dom_t2, uf_t2) =
    let dom_t, uf_t = join_uf (man, uf_man) uf_t1 uf_t2 dom_t2 in
    let dom_t = Dom.join man dom_t1 dom_t in
    dom_t, uf_t

  let join_list man l = match l with
    | [] -> assert false
    | t::q -> List.fold_left (join man) t q

  let push_label (man, uf_man) _ i (dom_t, uf_t) =
    Dom.push_label man uf_man.env i dom_t, uf_t

  let warning_t s t =
    Format.eprintf "-- warning: %s -- triggered by %a of type %a@." s
      Pretty.print_term t Pretty.print_ty (t_type t)

  let ident_ret =
    Ident.{pre_name = "$pat";
           pre_attrs = Sattr.empty;
           pre_loc   = None; }

  let access_field constr constr_args t arg_index (proj, ty) =
      match t.t_node with
      | Tapp (func, args) when func.ls_constr = 1 ->
         List.nth args arg_index
      | Tvar _ | _ ->
         match proj with
         | None ->
            let vs = create_vsymbol ident_ret ty in
            let pat =
              List.mapi (fun k ty ->
                  if k = arg_index then pat_var vs
                  else pat_wild ty) constr_args in
            t_case t [t_close_branch (pat_app constr pat (t_type t)) (t_var vs)]
         | Some s -> t_app s [t] (Some ty)

  let get_subvalues t ity =
    let open Ty in
    let open Decl in
    let myty = t_type t in
    match myty.ty_node with
    | _ when ty_equal myty ty_bool -> []
    | _ when ty_equal myty ty_int -> [t, None]
    | Tyapp (ts, vars) -> begin
        let vars = ts_match_args ts vars in
        match (Ident.Mid.find ts.ts_name known_logical_ident).d_node with
        | Ddata ([_, [ls, ls_projs]]) ->
           let tl =
             let my_ls_args = List.map (ty_inst vars) ls.ls_args in
             let args_projs = List.combine my_ls_args ls_projs in
             let inst (arg_type, proj) = match proj with
               | Some ls ->
                  let ty = match ls.ls_value with
                    | Some t -> let ty = ty_inst vars t in
                                assert (ty_equal ty arg_type);
                                ty
                    | None -> assert false in
                  Some ls, ty
               | None -> None, arg_type in
             let inst_args = List.map inst args_projs in
             List.mapi (access_field ls my_ls_args t) inst_args in
           begin match ity with
           | None -> List.map (fun t -> t, None) tl
           | Some its ->
              let pdecl = Pdecl.((find_its_defn known_pdecl its).itd_fields) in
              List.combine tl (List.map (fun a -> Some a) pdecl)
           end
        | Ddata [_; _] ->
           warning_t "Multiple constructors is not supported in abstract \
                      interpretation." t; []
        | Ddata _ ->
           warning_t "Recursive types is not supported in abstract \
                      interpretation." t; []
        | Dtype _  ->
           (* This happens when a type is private or has an invariant:
            it can't be accesed by the logic, so we give up and only
            look for projections by looking at program projections. *)
           begin try
               let open Ity in
               let open Expr in
               let its = restore_its ts in
               Opt.iter (fun its2 -> assert (its_equal its its2)) ity;
               let rsl = Pdecl.((find_its_defn known_pdecl its).itd_fields) in
               let inst_rs rs =
                 let ls = match (rs.rs_logic) with
                   | RLls ls -> ls
                   | _ -> assert false in
                 let this_ty = ty_of_ity rs.rs_cty.cty_result in
                 let ty = ty_inst vars this_ty in
                 t_app ls [t] (Some ty), Opt.map (fun _ -> rs) ity
               in List.map inst_rs rsl
             with Not_found -> failwith "could not restore its"
           end
        | Dind _ ->
           warning_t "Could not find type declaration (got inductive \
                      predicate)."
             t; []
        | Dlogic _ ->
           warning_t "Could not find type declaration (got logic \
                      declaration)."
             t; []
        | Dprop _ ->
           warning_t "Could not find type declaration (got propsition) \
                      for: "
             t; []
        | Dparam _ ->
           warning_t "Could not find type declaration (got param)."
             t; []
      end
    | Tyvar _ ->
       warning_t "Comparison of values with an abstract type, the \
                  interpretation will not be precise" t; []

  exception Bad_domain of Dom.t

  let rec extract_term (man, uf_man) is_in (dom_t, uf_t) v =
    let find_var v =
      try let candidate = Hashtbl.find uf_man.variable_mapping v in
          if is_in candidate then raise Not_found else candidate
      with Not_found ->
        try TermToVar.to_term uf_t.uf_to_var v
        with Not_found ->
          raise (Bad_domain (Dom.forget_array man dom_t [|v|] false)) in
    match Dom.get_linexpr man dom_t v with
    | Some x -> begin
        try let t = Ai_logic.varlist_to_term find_var x in
            assert (Ty.ty_equal (t_type t) Ty.ty_int); Some t
        with Bad_domain dom_t ->
          extract_term (man, uf_man) is_in (dom_t, uf_t) v
      end
    | None -> None

  let to_term (man, uf_man) (dom_t, uf_t) =
    let find_var v =
      try Hashtbl.find uf_man.variable_mapping v with Not_found ->
        try TermToVar.to_term uf_t.uf_to_var v with Not_found ->
          Format.eprintf "Couldn't find variable %s@." (Var.to_string v);
          raise Not_found in
    let t = Dom.to_term S.env (S.th_known, S.mod_known) man dom_t find_var in
    Union_find.fold_class (fun t uf1 uf2 ->
        let t1 = TermToClass.to_term uf_man.class_to_term uf1 in
        let t2 = TermToClass.to_term uf_man.class_to_term uf2 in
        t_and t (t_equ t1 t2)) t uf_t.classes


  (* Get a set of (apron) linear expressions from a constraint stated
     in why3 logic. *)
  (* The resulting list of linear expressions is weaker than the
     original why3 formula.  In the most imprecise case, it returns an
     empty list.  *)
  let meet_term: man -> term -> (t -> t) =
    let meetid = ref 0 in
    fun (man, uf_man) t ->
      incr meetid;
      (* First inline everything, for instance needed for references
         where !i is (!) i and must be replaced by (contents i) *)
      let t = t_inline_all t in
      (* Let's try to remove the nots that we can *)
      let t = t_push_negation t in
      let var_of_term t =
        try Some (Mterm.find t uf_man.apron_mapping)
        with Not_found -> None in

      (* Assuming that t is an arithmetic term, this computes the
         number of ocurrence of variables ando the constant of the
         arithmetic expression.  It returns (variables, constant) *)
      (* For instance, 4 + x + y set cst to 4, and constr to [(x, 1),
         (y, 1)] *)
      let rec term_to_var_list rud coeff t =
        let open Number in
        match t.t_node with
        | Tvar _ -> begin
            match var_of_term t with
            | Some var -> ([(var, coeff)], 0)
            | None -> Format.eprintf "Variable undefined: %a@."
                        Pretty.print_term t; failwith "undefined var" end
        | Tconst (Constant.ConstInt n) ->
          ([], coeff * BigInt.to_int n.il_int)
        | Tapp (ls, args) when ls_equal ls ad_int ->
          List.fold_left (fun (acc_vars, acc_cons) t ->
              let vars, cons = term_to_var_list rud coeff t in
              (acc_vars @ vars, acc_cons + cons)) ([], 0) args
        | Tapp (ls, [t1;t2]) when ls_equal ls min_int ->
          let vars1, cons1 = term_to_var_list rud coeff t1 in
          let vars2, cons2 = term_to_var_list rud (-coeff) t2 in
          (vars1 @ vars2, cons1 + cons2)
        | Tapp (ls, [t]) when ls_equal ls min_u_int ->
          term_to_var_list rud (-coeff)  t;
        | Tapp (ls, [{t_node = Tconst (Constant.ConstInt n)}; t])
        | Tapp (ls, [t; {t_node = Tconst (Constant.ConstInt n)}])
             when ls_equal ls mult_int ->
           term_to_var_list rud (BigInt.to_int n.il_int * coeff) t
        | _ -> (* maybe a record access *)
          begin
            match var_of_term t with
            | None -> begin
                try
                  let myvar = get_var_for_term uf_man rud t in
                  let cl = get_class_for_term uf_man t in
                  let classes = Union_find.union cl cl !rud.classes in
                  rud := { !rud with classes };
                  ([myvar, coeff], 0)
                with Not_found ->
                  Format.eprintf "REACHED END OF THE POOL@.@.@.@.@.";
                  raise (Not_handled t)
              end
            | Some s -> ([s, coeff], 0)
          end
      in

      (* This takes an epsilon-free formula and returns a list of linear
         expressions weaker than the original formula. *)
      let rec abstract t =
        let is_int_comp ls t =
          Ty.ty_equal (t_type t) Ty.ty_int &&
            (ls_equal ps_equ ls || ls_equal lt_int ls ||
             ls_equal gt_int ls || ls_equal le_int ls ||
             ls_equal ge_int ls) in
        try
          match t.t_node with
          | Tbinop (Tand, t1, t2) ->
            let f1 = abstract t1 in
            let f2 = abstract t2 in
            (fun (dom, uf) -> f2 (f1 (dom, uf)))
          | Tbinop (Tor, t1, t2) ->
            let f1 = abstract t1 in
            let f2 = abstract t2 in
            (fun (d, a) ->
               let dom_uf1 = f1 (d, a) in
               let dom_uf2 = f2 (d, a) in
               join (man, uf_man) dom_uf1 dom_uf2)
          | Tapp (func, [t1; t2]) when is_int_comp func t1 ->
            (* FIXME: >, <=, >=, booleans *)
            let base_coeff, eq_type =
              if      ls_equal ps_equ func then  1, Lincons1.EQ
              else if ls_equal lt_int func then  1, Lincons1.SUP
              else if ls_equal gt_int func then -1, Lincons1.SUP
              else if ls_equal le_int func then  1, Lincons1.SUPEQ
              else if ls_equal ge_int func then -1, Lincons1.SUPEQ
              else assert false in
            (fun (dom, uf) ->
              let eqf =
                if ls_equal ps_equ func then do_eq (man, uf_man) t1 t2
                else fun_id in
               let dom, uf = eqf (dom, uf) in
               let ruf = ref uf in
               let vl1, c1 = term_to_var_list ruf (-base_coeff) t1 in
               let vl2, c2 = term_to_var_list ruf base_coeff t2 in
               let uf' = !ruf in
               let coef = c1 + c2 in
               let v = sum_list (vl1 @ vl2) in
               let expr = Linexpr1.make uf_man.env in
               let constr = List.map (fun (var, coeff) ->
                   Coeff.Scalar (Scalar.of_int coeff), var) v in
               Linexpr1.set_list expr constr None;
               let cons = Lincons1.make expr eq_type in
               Lincons1.set_cst cons (Coeff.Scalar (Scalar.of_int coef));
               let arr = Lincons1.array_make uf_man.env 1 in
               Lincons1.array_set arr 0 cons;
               Dom.meet_lincons_array man dom arr, uf')
          | Tapp (func, [t1;t2]) when ls_equal ps_equ func ->
            let f_uf = do_eq (man, uf_man) t1 t2 in
            let subv_1 = get_subvalues t1 None in
            let subv_2 = get_subvalues t2 None in
            List.fold_left (fun acc_f ((t1, _), (t2, _)) ->
                let f_eq = abstract (t_app ps_equ [t1; t2] None) in
                (fun abs -> acc_f (f_eq abs)))
              f_uf (List.combine subv_1 subv_2)
          | Tif (t1, t2, t3) ->
            let f1 = abstract t1 in
            let f1_not = abstract (t_push_negation (t_not t1)) in
            let f2 = abstract t2 in
            let f3= abstract t3 in
            (fun abs ->
               let dom2 = f2 (f1 abs) in
               let dom3 = f3 (f1_not abs) in
               join (man, uf_man) dom2 dom3)
          | Ttrue -> fun_id
          | _ when t_equal t t_bool_true || t_equal t t_true -> fun_id
          | Tfalse -> (fun _ -> Dom.bottom man uf_man.env, empty_uf_domain)
          | _ when t_equal t t_bool_false || t_equal t t_false ->
             (fun _ -> Dom.bottom man uf_man.env, empty_uf_domain)
          | _ -> raise (Not_handled t)
        with Not_handled t ->
          Format.eprintf "Couldn't understand entirely the post condition: %a@."
            Pretty.print_term t;
          fun_id
      in (fun d -> abstract t d)

  let is_leq (man, uf_man) (dom_t1, uf_t1) (dom_t2, uf_t2) =
    let dom, _ = join_uf (man, uf_man) uf_t1 uf_t2 dom_t2 in
    let dom = Dom.is_leq man dom_t1 dom in
    let uf  = Union_find.is_leq uf_t1.classes uf_t2.classes in
    dom && uf

  let var_id = ref 0

  let ensure_variable uf_man v t =
    if not (Environment.mem_var uf_man.env v) then
      begin
        Hashtbl.add uf_man.variable_mapping v t;
        uf_man.env <- Environment.add uf_man.env [|v|] [||]
      end

  let add_lvariable_to_env (_, uf_man) vs =
    incr var_id;
    let open Ty in
    let t = t_var vs in
    try ignore (Mterm.find t uf_man.defined_terms) with Not_found ->
      uf_man.defined_terms <- Mterm.add t () uf_man.defined_terms;
      if Ty.ty_equal (t_type t) ty_int then begin
          let reg_name =
            Format.asprintf "%d%a" !var_id Pretty.print_term t in
          let v = Var.of_string reg_name in
          assert (not (Environment.mem_var uf_man.env v));
          ensure_variable uf_man v t;
          uf_man.apron_mapping <- Mterm.add t v uf_man.apron_mapping
        end
      else if Ty.ty_equal (t_type t) ty_bool then begin
          let reg_name =
            Format.asprintf "%d%a" !var_id Pretty.print_term t in
          let v = Var.of_string reg_name in
          assert (not (Environment.mem_var uf_man.env v));
          ensure_variable uf_man v t;
          uf_man.apron_mapping <- Mterm.add t v uf_man.apron_mapping;
        end
      else
        let subv = get_subvalues t None in
        let name_var t1 t2 =
          Format.asprintf "%d%a.%a"
            !var_id Pretty.print_term t1 Pretty.print_term t2 in
        List.iter (fun (t2, _) ->
          let v = Var.of_string (name_var t t2) in
          ensure_variable uf_man v t2;
          uf_man.apron_mapping <- Mterm.add t2 v uf_man.apron_mapping) subv

  let cached_vreturn = ref (Ty.Mty.empty)

  let ident_ret =
    Ident.{pre_name  = "$reg";
           pre_attrs = Ident.Sattr.empty;
           pre_loc   = None; }

  let create_vreturn man ty =
    assert (not (Ty.ty_equal ty Ity.ty_unit));
    try Ty.Mty.find ty !cached_vreturn with Not_found ->
      let v  = create_vsymbol ident_ret ty in
      add_lvariable_to_env man v;
      cached_vreturn := Ty.Mty.add ty v !cached_vreturn;
      v

  let add_variable_to_env (man, uf_man) pv =
    incr var_id;
    let open Expr in
    let open Ty in
    let open Ity in
    let open Pretty in
    let pv_t = t_var pv.pv_vs in
    match pv.pv_ity.ity_node, (t_type pv_t).ty_node with
    | _ when Ty.ty_equal (t_type pv_t) ty_int ->
      let reg_name =
        Format.asprintf "%d%a" !var_id print_term pv_t in
      let v = Var.of_string reg_name in
      assert (not (Environment.mem_var uf_man.env v));
      ensure_variable uf_man v pv_t;
      uf_man.apron_mapping <- Mterm.add pv_t v uf_man.apron_mapping
    | _ when Ty.ty_equal (t_type pv_t) ty_bool ->
      let reg_name = Format.asprintf "%d%a" !var_id print_term pv_t in
      let v = Var.of_string reg_name in
      assert (not (Environment.mem_var uf_man.env v));
      ensure_variable uf_man v pv_t;
      uf_man.apron_mapping <- Mterm.add pv_t v uf_man.apron_mapping;
    | _ when ity_equal pv.pv_ity Ity.ity_unit-> ()
    | Ityreg reg, Tyapp _ -> begin
        let vret = create_vreturn (man, uf_man) (t_type pv_t) in
        let subv = get_subvalues (t_var vret) (Some reg.reg_its) in
        let subv_r = get_subvalues pv_t (Some reg.reg_its) in
        let proj_list =
          List.fold_left2 (fun acc (gen_reg_t, pfield) (real_term, _) ->
            let name = Format.asprintf "r$%a.%a" print_reg_name reg
                         print_term gen_reg_t in
            let var = Var.of_string name in
            ensure_variable uf_man var real_term;
            uf_man.apron_mapping <-
              Mterm.add real_term var uf_man.apron_mapping;
            let accessor = Opt.get (Opt.get pfield).rs_field in
            (accessor, real_term) :: acc ) [] subv subv_r in
        let old_projs, old_vars =
          try Mreg.find reg uf_man.region_mapping,
              Mreg.find reg uf_man.region_var
          with Not_found -> [], [] in
        uf_man.region_mapping <-
          Mreg.add reg (proj_list @ old_projs) uf_man.region_mapping;
        uf_man.region_var <-
          Mreg.add reg (pv.pv_vs :: old_vars) uf_man.region_var
      end
    | Ityapp _, _ ->
      let subv = get_subvalues pv_t None in
      List.iter (fun (t, _) ->
          let name = Format.asprintf "%d%a.%a" !var_id
                       print_pv pv print_term t in
          let var = Var.of_string name in
          ensure_variable uf_man var t;
          uf_man.apron_mapping <- Mterm.add t var uf_man.apron_mapping) subv
    | _ ->
       Format.eprintf "Variable of type %a could not be added properly: %a@."
         print_ity pv.pv_ity print_term pv_t

  let is_in t1 t2 =
    let found = ref false in
    let rec is_in t =
      if t_equal t1 t then found := true;
      t_map is_in t in
    ignore (is_in t2);
    !found

  let rec tdepth t = 1 + t_fold (fun i t -> max (tdepth t) i) 0 t

  let rec forget_term (man, uf_man) t =
    let forget_fun (dom_t, uf_t) =
      let dom_t, uf_t =
        try
          let var = Mterm.find t uf_man.apron_mapping in
          let dom_t, uf_t =
            match extract_term (man, uf_man) (is_in t) (dom_t, uf_t) var with
            | Some t2 -> do_eq (man, uf_man) t t2 (dom_t, uf_t)
            | None -> dom_t, uf_t in
          Dom.forget_array man dom_t [|var|] false, uf_t
        with Not_found -> dom_t, uf_t in
      let (dom_t, uf_t), alt =
        try
          let t_class = get_class_for_term uf_man t in
          let classes = Union_find.get_class t_class uf_t.classes in
          let class2term = TermToClass.to_term uf_man.class_to_term in
          let tl = List.map class2term classes in
          let term = List.find (fun t2 -> not (is_in t t2)) tl in
          do_eq (man, uf_man) term t (dom_t, uf_t), Some term
        with Not_found -> (dom_t, uf_t), None in
      let all_values = Union_find.flat uf_t.classes in
      let all_values = List.map (fun c ->
          c, TermToClass.to_term uf_man.class_to_term c) all_values in
      let all_values =
          (get_class_for_term uf_man t, t) ::
          List.filter (fun (_, a) ->
              is_in t a && not (t_equal t a) ) all_values in
      let int_values, other_values =
        List.partition (fun (_, t) ->
            Ty.ty_equal (t_type t) Ty.ty_int) all_values in
      let uf_t = List.fold_left (fun uf_t (cl, _) ->
        let classes = snd (Union_find.forget cl uf_t.classes) in
        { uf_t with classes} ) uf_t other_values in
      let forgot_var = t in
      let aux (dom_t1, uf_t1) (cl, t) =
        let old_cl = uf_t1.classes in
        let classes = snd (Union_find.forget cl uf_t1.classes) in
        let uf_t1 = { uf_t1 with classes } in
        try
          let apron_var = TermToVar.to_t uf_t1.uf_to_var t in
          let uf_to_var = TermToVar.remove_term uf_t1.uf_to_var t in
          try
            let alt_cl = Union_find.get_class cl old_cl in
            let alt_cl, classes = match alt with
              | Some alt ->
                 let new_t = replaceby forgot_var alt t in
                 let new_cl = get_class_for_term uf_man new_t in
                 new_cl :: alt_cl,
                 snd (Union_find.forget cl (Union_find.union cl new_cl old_cl))
              | None -> alt_cl, uf_t1.classes in
            let f c =
              if c <> cl then
                let t = TermToClass.to_term uf_man.class_to_term c in
                try TermToVar.to_t uf_t1.uf_to_var t |> ignore; None
                with Not_found -> if tdepth t < 4 then Some t else None
              else None in
            let alt_cl = List.map f alt_cl in
            let cl_t = List.find (function Some _ -> true | _ -> false) alt_cl in
            let alt_term = match cl_t with Some x -> x | _ -> assert false in
            let uf_to_var = TermToVar.add uf_to_var alt_term apron_var in
            dom_t1, { uf_t1 with uf_to_var; classes }
          with Not_found ->
            Dom.forget_array man dom_t1 [|apron_var|] false,
            { uf_t1 with var_pool = VarPool.add apron_var uf_t1.var_pool; uf_to_var }
        with Not_found ->  dom_t1, uf_t1 in
      List.fold_left aux (dom_t, uf_t) int_values in
    List.fold_left (fun abs (t2, _) ->
        if t_equal t2 t then abs
        else (fun d  -> abs (forget_term (man, uf_man) t2 d))
      ) forget_fun (get_subvalues t None)

  let forget_var m v = forget_term m (t_var v)

  let forget_region (man, uf_man) reg _ =
    let members = Ity.Mreg.find reg uf_man.region_mapping |> List.map snd in
    let vars = Ity.Mreg.find reg uf_man.region_var in
    let forget_fields = List.fold_left (fun forget t ->
        let forget_t = forget_term (man, uf_man) t in
        fun x -> forget x |> forget_t) fun_id members in
    List.fold_left (fun f v ->
        fun (d, ud) ->
          let acl = get_class_for_term uf_man (t_var v) in
          let ud = { ud with classes = snd (Union_find.forget acl ud.classes) } in
          f (d, ud)) forget_fields vars

  let widening (man, uf_man) (dom_t1, uf_t1) (dom_t2, uf_t2) =
    let dom, uf = join_uf (man, uf_man) uf_t1 uf_t2 dom_t2 in
    let dom = Dom.widening man dom_t1 dom in
    dom, uf

  let is_join_precise (man, uf_man) (dom_t1, uf_t1) (dom_t2, uf_t2) =
    let dom, uf = join_uf (man, uf_man) uf_t1 uf_t2 dom_t2 in
    match Dom.is_join_precise man dom_t1 dom with
    | None -> None
    | Some dom -> Some (dom, uf)

  let make_consistent _ a b = a, b

end
