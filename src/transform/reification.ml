open Term
open Ty
open Decl
open Theory

let meta_reify_target = Theory.register_meta_excl "reify_target" [Theory.MTlsymbol]
    ~desc:"Declares@ the@ given@ type@ as@ target@ for@ reification,@ with@ its@ interpretation@ function." (*FIXME desc*)

(*let meta_reify_invert = Theory.register_meta "reify_invert" [Theory.MTlsymbol]
   ~desc:"Declares@ that@ the@ given@ interpretation@ function@ can@ be@ inverted@ during@ the@ reification."*)

(* target: t = V int | ...
   interp: t -> (int -> 'a) -> 'a *)


let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
  | a1::l1, a2::l2, a3::l3 -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | [], [], [] -> accu
  | _ -> raise (Invalid_argument "fold_left3")


let collect_reify_targets_t =
  Trans.on_meta_excl meta_reify_target
                     (function
                      | None -> raise Exit
                      | Some [Theory.MAls i]
                        -> Trans.return i
                      | _ -> assert false)

exception Exit

let debug = false

let reify_goal interp task =
  let kn = Task.task_known task in
  let ty_vars, ty_val = match interp.ls_args, interp.ls_value with
    | [ _ty_target; ty_vars ], Some ty_val
         when ty_equal ty_vars (ty_func ty_int ty_val)
      -> ty_vars, ty_val
    | _ -> raise Exit in
  let ly = create_fsymbol (Ident.id_fresh "y") [] ty_vars in
  let y = t_app ly [] (Some ty_vars) in
  let rec invert_pat vl (env, fr) (p,f) t =
    if debug
    then Format.printf "invert_pat p %a f %a t %a@."
                       Pretty.print_pat p Pretty.print_term f Pretty.print_term t;
    match p.pat_node, f.t_node, t.t_node with
    | Pwild, _, _ -> raise Exit
    | Papp (cs, [{pat_node = Pvar v1}]),
      Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}]),
      Tvar _
    | Papp (cs, [{pat_node = Pvar v1}]),
      Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}]),
      Tapp(_, [])
         when ty_equal v1.vs_ty ty_int
              && Svs.mem v1 p.pat_vars
              && vs_equal v1 v2
              && ls_equal ffa fs_func_app
              && List.exists (fun vs -> vs_equal vs vy) vl (*FIXME*)
      ->
       if debug then Format.printf "case var@.";
       let rty = cs.ls_value in
       if Mterm.mem t env
       then
         begin
           if debug then Format.printf "%a exists@." Pretty.print_term t;
           (*(env,fr,t_app fs_func_app [yt; t_nat_const (Mvs.find v env)] rty) ???*)
           (env, fr, t_app cs [t_nat_const (Mterm.find t env)] rty)
         end
       else
         begin
           if debug then Format.printf "%a is new@." Pretty.print_term t;
           let env = Mterm.add t fr env in
           (env, fr+1, t_app cs [t_nat_const fr] rty)
         end
(*    | Papp (cs, [{pat_node = Pvar v1}]),
      Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}]), Tapp (ls, []) ->
       Format.printf "yes@."; raise Exit*)
    | Papp (cs, pl), Tapp(ls1, la1), Tapp(ls2, la2) when ls_equal ls1 ls2
      ->
       if debug then Format.printf "case app@.";
       (* same head symbol, match parameters *)
       let env, fr, rl =
         fold_left3
           (fun (env, fr, acc) p f t ->
             let env, fr, t = invert_pat vl (env, fr) (p, f) t in
             if debug then Format.printf "param matched@.";
             (env, fr, t::acc))
           (env, fr, []) pl la1 la2 in
       env, fr, t_app cs (List.rev rl) cs.ls_value
    | Papp _, Tapp (ls1, _), Tapp(ls2, _) ->
       if debug then Format.printf "head symbol mismatch %a %a@."
                                   Pretty.print_ls ls1 Pretty.print_ls ls2;
       raise Exit
    | Por (p1, p2), _, _ ->
       if debug then Format.printf "case or@.";
       begin try invert_pat vl (env, fr) (p1, f) t
             with Exit -> invert_pat vl (env, fr) (p2, f) t
       end
    | Pvar _, Tapp (ls, _la), _ when ls_equal ls interp
      -> if debug then Format.printf "case interp@.";
         invert_interp (env, fr) ls t
    (*| Papp (cs, pl), Tapp (ls1, la1), _ when Sls.mem ls1 !reify_invert
    -> (* Cst c -> morph c <- 42 ? *) *)
    | _ -> raise Exit

  (* interp x y <- t ? *)
  and invert_interp (env, fr) ls (t:term) = (*la ?*)
    let ld = Opt.get (find_logic_definition kn ls) in
    let vl, f = open_ls_defn ld in
    (*assert (oty_equal f.t_ty t.t_ty);*)
    if debug then Format.printf "invert_interp ls %a t %a@."
                                Pretty.print_ls ls Pretty.print_term t;
    match f.t_node, t.t_node with
    | Tcase (x, bl), _ ->
       (*FIXME*)
       assert (List.length vl = 2);
       (match x.t_node with Tvar v when vs_equal v (List.hd vl) -> () | _ -> assert false);
       if debug then Format.printf "case match@.";
       let rec aux = function
         | [] -> raise Exit
         | tb::l ->
            try invert_pat vl (env, fr) (t_open_branch tb) t
            with Exit -> if debug then Format.printf "match failed@.";aux l in
       aux bl
    | _ -> raise Exit
  in
  let rec reify_term (env, fr) (t:term) =
    if debug then Format.printf "reify_term %a@." Pretty.print_term t;
    match t.t_node with
    | Tapp(ls, [t1; t2]) when ls_equal ls ps_equ ->
       if debug then Format.printf "case =@.";
       let (env, fr, t1) = reify_term (env, fr) t1 in
       let (env, fr, t2) = reify_term (env, fr) t2 in
       env, fr, t_equ t1 t2
    | Tquant (Tforall, _) ->
       raise Exit (* we introduce premises before the transformation *)
    | _ -> (*FIXME*)
       ignore (oty_match Mtv.empty t.t_ty interp.ls_value);
       if debug then Format.printf "case interp@.";
       let env, fr, x = invert_interp (env, fr) interp t in
       env, fr, t_app interp [x; y] (Some ty_val)
    (*| _ ->
       if debug then
         Format.printf "wrong type: t.ty %a interp.ls_value %a@."
                       Pretty.print_ty (Opt.get t.t_ty)
                       Pretty.print_ty (Opt.get interp.ls_value);
       raise Exit*)
  in

  let open Task in
  match task with
  | Some
    { task_decl =
        { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
      task_prev = prev;
    } ->
     begin try
         if debug then Format.printf "start@.";
         let (env, _fr, t) = reify_term (Mterm.empty, 0) f in
         if debug then Format.printf "building y map@.";
         let d = create_param_decl ly in
         let prev = Task.add_decl prev d in
         let prev = Mterm.fold
                      (fun t i prev ->
                        let et = t_equ (t_app fs_func_app [y; t_nat_const i] (Some ty_val))
                                       t in
                        if debug then Format.printf "eq_term ok@.";
                        let pr = Decl.create_prsymbol (Ident.id_fresh "y_val") in
                        let d = Decl.create_prop_decl Paxiom pr et in
                        Task.add_decl prev d)
                      env prev in
         if debug then Format.printf "building goal@.";
         let d = Decl.create_prop_decl Pgoal pr t in
         Task.add_decl prev d
       with Exit -> task end
  | _ -> assert false


let reify_goal_t interp = Trans.store (reify_goal interp)

let reify_in_goal = (Trans.compose Introduction.introduce_premises
                          (Trans.bind collect_reify_targets_t reify_goal_t))
                                      
let () = Trans.register_transform
           "reify_in_goal"
           ~desc:"Reify@ goal@ to@ declared@ target@ datatype."
           reify_in_goal
(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)