(*  Title:      derivation.ML
    Author:     Joshua Chen

Management and automation of type derivation, and setup of soft type interface.

*)

structure Derivation =
struct

(*** Tracing ***)

val debug = Attrib.setup_config_bool \<^binding>\<open>derivation_debugger\<close> (K false)

fun warn ctxt msg = if Config.get ctxt debug then warning msg else ()


(*** Context data ***)

(** Derivation rules **)

(*
  A type derivation rule is an implication whose premises and conclusion are
  typing or adjective judgments ("judgments").

  These are stored in normalized form: premises are broken up into atomic type
  or adjective judgments, and the conclusion is also split to yield multiple
  rules whose premises are the same and whose conclusions are the atomic
  components of the original.
*)

fun get_derivation_rules ctxt =
  Named_Theorems.get ctxt \<^named_theorems>\<open>derivation_rules\<close>

fun put_derivation_rule thm context =
  context |> (fold
    (Named_Theorems.add_thm \<^named_theorems>\<open>derivation_rules\<close>)
    (Soft_Type_Context.normalize (Context.proof_of context) thm))


(** Opaque terms **)

(*
  Type derivation takes all subterms of the goal state and generates type
  judgments for them. Sometimes we may want particular terms to be opaque, i.e.
  to prevent them from being considered by the type derivator.
*)

structure Opaque_Terms = Generic_Data (
  type T = term Item_Net.T
  val empty = Item_Net.init Term.aconv single
  val extend = I
  val merge = Item_Net.merge
)

fun get_opaque_terms ctxt = Opaque_Terms.get (Context.Proof ctxt)
fun put_opaque_terms tms =
  Opaque_Terms.map (foldl1 (op o) (map Item_Net.update tms))

val _ = (
  Outer_Syntax.local_theory \<^command_keyword>\<open>opaque\<close> "declare opaque terms"
    let
      val parser = Scan.repeat Parse.term
    in
      (parser >> (fn tms => fn lthy => lthy |>
        Local_Theory.background_theory (Context.theory_map
          (put_opaque_terms (Syntax.read_terms lthy tms)))))
    end;

  Outer_Syntax.command \<^command_keyword>\<open>print_opaque_terms\<close>
    "print opaque terms of the proof context or local theory"
    let
      fun pretty_terms ctxt =
        Item_Net.content (get_opaque_terms ctxt)
        |> map (Proof_Display.pp_term (K (Proof_Context.theory_of ctxt)))
        |> Pretty.chunks
    in
      (Scan.succeed
        (Toplevel.keep (Pretty.writeln o pretty_terms o Toplevel.context_of)))
    end
)


(*** Type derivation ***)

val derive_depth = Attrib.setup_config_int \<^binding>\<open>derivation_depth\<close> (K 10)

fun term_jdgmts_from_rule ctxt tm jdgmts rule =
  let
    fun discharge_prems thms =
      let
        val in_jdgmts = member Thm.eq_thm_prop jdgmts
      in
        (*Invariant: every theorem in thms has the same number of premises*)
        case thms |> filter_out in_jdgmts of
          [] => []
        | thms as thm :: _ =>
            if Thm.no_prems thm then thms
            else discharge_prems (jdgmts RLN (Thm.nprems_of thm, thms))
      end
  in
    let
      val inst =
        ((Soft_Type.term_of_jdgmt o Thm.concl_of) rule, tm)
        |> apply2 (Thm.cterm_of ctxt)
        |> Thm.match
    in
      discharge_prems [Thm.instantiate inst rule]
    end
    handle Pattern.MATCH => []
  end

(*
  Derive judgments for a set of terms from a set of judgments using a set of
  rules. All derived judgments are atomic since the derivation rules are
  normalized. The returned results include judgments already in the context.
*)
fun derive_jdgmts ctxt tms jdgmts rules =
  let
    fun derive_jdgmts' jdgmts iter =
      if iter > Config.get ctxt derive_depth
      then
        (warning
          ("Type derivation depth limit reached; " ^
          "consider increasing derivation_depth");
        jdgmts)
      else
        let
          fun derive_new_jdgmts tm =
            map (term_jdgmts_from_rule ctxt tm jdgmts) rules
            |> flat
            |> distinct Thm.eq_thm_prop

          val new_jdgmts = flat (map derive_new_jdgmts tms)
        in
          if null new_jdgmts
          then jdgmts
          else derive_jdgmts' (jdgmts @ new_jdgmts) (iter + 1)
        end
  in
    derive_jdgmts' jdgmts 0
  end


(*** Soft type setup ***)

(** Further processing of type judgments **)

(*
  Convert typing judgments
    "f : T1 \<Rightarrow> ... \<Rightarrow> Tn \<Rightarrow> T"
  to type derivation rules
    "x1 : T1 \<Longrightarrow> ... \<Longrightarrow> xn : Tn \<Longrightarrow> f x1 ... xn : T"
*)
fun Pi_derivation_rule thm =
  case Soft_Type.type_of_typing (Thm.concl_of thm) of
    Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ _ =>
      Pi_derivation_rule (thm RS @{thm Pi_typeE})
  | _ => thm


(** The [derive] attribute **)

(*Register type derivation rules and subtyping rules*)
val derivation_rule_parser: attribute context_parser =
  Scan.lift (Scan.succeed (Thm.declaration_attribute put_derivation_rule))


(** The [type] attribute **)

(*
  May optionally declare some number of implicit arguments for constant terms
  via `[type implicit: n]`.
*)
fun extract_param_names 0 _ = []
  | extract_param_names i (Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ Abs (n, _, b)) =
      n :: extract_param_names (i - 1) b
  | extract_param_names i _ = replicate i ""

fun declare_current_type implicit thm context =
  let
    val (x, st) = Soft_Type.dest_typing (Thm.prop_of thm)
    val names = extract_param_names (the_default 0 implicit) st
    val handle_Pi = put_derivation_rule (Pi_derivation_rule thm)
  in
    context
    |> Soft_Type_Context.put_current_type x thm
    |> Soft_Type_Context.put_type x thm
    |> (if is_Const x
        then Implicit_Arguments.put_implicit (fst (dest_Const x)) names
        else I)
    |> (if Soft_Type.is_Pi st then handle_Pi else I)
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>type\<close>
  (Scan.lift (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int)
    >> (fn implicit => Thm.declaration_attribute (declare_current_type implicit))))
  "Declare current soft type")


(*** Tactics ***)

(** Single step discharge; works on the first subgoal **)

fun raw_discharge_type_tac add_facts add_tms =
  Subgoal.FOCUS_PREMS (fn {context = goal_ctxt, prems, concl, ...} =>
    let
      val concl_tm = Thm.term_of concl
    in
      if Soft_Type.is_jdgmt concl_tm
      then
        let
          fun is_derivation_rule thm =
            Soft_Type.is_typing (Thm.concl_of thm)
            andalso not (Thm.no_prems thm)
            andalso forall Soft_Type.is_jdgmt (Thm.prems_of thm)

          fun add_to_context prem context =
            let
              val prop = Thm.prop_of prem
            in
              if Soft_Type.is_typing prop then
                (if Soft_Type.is_Pi (Soft_Type.type_of_typing prop)
                then put_derivation_rule (Pi_derivation_rule prem) context
                else context)
                |> Soft_Type_Context.put_type (Soft_Type.term_of_typing prop) prem
              else if Soft_Type.is_adj prop then
                Soft_Type_Context.put_adj (Soft_Type.term_of_jdgmt prop) prem context
              else if is_derivation_rule prem then
                put_derivation_rule prem context
              else context
            end

          val goal_ctxt' =
            goal_ctxt
            |> Context.proof_map (fold add_to_context
              (map (Soft_Type.eta_norm goal_ctxt) (add_facts @ prems)))

          fun typable_subterms tm =
            let
              val is_opaque = Item_Net.member (get_opaque_terms goal_ctxt)

              val res =
                if Term.is_open tm orelse is_opaque tm
                then [] else [tm]
            in
              distinct Term.aconv (
                res @ (case tm of
                  t1 $ t2 =>
                    if is_opaque t1
                    then []
                    else typable_subterms t1 @ typable_subterms t2
                | Abs (_, _, t) => typable_subterms t
                | Free _ => [tm]
                | _ => []
                ))
            end

          val tm = Soft_Type.term_of_jdgmt concl_tm
          val tms =
            distinct Term.aconv (
              typable_subterms tm
              @ flat (map typable_subterms add_tms))

          val jdgmts =
            Soft_Type_Context.get_types goal_ctxt' tms
            @ Soft_Type_Context.get_adjs goal_ctxt' tms
            @ Soft_Type_Context.univ_types goal_ctxt'
            @ Soft_Type_Context.univ_adjs goal_ctxt'

          val rules = get_derivation_rules goal_ctxt'
          val jdgmts' = derive_jdgmts goal_ctxt' tms jdgmts rules

          val str_of_tm = Syntax.string_of_term goal_ctxt'
          fun itemize strs = "  " ^ space_implode "\n  " strs

          val _ =
            Soft_Type.tracing goal_ctxt' (cat_lines (
              [">> Goal conclusion:\n  " ^ str_of_tm concl_tm,
              "\n>> Starting from subterms:\n" ^
                (itemize (map str_of_tm (typable_subterms tm))),
              "and additional terms:\n" ^
                (itemize (map str_of_tm (flat (map typable_subterms add_tms)))),
              "and known judgments:\n" ^
                (itemize (map (str_of_tm o Thm.prop_of) jdgmts)),
              (* "using derivation rules:\n  " ^
                (itemize (map (str_of_tm o Thm.prop_of) rules)), *)
              "\n>> Derived judgments:\n" ^
                (itemize (map (str_of_tm o Thm.prop_of) jdgmts'))]))
        in
          case
            filter (fn th => Term.could_unify (concl_tm, Thm.prop_of th)) jdgmts'
          of
            [] => (Soft_Type.tracing goal_ctxt' ">> No unifier!\n"; no_tac)
          | ths =>
              (Soft_Type.tracing goal_ctxt'
                (itemize (map (str_of_tm o Thm.prop_of) ths));
              HEADGOAL
                (foldl1
                  (op APPEND')
                  (map (fn th => resolve_tac goal_ctxt' [th]) ths)))
        end
      else (Soft_Type.tracing goal_ctxt ">> Not a judgment!\n"; no_tac)
    end)


(** Fully automated type derivation and discharge **)

fun full_discharge_types_tac add_facts add_tms ctxt =
  let
    val discharge_tac =
      SUBGOAL (fn _ => ALLGOALS (TRY o (
        (* (TRY o (EqSubst.eqsubst_tac ctxt [0] [@{thm eta_contract_eq}])) THEN' *)
        raw_discharge_type_tac add_facts add_tms ctxt)))

    val refine_tac = REPEAT o (resolve_tac ctxt [@{thm Int_typeI}, @{thm has_type_adjI}])

    val backward_tac = resolve_tac ctxt
      (Named_Theorems.get ctxt \<^named_theorems>\<open>backderivation_rules\<close>)
  in
    (TRY o refine_tac) THEN' (
      (CHANGED o discharge_tac) ORELSE' (backward_tac THEN' discharge_tac)
    )
  end


end
