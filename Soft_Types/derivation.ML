(*  Title:      derivation.ML
    Author:     Joshua Chen

Management and automation of type derivation, and setup of soft type interface.

*)

structure Derivation =
struct

(*** Tracing ***)

val derive_debug = Attrib.setup_config_bool \<^binding>\<open>derive_debug\<close> (K false)

fun warn ctxt msg = if Config.get ctxt derive_debug then warning msg else ()


(*** Context data ***)
(*
  A type derivation rule is an implication whose premises and conclusion are typing or
  adjective judgments ("judgments").

  These are stored in normalized form: premises are broken up into atomic type/adjective
  judgments, and the conclusion is also split to yield multiple rules whose premises are
  the same and whose conclusions are the atomic components of the original.
*)

fun get_derivation_rules ctxt = Named_Theorems.get ctxt \<^named_theorems>\<open>derivation_rules\<close>

fun put_derivation_rule ctxt =
  Soft_Type_Context.normalize ctxt
  #> fold (Named_Theorems.add_thm \<^named_theorems>\<open>derivation_rules\<close>)

val put_subtype_rule = Named_Theorems.add_thm \<^named_theorems>\<open>subtype_rules\<close>


(*** Type derivation ***)

val derive_depth = Attrib.setup_config_int \<^binding>\<open>derive_depth\<close> (K 10)

fun term_jdgmts_from_rule ctxt tm jdgmts rule =
  let
    fun in_jdgmts thm =
      subset Term.aconv
        (map Thm.concl_of (Soft_Type_Context.normalize ctxt thm), map Thm.prop_of jdgmts)

    fun discharge_prems thms = case thms |> filter_out in_jdgmts of
        [] => []
      | thms as thm :: _ =>
          if Thm.no_prems thm then thms
          else discharge_prems (jdgmts RLN (Thm.nprems_of thm, thms))
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
  Derive judgments for a set of terms from a set of judgments using a set of rules.
  All derived judgments are atomic since the derivation rules are normalized.
  The returned results include judgments already in the context.
*)
fun derive_jdgmts ctxt tms jdgmts rules =
  let
    fun derive_jdgmts' jdgmts iter =
      if iter > Config.get ctxt derive_depth
      then
        (warning "Type derivation depth limit reached; consider increasing derive_depth";
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
  Convert "f : T1 \<Rightarrow> ... \<Rightarrow> Tn \<Rightarrow> T" to "x1 : T1 \<Longrightarrow> ... \<Longrightarrow> xn : Tn \<Longrightarrow> f x1 ... xn : T".
*)
fun Pi_derivation_rule thm = case Soft_Type.type_of_typing (Thm.concl_of thm) of
    Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ _ => Pi_derivation_rule (thm RS @{thm Pi_typeE})
  | _ => thm

(*
  Convert "T \<prec> S" to "x : T \<Longrightarrow> x : S".
*)
fun subtype_derivation_rule thm =
  thm RS @{thm subtypeE'}
  handle THM _ => error "subtype_derivation_rule: not a subtype judgment"


(** The [derive] attribute **)
(*
  Used to register type derivation rules and subtyping rules.
*)

val derivation_rule_parser =
  Attrib.add_del
    (Thm.declaration_attribute (fn thm => fn context =>
      if Soft_Type.is_subtyping (Thm.prop_of thm)
      then
        context
        |> put_subtype_rule thm
        |> put_derivation_rule (Context.proof_of context) (subtype_derivation_rule thm)
      else
        put_derivation_rule (Context.proof_of context) thm context))
    (Thm.declaration_attribute (fn _ =>
      (warning "Deletion of derivation rules not implemented"; I)))


(** The [type] attribute **)
(*
  May optionally declare some number of implicit arguments for constant terms via
  `[type implicit: n]`.
*)

fun extract_param_names 0 _ = []
  | extract_param_names i (Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ Abs (n, _, b)) =
      n :: extract_param_names (i - 1) b
  | extract_param_names i _ = replicate i ""

fun declare_current_type implicit thm context =
  let
    val (x, st) = Soft_Type.dest_typing (Thm.prop_of thm)
    val names = extract_param_names (the_default 0 implicit) st

    val handle_Pi = fn context =>
      put_derivation_rule (Context.proof_of context) (Pi_derivation_rule thm) context
  in
    context
    |> Soft_Type_Context.put_current_type x thm
    |> Soft_Type_Context.put_type x thm
    |> (if is_Const x then Implicit_Arguments.put_implicit (fst (dest_Const x)) names else I)
    |> (if Soft_Type.is_Pi st then handle_Pi else I)
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>type\<close>
  (Scan.lift
    (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int) >> (fn implicit =>
      Thm.declaration_attribute (declare_current_type implicit))))
  "Declare current soft type")


(*** Tactics ***)

fun discharge_type_tac ctxt add_tms = SUBGOAL (fn (_, i) =>
  TRY (REPEAT (resolve_tac ctxt [@{thm Int_typeI}, @{thm adjI}] i))
  THEN ALLGOALS (TRY o (Subgoal.FOCUS_PREMS
    (fn {context = goal_ctxt, prems, concl, ...} =>
      let val concl_tm = Thm.term_of concl in
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
                Soft_Type_Context.put_type (Soft_Type.term_of_typing prop) prem context
              else if Soft_Type.is_adj prop then
                Soft_Type_Context.put_adj (Soft_Type.term_of_jdgmt prop) prem context
              else if is_derivation_rule prem then
                put_derivation_rule (Context.proof_of context) prem context
              else context
            end

          val goal_ctxt' =
            Context.proof_of (fold add_to_context prems (Context.Proof goal_ctxt))

          fun typable_subterms tm =
            let
              val res = if Term.is_open tm then [] else [tm]
            in
              res @ (case tm of
                t1 $ t2 => typable_subterms t1 @ typable_subterms t2
              | Abs (_, _, t) => typable_subterms t
              | Var _ => [tm]
              | _ => []
              )
            end

          val tm = Soft_Type.term_of_jdgmt concl_tm
          val tms = (typable_subterms tm @ flat (map typable_subterms add_tms))

          val jdgmts =
            Soft_Type_Context.get_types goal_ctxt' tms
            @ Soft_Type_Context.get_adjs goal_ctxt' tms
            @ Soft_Type_Context.univ_types goal_ctxt'
            @ Soft_Type_Context.univ_adjs goal_ctxt'

          val rules = get_derivation_rules goal_ctxt'
          val jdgmts' = derive_jdgmts goal_ctxt' tms jdgmts rules

          val str_of_tm = Syntax.string_of_term goal_ctxt'
          val itemize = space_implode "\n  "
          val _ =
            Soft_Type.tracing goal_ctxt' (cat_lines (
              ["Proving judgment:\n  " ^ str_of_tm concl_tm,
              "with subterms:\n  " ^
                (itemize (map str_of_tm (typable_subterms tm))),
              "and additional terms:\n  " ^
                (itemize (map str_of_tm (flat (map typable_subterms add_tms)))),
              "beginning with judgments:\n  " ^
                (itemize (map (str_of_tm o Thm.prop_of) jdgmts)),
              "using derivation rules:\n  " ^
                (itemize (map (str_of_tm o Thm.prop_of) rules)),
              "derived judgments:\n  " ^
                (itemize (map (str_of_tm o Thm.prop_of) jdgmts'))]))
        in
          case find_first (fn th => Term.could_unify (concl_tm, Thm.prop_of th)) jdgmts'
          of
            NONE => (warning "No unifier"; no_tac)
          | SOME th => resolve_tac goal_ctxt' [th] i
        end
      else (warning "Not a judgment"; no_tac)
    end) ctxt)))


end
