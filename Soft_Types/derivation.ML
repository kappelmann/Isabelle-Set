(*  Title:      derivation.ML
    Author:     Joshua Chen

Management and automation of type derivation, and setup of soft type interface.

*)

structure Derivation =
struct

(*** Tracing ***)

val debug = Attrib.setup_config_bool \<^binding>\<open>type_derivation_debugger\<close> (K false)

fun trace ctxt msg = if Config.get ctxt debug then tracing msg else ()
fun warn ctxt msg = if Config.get ctxt debug then warning msg else ()


(*** Context data ***)

(** Derivation rules I **)

(*
  Type derivation rules are implications whose conclusions are typing or
  adjective judgments ("judgments"). There are two kinds of derivation rule:
  forward ("standard") derivation rules, and backward derivation
  ("backderivation") rules.

  Forward derivation rules are used in the saturation-based type derivation
  algorithm which, roughly speaking, only adds a type to the list of known types
  if there is a derivation rule whose premises can be immediately discharged
  from already-known type data. All rules whose premises are themselves
  judgments are valid forward derivation rules. They are stored in normalized
  form: premises are broken up into atomic type or adjective judgments, and the
  conclusion is also split to yield multiple rules whose premises are the same
  and whose conclusions are the atomic components of the original.

  Backderivation rules are applied backwards, yielding new proof obligations,
  and in theory may require all the power of general proof methods to derive
  their conclusions. Derivation rules whose premises are not simple type or
  adjective judgments, e.g the introduction rule for the Pi_type, are usually
  backward rules.

  Josh: Backderivation rules should be declared sparingly and with caution;
  I suspect that, besides the Pi type introduction rule, other non-forward
  derivation rules usually express non-trivial proof content which, for now, are
  better off handled with means other than the type derivator.
*)

fun get_backderivation_rules ctxt =
  Named_Theorems.get ctxt \<^named_theorems>\<open>backderivation_rules\<close>

val put_backderivation_rule =
  Named_Theorems.add_thm \<^named_theorems>\<open>backderivation_rules\<close>

fun get_derivation_rules ctxt =
  Named_Theorems.get ctxt \<^named_theorems>\<open>derivation_rules\<close>

(*val put_subtype_rule = Named_Theorems.add_thm \<^named_theorems>\<open>subtype_rules\<close>*)


(** Backderived types **)

(*
  Context data `Backderived_Types` stores types which have backward derivation
  rules.
*)

structure Backderived_Types = Generic_Data (
  type T = term Item_Net.T
  val empty = Item_Net.init Term.aconv (single o Term.head_of)
  val extend = I
  val merge = Item_Net.merge
)

fun get_bderived_types ctxt = Backderived_Types.get (Context.Proof ctxt)

fun put_bderived_type tm = (
  if is_Var tm
  then raise TERM (
    "put_bderived_type: backward derivation rule for schematic soft type", [tm])
  else ();
  Backderived_Types.map (Item_Net.update tm))


(** Derivation rules II **)

(*
  The backderived type data is used to automatically propagate the
  backderivation property to new derivation rules, roughly in the following
  manner[*]:

  If a derivation rule R of the form
    "p_1 \<Longrightarrow> ... \<Longrightarrow> p_k \<Longrightarrow> concl"
  has a simple premise
    p_i = s : S
  where S specializes (in the sense of unification) a type T with a known
  backderivation rule, then R should also be backderivation.

  [*]Modulo certain heuristics to prevent looping.

  Josh: I'm not sure how well the above actually performs; we need more case
  studies to experiment.
*)

(*Heuristics for when a rule should not be backderivation*)
fun prevent_backderivation context thm =
  let
    fun is_higher_order_schematic tm =
      case tm of
        Var (_, Type ("fun", _)) => true
      | _ => false
  in
    exists_subterm is_higher_order_schematic (Thm.concl_of thm)
  end

fun put_derivation_rule thm context =
  let
    val needs_backderivation =
      if prevent_backderivation context thm
      then false
      else
        let
          val prem_types = Thm.prems_of thm
            |> filter Soft_Type.is_typing
            |> map Soft_Type.type_of_typing
        in
          exists
            (fn S => exists
              (fn T => Soft_Type.specializes (S, T))
              (Item_Net.retrieve (Backderived_Types.get context) (Term.head_of S)))
            prem_types
        end

    (*Invariant: all thms in `rules` have the same premises*)
    val rules = Soft_Type_Context.normalize (Context.proof_of context) thm
  in
    context
    |> (fold (Named_Theorems.add_thm \<^named_theorems>\<open>derivation_rules\<close>) rules)
    |> (if needs_backderivation then fold put_backderivation_rule rules else I)
  end


(** Opaque terms **)

(*
  Type derivation takes all subterms appearing in the goal state and generates
  type judgments for them. Sometimes we may want particular terms to be opaque,
  i.e. to have them not be considered by the type derivator.
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


(** Soft type translation **)

(*Automatically convert certain predicates to type judgments*)

structure Soft_Type_Translation = Theory_Data (
  type T = (thm * thm) Termtab.table
  val empty = Termtab.empty
  val extend = I
  val merge =
    Termtab.merge
      (fn ((th1, th1'), (th2, th2')) =>
        Term.aconv (apply2 Thm.full_prop_of (th1, th2)) andalso
        Term.aconv (apply2 Thm.full_prop_of (th1', th2')))
)

fun put_translation pred trans_to trans_from =
  Soft_Type_Translation.map
    (Termtab.update_new (head_of pred, (trans_to, trans_from)))

fun get_forward_translation ctxt t =
  SOME (#1 (the (Termtab.lookup
    (Soft_Type_Translation.get (Proof_Context.theory_of ctxt))
    t)))
  handle Option => NONE

fun get_backward_translation ctxt t =
  SOME (#2 (the (Termtab.lookup
    (Soft_Type_Translation.get (Proof_Context.theory_of ctxt))
    t)))
  handle Option => NONE

fun get_translations ctxt =
  Termtab.dest (Soft_Type_Translation.get (Proof_Context.theory_of ctxt))

val get_forward_translations = (map (fst o snd)) o get_translations
val get_backward_translations = (map (snd o snd)) o get_translations

val _ = Outer_Syntax.command \<^command_keyword>\<open>soft_type_translation\<close>
  "declare automatic soft type translations"
  (Parse.term -- (Parse.$$$ "=" |-- Parse.term) >> (fn (pred, styp) =>
    Toplevel.theory_to_proof (fn thy =>
      let
        val ctxt = Proof_Context.init_global thy

        val (pred_tm, styp_tm) = apply2 (Syntax.read_term ctxt) (pred, styp)
        val (pred_tm', styp_tm') = apply2 Soft_Type.mk_Trueprop (pred_tm, styp_tm)
        val hd_const = head_of pred_tm

        val _ =
          if Termtab.defined (Soft_Type_Translation.get thy) hd_const
          then error ("Translation already declared for " ^
            Syntax.string_of_term ctxt hd_const)
          else ()

        fun after_qed [[trans_to], [trans_from]] =
              Proof_Context.background_theory
                (put_translation hd_const trans_to trans_from)
          | after_qed _ = raise ERROR "soft_type_translation: after_qed"

        val state = ctxt |> Proof.theorem NONE after_qed
          [ [(Logic.mk_implies (pred_tm', styp_tm'), [])],
            [(Logic.mk_implies (styp_tm', pred_tm'), [])] ]

        val _ = state
          |> Pretty.string_of o Pretty.chunks o Proof.pretty_state
          |> Output.state
      in
        state
      end)))


(*** Soft type setup ***)

(** Pi type declarations **)

(*
  Convert Pi type judgments
    "f : T1 \<Rightarrow> ... \<Rightarrow> Tn \<Rightarrow> T"
  to derivation rules
    "x1 : T1 \<Longrightarrow> ... \<Longrightarrow> xn : Tn \<Longrightarrow> f x1 ... xn : T".
*)
fun Pi_derivation_rule thm =
  case Soft_Type.type_of_typing (Thm.concl_of thm) of
    Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ _ =>
      Pi_derivation_rule (thm RS @{thm Pi_typeE})
  | _ => thm

(*
  Convert "T \<prec> S" to "x : T \<Longrightarrow> x : S".

  UNUSED at the moment!
*)
(* fun subtype_derivation_rule thm =
  thm RS @{thm subtypeE'}
  handle THM _ => error "subtype_derivation_rule: not a subtype judgment" *)


(** Backward derivation rules **)

(*Register derivation rules that should be applied backwards*)
val backderivation_rule_parser: attribute context_parser =
  let 
    fun register_bderived_type thm =
      let val concl = Thm.concl_of thm
      in
        if Soft_Type.is_typing concl
        then put_bderived_type (Soft_Type.type_of_typing concl)
        else I
      end
  in
    Scan.lift (Scan.succeed (Thm.declaration_attribute (fn thm =>
      put_backderivation_rule thm
      #> register_bderived_type thm)))
  end

val _ =
  Theory.setup (Attrib.setup \<^binding>\<open>backward_derive\<close> backderivation_rule_parser
    "declare backwards derivation rule")


(** Standard derivation rules **)

(*
  Register type derivation rules.

  As described in the section "Backderived types", a derivation rule will also
  automatically be declared backderivation if it contains a simple typing
  premise whose type specializes a type having a backderived rule.
*)

val derivation_rule_parser: attribute context_parser =
  Scan.lift (Scan.succeed (Thm.declaration_attribute put_derivation_rule))

val _ =
  Theory.setup (Attrib.setup \<^binding>\<open>derive\<close> derivation_rule_parser
    "declare derivation rule")


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
  in
    context
    |> Soft_Type_Context.put_current_type x thm
    |> Soft_Type_Context.put_type x thm
    |> (if is_Const x
        then Implicit_Arguments.put_implicit (fst (dest_Const x)) names
        else I)
    |> (if Soft_Type.is_Pi st
        then put_derivation_rule (Pi_derivation_rule thm)
        else I)
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>type\<close>
  (Scan.lift (Scan.option (Args.$$$ "implicit" |-- Args.colon |-- Parse.int)
    >> (fn implicit => Thm.declaration_attribute (declare_current_type implicit))))
  "declare current soft type")


(*** Type derivation ***)

val derive_depth = Attrib.setup_config_int \<^binding>\<open>derivation_depth\<close> (K 10)

(*
  Generate all possible type judgments for a given term that can be derived from
  a single derivation rule by using a given collection of known judgments to
  discharge its premises.
*)
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
          val facts = map fst (Facts.props (Proof_Context.facts_of goal_ctxt))

          fun is_derivation_rule thm =
            Soft_Type.is_typing (Thm.concl_of thm)
            andalso not (Thm.no_prems thm)
            andalso forall Soft_Type.is_jdgmt (Thm.prems_of thm)

          fun add_to_context prem context =
            let
              val prop = Thm.prop_of prem

              val trans_opt =
                get_forward_translation (Context.proof_of context)
                    (head_of (Soft_Type.dest_Trueprop prop))

              val add_translation =
                case trans_opt of
                  SOME th =>
                    let
                      val typing = prem RS th
                      val t = Soft_Type.term_of_typing (Thm.prop_of typing)
                    in
                      Soft_Type_Context.put_type t typing
                    end
                | NONE => I
            in
              (if Soft_Type.is_typing prop then
                (if Soft_Type.is_Pi (Soft_Type.type_of_typing prop)
                then put_derivation_rule (Pi_derivation_rule prem) context
                else context)
                |> Soft_Type_Context.put_type (Soft_Type.term_of_typing prop) prem
              else if Soft_Type.is_adj prop then
                Soft_Type_Context.put_adj (Soft_Type.term_of_jdgmt prop) prem context
              else if is_derivation_rule prem then
                put_derivation_rule prem context
              else context)
              |> add_translation
            end

          val goal_ctxt' =
            goal_ctxt
            |> Context.proof_map (fold add_to_context
              (map (Soft_Type.eta_norm goal_ctxt) (add_facts @ facts @ prems)))

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
            trace goal_ctxt' (cat_lines (
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
          case filter (fn th => Term.could_unify (concl_tm, Thm.prop_of th)) jdgmts'
          of
            [] => (trace goal_ctxt' ">> No unifier!\n"; no_tac)
          | ths => (
              trace goal_ctxt' (itemize (map (str_of_tm o Thm.prop_of) ths));
              HEADGOAL (
                foldl1 (op APPEND') (map (fn th => resolve_tac goal_ctxt' [th]) ths)))
        end
      else no_tac
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
