(* Title:  derivation.ML
   Author: Joshua Chen
   Date:   Jul 2019

Management and automation of type derivation, and setup of soft type interface.

*)

structure Derivation =
struct

(*** Tracing ***)

val derive_debug = Attrib.setup_config_bool @{binding "derive_debug"} (K false)

fun warn ctxt msg = if Config.get ctxt derive_debug then warning msg else ()


(*** Context data for type derivation rules ***)
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


(*** Type derivation ***)

(*
  Recursion depth limit for type derivation
*)
val derive_depth = Attrib.setup_config_int @{binding "derive_depth"} (K 10)

(*
  Derive all judgments for `tm` not already in `jdgmts` that are deducible from `rule` by
  instantiating the term in the conclusion of `rule` with `tm`, and discharging any premises
  using the theorems in `jdgmts`.
*)
fun term_jdgmts_from_rule ctxt tm jdgmts rule =
  let
    fun in_jdgmts thm =
      subset
        (Term.aconv)
        (map Thm.concl_of (Soft_Type_Context.normalize ctxt thm), map Thm.prop_of jdgmts)

    (*
      Recursively filter rules whose conclusions are already in `jdgmts`, and discharge
      the rightmost premise of those remaining. In each recursive call, the theorems in
      the argument `thms` have the same number of premises.
    *)
    fun rec_discharge_prems thms = case thms |> filter_out in_jdgmts of
        [] => []
      | thms as thm :: _ =>
          if Thm.no_prems thm then thms
          else rec_discharge_prems (jdgmts RLN (Thm.nprems_of thm, thms))
  in
    let
      val inst =
        (Thm.match o apply2 (Thm.cterm_of ctxt))
          ((Soft_Type.term_of_jdgmt o Thm.concl_of) rule, tm)
    in
      rec_discharge_prems [Thm.instantiate inst rule]
    end
    handle Pattern.MATCH => []
  end

(*
  Derive judgments for a set of terms starting with the judgment data for those terms and
  using derivation rules available in the context.

  All derived judgments are atomic since the derivation rules are normalized.
  The returned results include judgments already in the context.
*)
fun derive_jdgmts ctxt tms =
  let
    val rules = get_derivation_rules ctxt

    fun rec_derive_jdgmts jdgmts iter =
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
          else rec_derive_jdgmts (jdgmts @ new_jdgmts) (iter + 1)
        end
  in
    rec_derive_jdgmts
      (Soft_Type_Context.get_types ctxt tms @ Soft_Type_Context.get_adjs ctxt tms) 0
  end


(*** Soft type setup ***)

(** Further processing of particular type judgments **)

(* Function types *)

(*
  Convert a judgment "f : T1 \<Rightarrow> ... \<Rightarrow> Tn \<Rightarrow> T" to a rule
  "x1 : T1 \<Longrightarrow> ... \<Longrightarrow> xn : Tn \<Longrightarrow> f x1 ... xn : T" and add it to the derivation rule list.
*)
fun Pi_derivation_rule thm = case Soft_Type.type_of_typing (Thm.concl_of thm) of
    Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ _ => Pi_derivation_rule (thm RS @{thm Pi_typeE})
  | _ => thm


(* Subtypes *)

(*
  Convert "T \<prec> S" to "x : T \<Longrightarrow> x : S"
*)
fun subtype_derivation_rule thm =
  thm RS @{thm subtypeE'}
  handle THM _ => error "subtype_derivation_rule: not a subtype judgment"

val put_subtype_rule = Named_Theorems.add_thm \<^named_theorems>\<open>subtype_rules\<close>


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
      Thm.declaration_attribute (declare_current_type implicit)))) "Declare current soft type")


(*** Tactics ***)

fun discharge_type_tac ctxt tms =
  let
    fun typable_subterms t = case t of
        Const (_, _) => [t]
      | Free (_, _) => [t]
      | Abs (_, _, b) => [t] @ typable_subterms b
      | t1 $ t2 => [t] @ typable_subterms t1 @ typable_subterms t2
      | _ => []

    val str_of_tm = Syntax.string_of_term ctxt
  in
    SUBGOAL (fn (sg, i) => (
      if Soft_Type.is_jdgmt sg
      then
        let
          val tm = Soft_Type.term_of_jdgmt sg

          val typings =
            derive_jdgmts ctxt (typable_subterms tm @ flat (map typable_subterms tms))

          val _ =
            Soft_Type.tracing ctxt (cat_lines [
              "Discharge judgment " ^ str_of_tm sg,
              "Subterms:\n" ^
                (commas (map str_of_tm (typable_subterms tm))),
              "Additional terms:\n" ^
                (commas (map str_of_tm (flat (map typable_subterms tms)))),
              "Derived judgments:\n" ^
                (commas (map (str_of_tm o Thm.prop_of) typings))])
        in
          (case find_first (fn th => Term.could_unify (sg, Thm.prop_of th)) typings of
            NONE => no_tac
          | SOME th => resolve_tac ctxt [th] i)
        end
      else no_tac))
  end


end
