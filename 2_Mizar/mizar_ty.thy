(********
Type automation for Isabelle/Mizar.
Mar 2019.

Some parts inspired by `$ISABELLE_HOME/src/Pure/Tools/named_thms.ML`.
********)

theory mizar_ty
imports mizar

begin

section \<open>Utility functions\<close>

ML \<open>
(* Set up tracing for debugging purposes *)
val ty_debug = Attrib.setup_config_bool @{binding "ty_debug"} (K false)

fun warn context msg = if Config.get (Context.proof_of context) ty_debug then warning msg else ()

(* Print warning and do nothing *)
fun id_msg msg = (warning msg; I)

(* Check if a term is a *non-conditional* typing judgment.
   A negated statement of has_type(Set) is also a typing judgment since it
   expresses the judgment "x is non T"
 *)
fun is_typing tm =
  let val tm' = dest_Trueprop tm
  in
    case tm' of
      @{const has_type(Set)} $ _ $ _ => true
    | @{const Not} $ (@{const has_type(Set)} $ _ $ _) => true
    | _ => false
  end
  handle TERM _ => false

(* Break a typing judgment into its term and type parts *)
fun dest_typing tm =
  let val tm' = dest_Trueprop tm
  in
    case tm' of
      @{const has_type(Set)} $ t $ T => (t, T)
    | @{const Not} $ (@{const has_type(Set)} $ t $ T) => (t, T)
    | _ => Exn.error "dest_typing: not a typing judgment"
  end
  handle TERM _ => Exn.error "dest_typing: cannot apply dest_Trueprop"

val tm_of_typing = #1 o dest_typing
val ty_of_typing = #2 o dest_typing

(* Break conclusion of a theorem into its conjuncts *)
fun dest_concl_conjs thm =
  (case dest_Trueprop (Thm.concl_of thm) of
    Const (@{const_name conj}, _) $ _ $ _ =>
      dest_concl_conjs (thm RS @{thm conjunct1}) @
      dest_concl_conjs (thm RS @{thm conjunct2})
  | _ => [thm])
  handle TERM _ => [thm]

(* Remove premises of the form "x be T" from a rule *)
fun remove_triv_prems thm =
  let
    fun is_object_typing tm =
      let val tm' = dest_Trueprop tm
      in
        case tm' of
          @{const has_type(Set)} $ _ $ @{const object} => true
        | _ => false
      end
      handle TERM _ => Exn.error "remove_triv_prems: cannot apply dest_Trueprop"
    
    fun rec_remove_triv n thm =
      if n = 0 then thm
      else if nth (Thm.prems_of thm) (n-1) |> is_object_typing
      then rec_remove_triv (n-1) (@{thm object_root} RSN (n, thm))
      else rec_remove_triv (n-1) thm
  in
    rec_remove_triv (Thm.nprems_of thm) thm
  end

(* Normalize theorem:
   simplify using the main simpset and basic Mizar definitions [*]
   rulify conjunctions in the premises,
   split conjunctions in the conclusion into multiple theorems,
   and only keep the resulting rules whose conclusions are typing judgments.

   [*] In particular, intersection types are split into their conjuncts,
   "x be non T" is simplified to "\<not> x be T", and all premises of the form
   "x be object" are removed.
*)
fun normalize context thm =
  let
    val ctxt = Context.proof_of context
    val simpctxt = (put_simpset main_ss ctxt) addsimps @{thms ty_intersection non_property}
  in
    Simplifier.full_simplify simpctxt thm |>
      Object_Logic.rulify ctxt |>
      remove_triv_prems |>
      dest_concl_conjs |>
      filter (is_typing o Thm.concl_of)
  end
\<close>


section \<open>Data slot and attribute setup\<close>

ML \<open>
structure Ty_Data = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm_prop (single o tm_of_typing o Thm.concl_of)
  val extend = I
  val merge = Item_Net.merge
)

structure Clus_Data = Generic_Data (
  type T = thm Item_Net.T
  val empty = Item_Net.init Thm.eq_thm_prop (single o tm_of_typing o Thm.concl_of)
  val extend = I
  val merge = Item_Net.merge
)

val get_ty_data = Item_Net.content o Ty_Data.get
val get_clus_data = Item_Net.content o Clus_Data.get

val add_ty_data = Ty_Data.map o Item_Net.update
val add_clus_data = Clus_Data.map o Item_Net.update

(* Add multiple theorems to data slots - should not usually use this directly;
   instead use the "add_normalized_..." functions below. *)
val add_thms_ty_data = fold add_ty_data
val add_thms_clus_data = fold add_clus_data

(* Add the results of normalizing a given theorem *)
fun add_normalized_ty_data thm context = add_thms_ty_data (normalize context thm) context
fun add_normalized_clus_data thm context = add_thms_clus_data (normalize context thm) context
\<close>

text \<open>Attribute setup:\<close>

ML \<open>
val clus_acparser =
  let
    val check_typing_concl = fn thm =>
      let
        val not_all_typing_concls =
          (exists not) o (map (is_typing o Thm.concl_of)) o dest_concl_conjs
      in
        if not_all_typing_concls thm then Exn.error "Not a typing rule" else I
      end
  in
    Attrib.add_del
      (Thm.declaration_attribute (fn thm =>
        (check_typing_concl thm) #> (add_normalized_clus_data thm)))
      (Thm.declaration_attribute (fn _ => id_msg
        "Manual deletion of registrations is unsupported; no action taken"))
      (* For now we do not allow deletion of cluster registrations; a more thorough approach
         would involve keeping track of the typing judgments J that follow from each registration
         and deleting those J whose required registrations are deleted from the named theorem space.
      *)
  end
\<close>

setup \<open>
Attrib.setup @{binding "clus"} clus_acparser "Add normalized cluster registration." #>
Global_Theory.add_thms_dynamic (@{binding "clus"}, get_clus_data)
\<close>


section \<open>Existential registrations\<close>

\<comment>\<open>This is just mostly copied from the original code\<close>

named_theorems ex
declare object_exists[ex]

simproc_setup ex_simp ("inhabited(x)") = \<open>
fn _ => fn ctxt => fn ctm =>
  let
    val prems = filter (is_typing o Thm.prop_of) (Simplifier.prems_of ctxt)
    val ctxt' = Context.proof_map (fold add_ty_data prems) ctxt
    val ex = Proof_Context.get_thms ctxt' "ex"
    val ty = Proof_Context.get_thms ctxt' "ty"
    val clus = Proof_Context.get_thms ctxt' "clus"
    val thm =
      Simplifier.asm_full_rewrite
        (put_simpset main_ss ctxt' addsimps ty @ clus @ ex) ctm
    val (_ $ _) $ r = Thm.prop_of thm
  in
    if r = @{term True} orelse r = @{term False} then SOME thm else NONE
  end
\<close>


section \<open>Type derivation\<close>

ML \<open>
(* Derive all typings for `tm` not already in `typings` that are
   deducible from `rule` by instantiating the term in the typing conclusion
   of `rule` with `tm`, and discharging any premises using typing judgments
   in `typings`.

   NOTE: Derived typings are *not* normalized!
*)
fun term_typings_from_rule context tm rule typings =
  let
    fun concl_in_ty thm =
      subset (Term.aconv) (map Thm.concl_of (normalize context thm), map Thm.prop_of typings)

    (* Recursively filter rules whose conclusions are already in [ty],
       and discharge the rightmost premise of those remaining.
       In each recursive call, the theorems in the argument `thms` have
       the same number of premises. *)
    fun rec_discharge_prems thms = case thms |> filter_out concl_in_ty of
        [] => []
      | thms as thm :: _ =>
          if Thm.no_prems thm then thms
          else rec_discharge_prems (typings RLN (Thm.nprems_of thm, thms))
  in
    let
      val inst =
        (Thm.match o apply2 (Thm.cterm_of (Context.proof_of context)))
          ((tm_of_typing o Thm.concl_of) rule, tm)
    in
      rec_discharge_prems [Thm.instantiate inst rule]
    end
    handle Pattern.MATCH =>
      (warn context
        "term_typings_from_rule: could not match term in typing conclusion of the given rule";
      [])
  end

(* Recursion depth limit for type derivation *)
val ty_deriv_depth = Attrib.setup_config_int @{binding "ty_deriv_depth"} (K 10)

(* Derive typings for a set of terms using the typing data and registrations
   available in the context.
   All typings derived are already normal since the registrations are normalized.
   The returned results include typings already in the context.
*)
fun derive_typings ctxt tms =
  let
    val context = Context.Proof ctxt
    val clus_net = Clus_Data.get context

    fun rec_derive_typings typings iter =
      if iter > Config.get ctxt ty_deriv_depth
      then (warning "Type derivation depth limit reached; maybe consider increasing this?"; typings)
      else
        let
          fun new_tm_typings (tm, candidate_rules) =
            map (fn rule => term_typings_from_rule context tm rule typings) candidate_rules
              |> flat |> distinct Thm.eq_thm_prop
          
          (* Pair each term in `tms` with a list of registration rules that match it *)
          val matching_tm_rules = tms ~~ map (Item_Net.retrieve clus_net) tms
          
          val new_typings = flat (map new_tm_typings matching_tm_rules)
        in
          if null new_typings then typings else rec_derive_typings (typings @ new_typings) (iter+1)
        end
  in
    rec_derive_typings (get_ty_data context) 0
  end

(* Return the list of theorems obtained by simplifying the premises of a given
   theorem and instantiating those which are typings using type information
   available in the context.
   Note that the simplification is different from that done in normalization;
   we split intersection and non- types, remove trivial premises of the form
   "a be object" for non-schematic a, and only use the basic HOL simpset
   (c.f. `normalize` above).
*)
fun instantiate_typings ctxt thm =
  let
    val typings = get_ty_data (Context.Proof ctxt)

    (* Test if a term is an "a be object" judgment for non-schematic a *)
    fun is_nonsch_obj_typing tm =
      (ty_of_typing tm) aconv @{const object} andalso not (is_Var (tm_of_typing tm))

    fun rec_inst_typings n thm =
      if n = 0 then [thm]
      else let val prem = nth (Thm.prems_of thm) (n-1) in
        if is_typing prem then
          (* Remove non-schematic "a is object" typings from the premises *)
          if is_nonsch_obj_typing prem
          then rec_inst_typings (n-1) (@{thm object_root} RSN (n, thm))
          else map (rec_inst_typings (n-1)) (typings RLN (n, [thm])) |> flat
        else rec_inst_typings (n-1) thm
      end

    val simpctxt = (put_simpset basic_ss ctxt) addsimps @{thms ty_intersection non_property}

    val thm' = Object_Logic.rulify ctxt (Simplifier.asm_full_simplify simpctxt thm)
  in
    rec_inst_typings (Thm.nprems_of thm') thm'
  end

(* Return a list of all distinct subterms of a given term that have meta-type `Set`
   (i.e. the Mizar-typable subterms) *excluding* those that contain schematic variables or
   that are open.
   The list is sorted in what is usually a good approximation of the subterm partial order.
*)
fun typable_subterms tm =
  let
    fun fastype_of' tm = fastype_of tm handle TERM _ => dummyT

    val res =
      if fastype_of' tm = @{typ Set} andalso
         not (Term.is_open tm) andalso
         not (exists_subterm is_Var tm)
      then [tm]
      else []
  in
    res @ (case tm of
      t1 $ t2 => typable_subterms t1 @ typable_subterms t2
    | Abs(_, _, t) => typable_subterms t
    | _ => []
    ) |> Ord_List.make Term_Ord.fast_term_ord
  end

(* Helper function: takes the current context and a list of terms and
   returns a triple `(tms, typings, ctxt)` whose entries are, respectively,
     1. The typable subterms of the current context, i.e. those in the given terms,
        those in [ty], and the definitional theorems for these terms,
     2. All typings derivable about these subterms using (recursively) the
        typings and cluster registrations in the context,
     3. The argument context in which [ty] is augmented with the derived typing data.
*)
fun gen_typing_data' ctxt terms =
  let
    val ty = get_ty_data (Context.Proof ctxt)
    
    fun defnames_in_term tm = case tm of
          Const (name, _) => [name]
        | t1 $ t2 => defnames_in_term t1 @ defnames_in_term t2
        | Abs(_, _, t) => defnames_in_term t
        | _ => []
    
    fun typable_terms_of_fact name =
      let
        val def = (hd o #thms o the) (Proof_Context.lookup_fact ctxt name)
      in
        (typable_subterms o Thm.prop_of) def
      end
      handle Option.Option => []
    
    val tms_from_ctxt =
      map typable_subterms (terms @ map Thm.prop_of ty) |> flat |> distinct Term.aconv
    
    val tms_from_defs =
      tms_from_ctxt
          |> map defnames_in_term |> flat
          |> map typable_terms_of_fact |> flat
          |> distinct Term.aconv

    val tms = tms_from_ctxt @ tms_from_defs
    val typings = derive_typings ctxt tms
    val ctxt' = Context.proof_map (add_thms_ty_data typings) ctxt
  in (tms, typings, ctxt') end

val gen_typing_data = fn ctxt => (gen_typing_data' ctxt) o (map Thm.prop_of)
\<close>

text \<open>Attribute setup:\<close>

ML \<open>
val ty_acparser =
  let
    (* The following check needs to be modified: we also want to admit theorems of the form
       <typing judgment> ==> False; see e.g. int_1_th_13 *)
    fun check_typing thm =
      let
        val not_all_typings =
          (exists not) o (map (is_typing o Thm.prop_of)) o dest_concl_conjs
      in
        if not_all_typings thm then Exn.error "Not a typing judgment" else I
      end
    
    fun derive_conseqs thm context =
      let val (_, _, ctxt') = gen_typing_data (Context.proof_of context) [thm]
      in Context.Proof ctxt' end
  in
    Attrib.add_del
      (Thm.declaration_attribute (fn thm => 
        (* (check_typing thm) #> *) (add_normalized_ty_data thm) #> (derive_conseqs thm)))
      (Thm.declaration_attribute (fn _ => id_msg
        "Manual deletion of typing judgments is unsupported; no action taken"))
      (* Similar situation here as for registrations *)
  end
\<close>

setup \<open>
Attrib.setup @{binding "ty"} ty_acparser "Add normalized typing judgment and derived consequences"
  #> Global_Theory.add_thms_dynamic (@{binding "ty"}, get_ty_data)
\<close>


section \<open>Methods\<close>

ML \<open>
(* Infer typing information and add it to the context, without changing the goal state. *)
fun infer_ty_method facts (ctxt, goal) =
  let
    val (tms, typings, ctxt') = gen_typing_data ctxt (goal::facts)
    val _ =
      if Config.get ctxt ty_debug
      then (@{print} "tms, typings:"; @{print} tms; @{print} typings)
      else []
  in [(ctxt', goal)] |> Seq.of_list |> Seq.make_results end

(* Derive typing information and use it to instantiate typings in subgoal premises. *)
fun inst_ty_method facts (ctxt, goal) =
  let
    val (_, typings, ctxt') = gen_typing_data ctxt (goal::facts)
    val inst_facts = flat (map (instantiate_typings ctxt') facts)
    val inst_ty_tac = Method.insert_tac ctxt' (inst_facts @ typings)
  in
    METHOD (K (ALLGOALS inst_ty_tac)) facts (ctxt, goal)
  end

(* Derive typings, instantiate premises, move into the subgoal statements and perform auto *)
fun inst_ty_auto_method facts (ctxt, goal) =
  let
    val (_, typings, ctxt') = gen_typing_data ctxt (goal::facts)
    val inst_facts = flat (map (instantiate_typings ctxt') facts)
    val inst_ty_tac = Method.insert_tac ctxt' (inst_facts @ typings)
  in
    METHOD (K (ALLGOALS inst_ty_tac THEN Clasimp.auto_tac ctxt')) facts (ctxt, goal)
  end

fun infer_auto_method facts (ctxt, goal) =
  let
    val (_, typings, ctxt') = gen_typing_data ctxt (goal::facts)
    val insert_facts_ty_tac = Method.insert_tac ctxt' (typings @ facts)
  in
    METHOD (K (ALLGOALS insert_facts_ty_tac THEN Clasimp.auto_tac ctxt')) facts (ctxt, goal)
  end
\<close>

method_setup move =
  \<open>Scan.succeed (METHOD o (ALLGOALS oo Method.insert_tac))\<close> "Move facts into the goal statements"

method_setup infer_ty = \<open>
Scan.succeed (K infer_ty_method)
\<close> "Derive as much type information as possible about the terms appearing in the currect context, without changing the goal state"

method_setup inst_ty = \<open>
Scan.succeed (K inst_ty_method)
\<close> "Instantiate facts with typings and move them into the goal statements"

method_setup inst_nopass_auto = \<open>
Scan.succeed (K inst_ty_auto_method)
\<close> "Instantiate facts, move into goal statements and call auto. Discards the original facts."

method inst_pass_auto = (inst_ty, auto)
\<comment>\<open>Instantiate facts, move into goal statements and call auto. Keeps the original facts.\<close>

method_setup infer_auto = \<open>
Scan.succeed (K infer_auto_method)
\<close> "Move facts and derived typings into goal statements and call auto"

method ty_simp = simp add: ty
method infer_simp = (infer_ty, simp add: ty)

method ty_auto = auto intro: ty simp: ty
method mauto = (solves\<open>ty_auto\<close> | solves\<open>inst_nopass_auto\<close> | solves\<open>inst_pass_auto\<close>)+


end
