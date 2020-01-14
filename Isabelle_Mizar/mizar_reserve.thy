theory mizar_reserve
imports mizar_defs

keywords
  "reserve" :: thy_decl and
  "mtheorem" "mlemma" "mscheme" :: thy_goal and
  "mdefinition" "mdef" :: thy_goal and
  "mlet"

begin

ML \<open>
structure Miz_Reserve_Data = Theory_Data (
  type T = term Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = K Symtab.empty
)
\<close>

ML \<open>
fun do_var gen (v as (n, _)) lthy =
  case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of lthy)) n of
    NONE => raise Fail ("Non-reserved free set variable: " ^ n ^ " in goal!")
  | SOME D =>
    let
      val fs = Term.add_frees D [];
      val (assms, lthy1) = fold_map (do_var gen) fs lthy;
      val (_, lthy2) =
        if Variable.is_fixed lthy1 n then ([], lthy1) else Variable.add_fixes [n] lthy1;
      val cp = Thm.cterm_of lthy (mk_Trueprop ((@{term ty_membership} $ (Free v)) $ D))
      val (assm, lthy3) = yield_singleton (Assumption.add_assms Assumption.presume_export) cp lthy2
    in
      ((assm :: flat assms),
        if gen then lthy3 else Context.proof_map (add_normalized_ty_data assm) lthy3)
    end

fun do_var_nofail gen (v as (n, _)) lthy =
  let fun justfix lthy =
    (if Variable.is_fixed lthy n then ([], lthy) else ([], snd (Variable.add_fixes [n] lthy)))
  in
    do_var gen v lthy
    handle Fail _ => justfix lthy
         | TYPE _ => justfix lthy
  end
\<close>

ML \<open>
fun reserve_cmd (vs, tm) lthy =
  let
    val _ = if fastype_of tm <> @{typ "Ty"} then
      raise Fail "not a correctly typed constraint" else ();
    fun reserve thy =
      fold (fn v => fn thy => Miz_Reserve_Data.map (Symtab.update (v, tm)) thy)
        vs thy;
  in Local_Theory.background_theory reserve lthy end

val _ =
  Outer_Syntax.local_theory @{command_keyword reserve}
    "reserve variable names with types"
    ((Parse.list1 Parse.text -- (\<^keyword>\<open>for\<close> |-- Parse.term)) >> (fn (vs, tm) => fn lthy => reserve_cmd (vs, Syntax.read_term lthy tm) lthy))
\<close>

ML \<open>
fun do_lt tm lthya =
  case dest_Trueprop tm of
    (@{const has_type(Set)} $ Free (n, _) $ _) =>
      let
        val (_, lthya2) =
          if Variable.is_fixed lthya n then ([], lthya) else Variable.add_fixes [n] lthya
        val ct = Thm.cterm_of lthya tm
        val (assm, lthya3) =
          yield_singleton (Assumption.add_assms Assumption.presume_export) ct lthya2
      in (assm, Context.proof_map (add_normalized_ty_data assm) lthya3) end
  | _ =>
      let
        val ct = Thm.cterm_of lthya tm
        val (assm, lthya2) =
          yield_singleton (Assumption.add_assms Assumption.presume_export) ct lthya
      in (assm, lthya2 addsimps [assm]) end
\<close>

ML \<open>
fun normalize_thm ctxt th =
  let
    val th2 = Object_Logic.rulify ctxt th
    val ss =
      put_simpset main_ss ctxt
        addsimps @{thms object_root ty_intersection} addsimprocs [@{simproc ex_simp}]
    val th3 = Simplifier.asm_full_simplify ss th2 handle THM _ => th2
    fun do_prem
        (Const (@{const_name Trueprop}, _) $ (Const (@{const_name Ball}, _) $ _ $ _)) = @{thm ballI}
      | do_prem _ = asm_rl
    val th4 = th3 OF (map (do_prem o Logic.strip_assums_concl) (Thm.prems_of th3))
    val th5 = @{thm bspec} OF [th4] handle THM _ => th4
  in
    if Thm.prop_of th = Thm.prop_of th5 then th else normalize_thm ctxt th5
  end
\<close>

ML \<open>
fun mdecl2 nameoption getth lt2 afterqed ((tm, (_, th)), lthy2) =
  let
    val vs = Term.add_vars (Thm.prop_of th) []
    val fs = map (fn (v as ((n, _), t)) => (v, Thm.cterm_of lthy2 (Free (n, t)))) vs
    val th2 = Thm.instantiate ([], fs) th
    val fname = case nameoption of SOME n => n | NONE => fst (dest_Free tm)
    val thr2 = (getth (Thm.prop_of th2)) OF [th2]
    val as_fs = map_filter (fn th => SOME ((dest_Free o fst o dest_typing) th) handle TERM _ => NONE) lt2
    val c_fs = Term.add_frees (Thm.prop_of thr2) []
    val fs = subtract (=) as_fs c_fs
    val setfs = filter (fn (_, ty) => ty = @{typ Set}) fs
    val (assms1, lthy2a) = fold_map (do_var_nofail false) setfs lthy2
    val (assms2, lthy3) = fold_map do_lt lt2 lthy2a
    val lthy4 = #3 (gen_typing_data' lthy3 (map Thm.prop_of (thr2 :: flat assms1 @ assms2)))
    fun after_qed thms lthy' = afterqed fname (flat thms) (Thm.prop_of th2) lthy'
  in
    lthy4
      |> Proof.theorem NONE after_qed [[(Thm.concl_of thr2, [])]]
      |> Proof.refine_singleton
          (Method.Basic (fn ctxt => Method.SIMPLE_METHOD (resolve_tac ctxt [thr2] 1)))
  end
\<close>

ML \<open>
fun mdecl nameoption decl lt defn getth afterqed lthy =
  let
    val lt2 = map (Syntax.read_prop lthy) (flat (the_list lt))
    val lthy1 = fold Variable.declare_term lt2 lthy
    val (ret, lthy2) =
      Specification.definition_cmd (SOME decl) [] [] (Binding.empty_atts, defn) false lthy1
  in
    mdecl2 nameoption getth lt2 (afterqed NONE) (ret, lthy2)
  end
\<close>

ML \<open>
fun mdecl_cmd nameoption decl lt defn getth afterqed lthy =
  let
    val lthy1 = fold Variable.declare_term lt lthy
    val (ret, lthy2) =
      Specification.definition' (SOME decl) [] [] (Binding.empty_atts, defn) false lthy1
  in
    mdecl2 nameoption getth lt (afterqed (SOME lthy2)) (ret, lthy2)
  end
\<close>

ML \<open>
fun mdefinition ((decl, lt), (defn, thref)) lthy =
  let
    fun afterqed retlthy fname thms _ lthy' =
      let
        val bind = (Binding.make (fname, Position.none), [])
        val ths = [(map (normalize_thm lthy') (conj_elims (the_single thms)), [])]
        val a = Attrib.partial_evaluation lthy' [(bind, ths)]
      in Local_Theory.notes a lthy' |> snd end
  in
    mdecl NONE decl lt defn (fn _ => singleton (Attrib.eval_thms lthy) thref) afterqed lthy
  end

val parser =
  (Parse_Spec.constdecl --
    (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
    (Parse.prop -- (@{keyword ":"} |-- Parse.thm))) >> mdefinition

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword mdefinition} "Mizar constant" parser
\<close>
ML \<open>
fun yxml_insert i s =
  case YXML.parse s of
    XML.Elem (a, [XML.Text c]) =>
      let
        val _ = warning (@{make_string} a)
        val s1 = String.substring (c, 0, 1)
        val s2 = String.substring (c, 1, (String.size c - 1))
      in
        YXML.string_of (XML.Elem (a, [XML.Text (s1 ^ i ^ s2)]))
      end
  | _ => raise ERROR "yxml_insert"
 \<close>

ML \<open>
fun note_suffix fname sffx attrs thm lthy =
  let
    val bind = ((Binding.map_name (suffix sffx) (Binding.make (fname, Position.none))), [])
    val a = Attrib.partial_evaluation lthy [(bind, [([normalize_thm lthy thm], attrs)])]
  in Local_Theory.notes a lthy |> snd end

fun conj1_ty_func name (thm, lthy) =
  let
    val thm_ty = @{thm conjunct1} OF [thm]
    val lthy' = Local_Theory.declaration {syntax = false, pervasive = false}
      (fn phi => add_normalized_clus_data (Morphism.thm phi thm_ty)) lthy
    val lthy'' = note_suffix name "_ty" [] thm_ty lthy'
    val thm = @{thm conjunct2} OF [thm]
  in (thm, lthy'') end

fun conj1_note_suffix suffix name (thm, lthy) =
  (@{thm conjunct2} OF [thm], note_suffix name suffix [] (@{thm conjunct1} OF [thm]) lthy)

fun conj2_note_suffix suffix name (thm, lthy) =
  (@{thm conjunct1} OF [thm], note_suffix name suffix [] (@{thm conjunct2} OF [thm]) lthy)

fun conj1_ex name (thm, lthy) =
  (@{thm conjunct2} OF [thm], snd (Local_Theory.note ((Binding.make (name ^ "_ex", Position.none), @{attributes [simplified,rule_format,ex]}), [@{thm conjunct1} OF [thm]]) lthy))

fun conj1_clus name (thm, lthy) =
  (@{thm conjunct2} OF [thm], snd (Local_Theory.note ((Binding.make (name ^ "_clus", Position.none), @{attributes [simplified,rule_format,clus]}), [@{thm conjunct1} OF [thm]]) lthy))

fun conj1_note_elim suf name (thm, lthy) =
  (@{thm conjunct2} OF [thm], snd (Local_Theory.note ((Binding.make (name ^ suf, Position.none), @{attributes [rule_format]}), [@{thm conjunct1} OF [thm]]) lthy))

fun conj1_note_intro suf name (thm, lthy) =
  (@{thm conjunct2} OF [thm], snd (Local_Theory.note ((Binding.make (name ^ suf, Position.none), @{attributes [rule_format,intro?]}), [@{thm conjunct1} OF [thm]]) lthy))

fun c1_note_attr suf atr name (thm, lthy) =
  (@{thm conjunct2} OF [thm], snd (Local_Theory.note ((Binding.make (name ^ suf, Position.none), atr), [@{thm conjunct1} OF [thm]]) lthy))

fun note_attr suf atr name (thm, lthy) =
  (thm, snd (Local_Theory.note ((Binding.make (name ^ suf, Position.none), atr), [thm]) lthy))
\<close>

ML \<open>
structure Miz_Identify_Data = Generic_Data (
  type T =
    (thm * ((string -> thm * local_theory -> thm * local_theory) list * Token.src list))
      Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = (Symtab.merge (fn _ => true))
)

fun add_miz_ident s th tr a ctxt =
  Context.theory_map (Miz_Identify_Data.map (Symtab.update_new (s, (th, (tr, a))))) ctxt
\<close>

setup \<open>
  fn thy => thy
  |> add_miz_ident @{const_name "ClusterFuncNoFor"}
      @{thm ClusterFuncNoFor_property}
      []
      @{attributes [simplified, rule_format, clus]}
  |> add_miz_ident @{const_name "ClusterFuncFor"}
      @{thm ClusterFuncFor_property}
      []
      @{attributes [simplified, rule_format, clus]}
  |> add_miz_ident @{const_name "ClusterExistence"}
      @{thm ClusterExistence_property}
      []
      @{attributes [simplified, rule_format, ex]}
  |> add_miz_ident @{const_name "ClusterCondAttrsAttrsTy"}
      @{thm ClusterCondAttrsAttrsTy_property}
      []
      @{attributes [simplified, rule_format, clus]}
  |> add_miz_ident @{const_name "ClusterCondAttrsTy"}
      @{thm ClusterCondAttrsTy_property}
      []
      @{attributes [simplified, rule_format, clus]}
  |> add_miz_ident @{const_name "redefine_func_means"}
      @{thm redefine_func_means_property}
      [c1_note_attr "_uniq" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_func_assume_means"}
      @{thm redefine_func_assume_means_property}
      [c1_note_attr "_uniq" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_func_means_if1"}
      @{thm redefine_func_means_if1_property}
      [c1_note_attr "_uniq" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_func_means_if1o"}
      @{thm redefine_func_means_if1o_property}
      [c1_note_attr "_uniq" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_func_equals"}
      @{thm redefine_func_equals_property}
      []
      @{attributes [rule_format]}
  |> add_miz_ident @{const_name "redefine_func_assume_equals"}
      @{thm redefine_func_assume_equals_property}
      []
      @{attributes [rule_format]}
  |> add_miz_ident @{const_name "redefine_func_equals_if1"}
      @{thm redefine_func_equals_if1_property}
      []
      @{attributes [rule_format]}
  |> add_miz_ident @{const_name "redefine_func_type"}
      @{thm redefine_func_type_property}
      []
      @{attributes [simplified, rule_format, clus]}
  |> add_miz_ident @{const_name "redefine_attr_means"}
      @{thm redefine_attr_means_property}
      [c1_note_attr "I" @{attributes [rule_format]}, c1_note_attr "E" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_mode_means"}
      @{thm redefine_mode_means_property}
      [c1_note_attr "I" @{attributes [rule_format]}, c1_note_attr "E" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_pred_means"}
      @{thm redefine_pred_means_property}
      [c1_note_attr "I" @{attributes [rule_format]}, c1_note_attr "E" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "redefine_pred_means_if1"}
      @{thm redefine_pred_means_if1_property}
      [c1_note_attr "I" @{attributes [rule_format]}, c1_note_attr "E" @{attributes [rule_format]}]
      []
  |> add_miz_ident @{const_name "func_means"}
      @{thm func_means_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_means_if1"}
      @{thm func_means_if1_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_means_if2"}
      @{thm func_means_if2_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_means_if1o"}
      @{thm func_means_if1o_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_means_if2o"}
      @{thm func_means_if2o_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_means_if3"}
      @{thm func_means_if3_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_means_if4"}
      @{thm func_means_if4_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_assume_means"}
      @{thm func_assume_means_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_assume_means_if1"}
      @{thm func_assume_means_if1_property}
      [conj1_ty_func, conj1_note_suffix "_uniq"]
      []
  |> add_miz_ident @{const_name "func_equals"}
      @{thm func_equals_property}
      [conj1_ty_func]
      []
  |> add_miz_ident @{const_name "func_equals_if1"}
      @{thm func_equals_if1_property}
      [conj1_ty_func]
      []
  |> add_miz_ident @{const_name "func_equals_if2"}
      @{thm func_equals_if2_property} [conj1_ty_func] []
  |> add_miz_ident @{const_name "func_equals_if1o"}
      @{thm func_equals_if1o_property}
      [conj1_ty_func]
      []
  |> add_miz_ident @{const_name "func_equals_if2o"}
      @{thm func_equals_if2o_property}
      [conj1_ty_func]
      []
  |> add_miz_ident @{const_name "func_assume_equals"}
      @{thm func_assume_equals_property}
      [conj1_ty_func]
      []
  |> add_miz_ident @{const_name "pred_means"}
      @{thm pred_means_property}
      [conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "pred_means_if1"}
      @{thm pred_means_if1_property}
      [conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "pred_means_if2"}
      @{thm pred_means_if2_property}
      [conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "pred_means_if3"}
      @{thm pred_means_if3_property}
      [conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "pred_antonym"} @{thm pred_antonym_property} [] []
  |> add_miz_ident @{const_name "func_synonym"} @{thm func_synonym_property} [] []
  |> add_miz_ident @{const_name "mode_means"}
      @{thm mode_means_property}
      [conj1_ex, conj1_clus, conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "mode_assume_means"}
      @{thm mode_assume_means_property} 
      [conj1_ex, conj1_clus, conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "mode_means_if1"}
      @{thm mode_means_if1_property} 
      [conj1_ex, conj1_clus, conj1_note_intro "I", conj1_note_elim "E"]
      []
  |> add_miz_ident @{const_name "attr_means"}
      @{thm attr_means_property}
      [conj1_note_intro "I", conj1_note_elim "E", conj1_note_intro "nI"]
      []
  |> add_miz_ident @{const_name "attr_assume_means"}
      @{thm attr_assume_means_property} 
      [conj1_note_intro "I", conj1_note_elim "E", conj1_note_intro "nI"]
      []
  |> add_miz_ident @{const_name "attr_means_if1"}
      @{thm attr_means_if1_property}
      [conj1_note_intro "I", conj1_note_elim "E"]
      []
\<close>

ML \<open>
fun mdef_identify_const ctxt c =
  case Symtab.lookup (Miz_Identify_Data.get (Context.Proof ctxt)) c of
    SOME v => v
  | NONE => raise Fail ("mdef cannot identify constant" ^ c)

fun mdef_identify ctxt (_ $ (_ $ _ $ rhs)) =
  let
    val (c, _) = strip_comb rhs
  in
    case c of
      Const (cn, _) => mdef_identify_const ctxt cn
    | _ => raise Fail "mdef definition not a constant"
  end
| mdef_identify _ _ = raise Fail "mdef cannot identify definition"

fun mdefafterqed retlthy fname thms prop lthy' =
  let
    val (thm, lthy) =
      case retlthy of
        SOME lt => (the_single (Variable.export lthy' lt
          [Assumption.export false lthy' lt (the_single thms)]), lt)
      | NONE => (the_single thms, lthy')

    val (processors, attrs) = snd (mdef_identify lthy prop)
    val (thm, lthy'') = fold (fn p => fn sf => p fname sf) processors (thm, lthy)
  in
    note_suffix fname "" attrs thm lthy''
  end

fun mdef (nameopt, ((decl, lt), defn)) lthy =
  let fun getth prop = fst (mdef_identify lthy prop)
  in mdecl nameopt decl lt defn getth mdefafterqed lthy
  end

fun mdef_cmd (nameopt, ((decl, lt), defn)) lthy =
  let fun getth prop = fst (mdef_identify lthy prop)
  in mdecl_cmd nameopt decl lt defn getth mdefafterqed lthy
  end
\<close>

ML \<open>
val parser =
  (Scan.option
    (Parse.binding --| @{keyword ":"}) --
    (Parse_Spec.constdecl --
      (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
      Parse.prop)) >> (fn (b,t) => mdef (Option.map Binding.name_of b, t))

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword mdef} "Mizar functor" parser
\<close>

ML \<open>
fun do_then ofth _ (thm, lthy) = (ofth OF [thm], lthy)

fun thm_identify_const ctxt c =
  case Symtab.lookup (Miz_Identify_Data.get (Context.Proof ctxt)) c of
    SOME v => v
  | NONE => (@{thm refl}, ([], []))

fun thm_identify ctxt t =
  let val (c, _) = strip_comb t
  in case c of
      Const (cn, _) => thm_identify_const ctxt cn
    | _ => (@{thm refl}, ([], []))
  end

fun mtheorem_cmd scheme generalize name attr lets prop lthy =
  let
    val attr = map (Attrib.check_src lthy) attr
    val as_fs =
      map_filter
        (fn x => SOME ((dest_Free o fst o dest_typing) x) handle TERM _ => NONE) lets
    val c_fs = fold Term.add_frees lets (Term.add_frees prop [])
    val fs = subtract (op=) as_fs c_fs
    val _ =
      if
        not scheme
        andalso filter_out (fn (n, ty) => ty = @{typ Set}
        orelse Variable.is_fixed lthy n) fs <> []
      then warning "Warning: Free variables! Is it a scheme?"
      else ()
    val setfs = filter (fn (n, ty) => ty = @{typ Set} andalso not (Variable.is_fixed lthy n)) fs
    val nosetfs = filter (fn (n, ty) => ty <> @{typ Set} andalso not (Variable.is_fixed lthy n)) fs
    val (assms1, lthy1) = fold_map
      (if scheme then do_var_nofail generalize else do_var generalize) setfs lthy
    val (_, lthy2) =
      fold_map (do_var_nofail generalize) nosetfs lthy1
      handle _ => ([], lthy1)
    val (assms2, lthy3) = fold_map do_lt lets lthy2
    val lthy4 =
      if generalize
      then lthy3
      else #3 (gen_typing_data' lthy3 (prop :: (map Thm.prop_of (flat assms1 @ assms2))))
    fun after_qed thms lthyn = (
      case (if generalize then (lthy, flat thms) else (lthyn, flat thms)) of
        (lthy, [thm]) =>
        let
          val (ofth, (procs, attr2)) = thm_identify lthy (Thm.prop_of thm);
          val thm = if generalize then the_single (Variable.export lthyn lthy [Assumption.export false lthyn lthy thm]) else thm
          (*val _ = tracing (@{make_string} thm)*)
          val thm = if Thm.prop_of ofth <> Thm.prop_of @{thm refl} then ofth OF [thm] else thm;
          val (thm, lthy'') = fold (fn p => fn sf => p (Binding.name_of name) sf) procs (thm, lthy)
          val thm = if scheme orelse generalize then thm else normalize_thm lthy thm; 
          val a = [((name, attr), [([thm], attr2)])];

          val a = Attrib.partial_evaluation lthy a

        in
          Local_Theory.notes a lthy'' |> snd
        end
      | (lthy, thms) =>
          let
            val a = [((name, attr), [(map (normalize_thm lthy) thms, [])])];
            val a = Attrib.partial_evaluation lthy a;
          in
            Local_Theory.notes a lthy |> snd
          end
      )
  in
    Proof.theorem NONE after_qed [[(prop, [])]] lthy4
  end

fun mtheorem scheme (((name, attr), lt), str) lthy =
  let
    val prop = Syntax.read_prop lthy str
    val lt2 = map (Syntax.read_prop lthy) (flat (the_list lt))
  in
    mtheorem_cmd scheme false name attr lt2 prop lthy
  end
\<close>

ML \<open>
Outer_Syntax.local_theory_to_proof @{command_keyword mtheorem} "Mizar theorem"
  ((Parse_Spec.opt_thm_name ":" --
    (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
    Parse.prop) >> (mtheorem false));

Outer_Syntax.local_theory_to_proof @{command_keyword mlemma} "Mizar lemma"
  ((Parse_Spec.opt_thm_name ":" --
    (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
    Parse.prop) >> (mtheorem false));

Outer_Syntax.local_theory_to_proof @{command_keyword mscheme} "Mizar scheme"
  ((Parse_Spec.opt_thm_name ":" --
    (Scan.option ((@{keyword "mlet"} || @{keyword "assumes"}) |-- Parse.list1 Parse.prop)) --
    Parse.prop) >> (mtheorem true));
\<close>

parse_translation \<open>
[(@{syntax_const "_BallML2"},
  let fun tr ctxt
    [((Const (@{syntax_const "_vs"}, _)) $ (v as (_ $ (vv as Free (n, _)) $ _)) $ vs), P] =
      (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
        NONE =>
          raise Fail ("BallML2a: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
      | SOME D =>
          Syntax.const @{const_syntax Ball} $ D $ (Syntax_Trans.abs_tr [v, tr ctxt [vs, P]])
      )
  | tr ctxt [(v as (_ $ (vv as Free (n, _)) $ _)), P] =
      (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
        NONE =>
          raise Fail ("BallML2b: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
      | SOME D =>
          Syntax.const @{const_syntax Ball} $ D $ (Syntax_Trans.abs_tr [v, P])
      )
  in tr end)]
\<close>

parse_translation \<open> [(@{syntax_const "_BexML2"},
  let fun tr ctxt
    [((Const (@{syntax_const "_vs"}, _)) $ (v as (_ $ (vv as Free (n, _)) $ _)) $ vs), P] =
      (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
        NONE =>
          raise Fail ("BexML2a: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
      | SOME D =>
          Syntax.const @{const_syntax Bex} $ D $ (Syntax_Trans.abs_tr [v, tr ctxt [vs, P]])
      )
  | tr ctxt [(v as (_ $ (vv as Free (n, _)) $ _)), P] =
      (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
        NONE =>
          raise Fail ("BexML2b: Variable " ^ n ^ " \<not> reserved and 'being' \<not> given!")
      | SOME D =>
        Syntax.const @{const_syntax Bex} $ D $ (Syntax_Trans.abs_tr [v, P]))
  in tr end)]
\<close>

end
