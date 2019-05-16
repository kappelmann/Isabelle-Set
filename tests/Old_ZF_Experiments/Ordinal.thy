(*  Title:      ZF/Ordinal.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Transitive Sets and Ordinals\<close>

theory Ordinal imports WF Bool Equalities begin

definition
  Memrel        :: "i=>i"  where
    "Memrel(A)   == {z\<in>A*A . \<exists>x y. z=<x,y> & x\<in>y }"

definition
  Transset  :: "i=>o"  where
    "Transset(i) == \<forall>x\<in>i. x<=i"

definition
  Ord  :: "i=>o"  where
    "Ord(i)      == Transset(i) & (\<forall>x\<in>i. Transset(x))"

definition
  lt        :: "[i,i] => o"  (infixl "<" 50)   (*less-than on ordinals*)  where
    "i<j         == i\<in>j & Ord(j)"

definition
  Limit         :: "i=>o"  where
    "Limit(i)    == Ord(i) & {}<i & (\<forall>y. y<i \<longrightarrow> succ(y)<i)"

abbreviation
  le  (infixl "\<le>" 50) where
  "x \<le> y == x < succ(y)"


subsection\<open>Rules for Transset\<close>

subsubsection\<open>Three Neat Characterisations of Transset\<close>

lemma Transset_iff_Pow: "Transset(A) <-> A<=Pow(A)"
by (unfold Transset_def, blast)

lemma Transset_iff_Union_succ: "Transset(A) <-> \<Union>(succ(A)) = A"
apply (unfold Transset_def)
apply (blast elim!: equalityE)
done

lemma Transset_iff_Union_subset: "Transset(A) <-> \<Union>(A) \<subseteq> A"
by (unfold Transset_def, blast)

subsubsection\<open>Consequences of Downwards Closure\<close>

lemma Transset_doubleton_D:
    "[| Transset(C); {a,b}\<in> C |] ==> a\<in>C & b\<in>C"
by (unfold Transset_def, blast)

lemma Transset_Pair_D:
    "[| Transset(C); <a,b>\<in>C |] ==> a\<in>C & b\<in>C"
apply (simp add: Pair_def)
apply (blast dest: Transset_doubleton_D)
done

lemma Transset_includes_domain:
    "[| Transset(C); A*B \<subseteq> C; b \<in> B |] ==> A \<subseteq> C"
by (blast dest: Transset_Pair_D)

lemma Transset_includes_range:
    "[| Transset(C); A*B \<subseteq> C; a \<in> A |] ==> B \<subseteq> C"
by (blast dest: Transset_Pair_D)

subsubsection\<open>Closure Properties\<close>

lemma Transset_0: "Transset({})"
by (unfold Transset_def, blast)

lemma Transset_Un:
    "[| Transset(i);  Transset(j) |] ==> Transset(i \<union> j)"
by (unfold Transset_def, blast)

lemma Transset_Int:
    "[| Transset(i);  Transset(j) |] ==> Transset(i \<inter> j)"
by (unfold Transset_def, blast)

lemma Transset_succ: "Transset(i) ==> Transset(succ(i))"
by (unfold Transset_def, blast)

lemma Transset_Pow: "Transset(i) ==> Transset(Pow(i))"
by (unfold Transset_def, blast)

lemma Transset_Union: "Transset(A) ==> Transset(\<Union>(A))"
by (unfold Transset_def, blast)

lemma Transset_Union_family:
    "[| !!i. i\<in>A ==> Transset(i) |] ==> Transset(\<Union>(A))"
by (unfold Transset_def, blast)

lemma Transset_Inter_family:
    "[| !!i. i\<in>A ==> Transset(i) |] ==> Transset(\<Inter>(A))"
by (unfold Inter_def Transset_def, blast)

lemma Transset_UN:
     "(!!x. x \<in> A ==> Transset(B(x))) ==> Transset (\<Union>x\<in>A. B(x))"
by (rule Transset_Union_family, auto)

lemma Transset_INT:
     "(!!x. x \<in> A ==> Transset(B(x))) ==> Transset (\<Inter>x\<in>A. B(x))"
by (rule Transset_Inter_family, auto)


subsection\<open>Lemmas for Ordinals\<close>

lemma OrdI:
    "[| Transset(i);  !!x. x\<in>i ==> Transset(x) |]  ==>  Ord(i)"
by (simp add: Ord_def)

lemma Ord_is_Transset: "Ord(i) ==> Transset(i)"
by (simp add: Ord_def)

lemma Ord_contains_Transset:
    "[| Ord(i);  j\<in>i |] ==> Transset(j) "
by (unfold Ord_def, blast)


lemma Ord_in_Ord: "[| Ord(i);  j\<in>i |] ==> Ord(j)"
by (unfold Ord_def Transset_def, blast)

(*suitable for rewriting PROVIDED i has been fixed*)
lemma Ord_in_Ord': "[| j\<in>i; Ord(i) |] ==> Ord(j)"
by (blast intro: Ord_in_Ord)

(* Ord(succ(j)) ==> Ord(j) *)
lemmas Ord_succD = Ord_in_Ord [OF _ succI1]

lemma Ord_subset_Ord: "[| Ord(i);  Transset(j);  j<=i |] ==> Ord(j)"
by (simp add: Ord_def Transset_def, blast)

lemma OrdmemD: "[| j\<in>i;  Ord(i) |] ==> j<=i"
by (unfold Ord_def Transset_def, blast)

lemma Ord_trans: "[| i\<in>j;  j\<in>k;  Ord(k) |] ==> i\<in>k"
by (blast dest: OrdmemD)

lemma Ord_succ_subsetI: "[| i\<in>j;  Ord(j) |] ==> succ(i) \<subseteq> j"
by (blast dest: OrdmemD)


subsection\<open>The Construction of Ordinals: 0, succ, Union\<close>

lemma Ord_0 [iff,TC]: "Ord({})"
by (blast intro: OrdI Transset_0)

lemma Ord_succ [TC]: "Ord(i) ==> Ord(succ(i))"
by (blast intro: OrdI Transset_succ Ord_is_Transset Ord_contains_Transset)

lemmas Ord_1 = Ord_0 [THEN Ord_succ]

lemma Ord_succ_iff [iff]: "Ord(succ(i)) <-> Ord(i)"
by (blast intro: Ord_succ dest!: Ord_succD)

lemma Ord_Un [intro,simp,TC]: "[| Ord(i); Ord(j) |] ==> Ord(i \<union> j)"
apply (unfold Ord_def)
apply (blast intro!: Transset_Un)
done

lemma Ord_Int [TC]: "[| Ord(i); Ord(j) |] ==> Ord(i \<inter> j)"
apply (unfold Ord_def)
apply (blast intro!: Transset_Int)
done

text\<open>There is no set of all ordinals, for then it would contain itself\<close>
lemma ON_class: "~ (\<forall>i. i\<in>X <-> Ord(i))"
proof (rule notI)
  assume X: "\<forall>i. i \<in> X \<longleftrightarrow> Ord(i)"
  have "\<forall>x y. x\<in>X \<longrightarrow> y\<in>x \<longrightarrow> y\<in>X"
    by (simp add: X, blast intro: Ord_in_Ord)
  hence "Transset(X)"
     by (auto simp add: Transset_def)
  moreover have "\<And>x. x \<in> X \<Longrightarrow> Transset(x)"
     by (simp add: X Ord_def)
  ultimately have "Ord(X)" by (rule OrdI)
  hence "X \<in> X" by (simp add: X)
  thus "False" by (rule mem_irrefl)
qed

subsection\<open>< is 'less Than' for Ordinals\<close>

lemma ltI: "[| i\<in>j;  Ord(j) |] ==> i<j"
by (unfold lt_def, blast)

lemma ltE:
    "[| i<j;  [| i\<in>j;  Ord(i);  Ord(j) |] ==> P |] ==> P"
apply (unfold lt_def)
apply (blast intro: Ord_in_Ord)
done

lemma ltD: "i<j ==> i\<in>j"
by (erule ltE, assumption)

lemma not_lt0 [simp]: "~ i<{}"
by (unfold lt_def, blast)

lemma lt_Ord: "j<i ==> Ord(j)"
by (erule ltE, assumption)

lemma lt_Ord2: "j<i ==> Ord(i)"
by (erule ltE, assumption)

(* @{term"ja \<le> j ==> Ord(j)"} *)
lemmas le_Ord2 = lt_Ord2 [THEN Ord_succD]

(* i<{} ==> R *)
lemmas lt0E = not_lt0 [THEN notE, elim!]

lemma lt_trans [trans]: "[| i<j;  j<k |] ==> i<k"
by (blast intro!: ltI elim!: ltE intro: Ord_trans)

lemma lt_not_sym: "i<j ==> ~ (j<i)"
apply (unfold lt_def)
apply (blast elim: mem_asym)
done

(* [| i<j;  ~P ==> j<i |] ==> P *)
lemmas lt_asym = lt_not_sym [THEN swap]

lemma lt_irrefl [elim!]: "i<i ==> P"
by (blast intro: lt_asym)

lemma lt_not_refl: "~ i<i"
apply (rule notI)
apply (erule lt_irrefl)
done


text\<open>Recall that  @{term"i \<le> j"}  abbreviates  @{term"i<succ(j)"} !!\<close>

lemma le_iff: "i \<le> j <-> i<j | (i=j & Ord(j))"
by (unfold lt_def, blast)

(*Equivalently, i<j ==> i < succ(j)*)
lemma leI: "i<j ==> i \<le> j"
by (simp add: le_iff)

lemma le_eqI: "[| i=j;  Ord(j) |] ==> i \<le> j"
by (simp add: le_iff)

lemmas le_refl = refl [THEN le_eqI]

lemma le_refl_iff [iff]: "i \<le> i <-> Ord(i)"
by (simp (no_asm_simp) add: lt_not_refl le_iff)

lemma leCI: "(~ (i=j & Ord(j)) ==> i<j) ==> i \<le> j"
by (simp add: le_iff, blast)

lemma leE:
    "[| i \<le> j;  i<j ==> P;  [| i=j;  Ord(j) |] ==> P |] ==> P"
by (simp add: le_iff, blast)

lemma le_anti_sym: "[| i \<le> j;  j \<le> i |] ==> i=j"
apply (simp add: le_iff)
apply (blast elim: lt_asym)
done

lemma le0_iff [simp]: "i \<le> {} <-> i={}"
by (blast elim!: leE)

lemmas le0D = le0_iff [THEN iffD1, dest!]

subsection\<open>Natural Deduction Rules for Memrel\<close>

(*The lemmas MemrelI/E give better speed than [iff] here*)
lemma Memrel_iff [simp]: "<a,b> \<in> Memrel(A) <-> a\<in>b & a\<in>A & b\<in>A"
by (unfold Memrel_def, blast)

lemma MemrelI [intro!]: "[| a \<in> b;  a \<in> A;  b \<in> A |] ==> <a,b> \<in> Memrel(A)"
by auto

lemma MemrelE [elim!]:
    "[| <a,b> \<in> Memrel(A);
        [| a \<in> A;  b \<in> A;  a\<in>b |]  ==> P |]
     ==> P"
by auto

lemma Memrel_type: "Memrel(A) \<subseteq> A*A"
by (unfold Memrel_def, blast)

lemma Memrel_mono: "A<=B ==> Memrel(A) \<subseteq> Memrel(B)"
by (unfold Memrel_def, blast)

lemma Memrel_0 [simp]: "Memrel({}) = {}"
by (unfold Memrel_def, blast)

lemma Memrel_1 [simp]: "Memrel(1) = {}"
by (unfold Memrel_def, blast)

lemma relation_Memrel: "relation(Memrel(A))"
by (simp add: relation_def Memrel_def)

(*The membership relation (as a set) is well-founded.
  Proof idea: show A<=B by applying the foundation axiom to A-B *)
lemma wf_Memrel: "wf(Memrel(A))"
apply (unfold wf_def)
apply (rule foundation [THEN disjE, THEN allI], erule disjI1, blast)
done

text\<open>The premise @{term "Ord(i)"} does not suffice.\<close>
lemma trans_Memrel:
    "Ord(i) ==> trans(Memrel(i))"
by (unfold Ord_def Transset_def trans_def, blast)

text\<open>However, the following premise is strong enough.\<close>
lemma Transset_trans_Memrel:
    "\<forall>j\<in>i. Transset(j) ==> trans(Memrel(i))"
by (unfold Transset_def trans_def, blast)

(*If Transset(A) then Memrel(A) internalizes the membership relation below A*)
lemma Transset_Memrel_iff:
    "Transset(A) ==> <a,b> \<in> Memrel(A) <-> a\<in>b & b\<in>A"
by (unfold Transset_def, blast)


subsection\<open>Transfinite Induction\<close>

(*Epsilon induction over a transitive set*)
lemma Transset_induct:
    "[| i \<in> k;  Transset(k);
        !!x.[| x \<in> k;  \<forall>y\<in>x. P(y) |] ==> P(x) |]
     ==>  P(i)"
apply (simp add: Transset_def)
apply (erule wf_Memrel [THEN wf_induct2], blast+)
done

(*Induction over an ordinal*)
lemmas Ord_induct [consumes 2] = Transset_induct [rule_format, OF _ Ord_is_Transset]

(*Induction over the class of ordinals -- a useful corollary of Ord_induct*)

lemma trans_induct [rule_format, consumes 1, case_names step]:
    "[| Ord(i);
        !!x.[| Ord(x);  \<forall>y\<in>x. P(y) |] ==> P(x) |]
     ==>  P(i)"
apply (rule Ord_succ [THEN succI1 [THEN Ord_induct]], assumption)
apply (blast intro: Ord_succ [THEN Ord_in_Ord])
done


section\<open>Fundamental properties of the epsilon ordering (< on ordinals)\<close>


subsubsection\<open>Proving That < is a Linear Ordering on the Ordinals\<close>

lemma Ord_linear:
     "Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> i\<in>j | i=j | j\<in>i"
proof (induct i arbitrary: j rule: trans_induct)
  case (step i)
  note step_i = step
  show ?case using \<open>Ord(j)\<close>
    proof (induct j rule: trans_induct)
      case (step j)
      thus ?case using step_i
        by (blast dest: Ord_trans)
    qed
qed

text\<open>The trichotomy law for ordinals\<close>
lemma Ord_linear_lt:
 assumes o: "Ord(i)" "Ord(j)"
 obtains (lt) "i<j" | (eq) "i=j" | (gt) "j<i"
apply (simp add: lt_def)
apply (rule_tac i1=i and j1=j in Ord_linear [THEN disjE])
apply (blast intro: o)+
done

lemma Ord_linear2:
 assumes o: "Ord(i)" "Ord(j)"
 obtains (lt) "i<j" | (ge) "j \<le> i"
apply (rule_tac i = i and j = j in Ord_linear_lt)
apply (blast intro: leI le_eqI sym o) +
done

lemma Ord_linear_le:
 assumes o: "Ord(i)" "Ord(j)"
 obtains (le) "i \<le> j" | (ge) "j \<le> i"
apply (rule_tac i = i and j = j in Ord_linear_lt)
apply (blast intro: leI le_eqI o) +
done

lemma le_imp_not_lt: "j \<le> i ==> ~ i<j"
by (blast elim!: leE elim: lt_asym)

lemma not_lt_imp_le: "[| ~ i<j;  Ord(i);  Ord(j) |] ==> j \<le> i"
by (rule_tac i = i and j = j in Ord_linear2, auto)


subsubsection \<open>Some Rewrite Rules for \<open><\<close>, \<open>\<le>\<close>\<close>

lemma Ord_mem_iff_lt: "Ord(j) ==> i\<in>j <-> i<j"
by (unfold lt_def, blast)

lemma not_lt_iff_le: "[| Ord(i);  Ord(j) |] ==> ~ i<j <-> j \<le> i"
by (blast dest: le_imp_not_lt not_lt_imp_le)

lemma not_le_iff_lt: "[| Ord(i);  Ord(j) |] ==> ~ i \<le> j <-> j<i"
by (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym])

(*This is identical to {}<succ(i) *)
lemma Ord_0_le: "Ord(i) ==> {} \<le> i"
by (erule not_lt_iff_le [THEN iffD1], auto)

lemma Ord_0_lt: "[| Ord(i);  i\<noteq>{} |] ==> {}<i"
apply (erule not_le_iff_lt [THEN iffD1])
apply (rule Ord_0, blast)
done

lemma Ord_0_lt_iff: "Ord(i) ==> i\<noteq>{} <-> {}<i"
by (blast intro: Ord_0_lt)


subsection\<open>Results about Less-Than or Equals\<close>

(** For ordinals, @{term"j\<subseteq>i"} implies @{term"j \<le> i"} (less-than or equals) **)

lemma zero_le_succ_iff [iff]: "{} \<le> succ(x) <-> Ord(x)"
by (blast intro: Ord_0_le elim: ltE)

lemma subset_imp_le: "[| j<=i;  Ord(i);  Ord(j) |] ==> j \<le> i"
apply (rule not_lt_iff_le [THEN iffD1], assumption+)
apply (blast elim: ltE mem_irrefl)
done

lemma le_imp_subset: "i \<le> j ==> i<=j"
by (blast dest: OrdmemD elim: ltE leE)

lemma le_subset_iff: "j \<le> i <-> j<=i & Ord(i) & Ord(j)"
by (blast dest: subset_imp_le le_imp_subset elim: ltE)

lemma le_succ_iff: "i \<le> succ(j) <-> i \<le> j | i=succ(j) & Ord(i)"
apply (simp (no_asm) add: le_iff)
apply blast
done

(*Just a variant of subset_imp_le*)
lemma all_lt_imp_le: "[| Ord(i);  Ord(j);  !!x. x<j ==> x<i |] ==> j \<le> i"
by (blast intro: not_lt_imp_le dest: lt_irrefl)

subsubsection\<open>Transitivity Laws\<close>

lemma lt_trans1: "[| i \<le> j;  j<k |] ==> i<k"
by (blast elim!: leE intro: lt_trans)

lemma lt_trans2: "[| i<j;  j \<le> k |] ==> i<k"
by (blast elim!: leE intro: lt_trans)

lemma le_trans: "[| i \<le> j;  j \<le> k |] ==> i \<le> k"
by (blast intro: lt_trans1)

lemma succ_leI: "i<j ==> succ(i) \<le> j"
apply (rule not_lt_iff_le [THEN iffD1])
apply (blast elim: ltE leE lt_asym)+
done

(*Identical to  succ(i) < succ(j) ==> i<j  *)
lemma succ_leE: "succ(i) \<le> j ==> i<j"
apply (rule not_le_iff_lt [THEN iffD1])
apply (blast elim: ltE leE lt_asym)+
done

lemma succ_le_iff [iff]: "succ(i) \<le> j <-> i<j"
by (blast intro: succ_leI succ_leE)

lemma succ_le_imp_le: "succ(i) \<le> succ(j) ==> i \<le> j"
by (blast dest!: succ_leE)

lemma lt_subset_trans: "[| i \<subseteq> j;  j<k;  Ord(i) |] ==> i<k"
apply (rule subset_imp_le [THEN lt_trans1])
apply (blast intro: elim: ltE) +
done

lemma lt_imp_0_lt: "j<i ==> {}<i"
by (blast intro: lt_trans1 Ord_0_le [OF lt_Ord])

lemma succ_lt_iff: "succ(i) < j <-> i<j & succ(i) \<noteq> j"
apply auto
apply (blast intro: lt_trans le_refl dest: lt_Ord)
apply (frule lt_Ord)
apply (rule not_le_iff_lt [THEN iffD1])
  apply (blast intro: lt_Ord2)
 apply blast
apply (simp add: lt_Ord lt_Ord2 le_iff)
apply (blast dest: lt_asym)
done

lemma Ord_succ_mem_iff: "Ord(j) ==> succ(i) \<in> succ(j) <-> i\<in>j"
apply (insert succ_le_iff [of i j])
apply (simp add: lt_def)
done

subsubsection\<open>Union and Intersection\<close>

lemma Un_upper1_le: "[| Ord(i); Ord(j) |] ==> i \<le> i \<union> j"
by (rule Un_upper1 [THEN subset_imp_le], auto)

lemma Un_upper2_le: "[| Ord(i); Ord(j) |] ==> j \<le> i \<union> j"
by (rule Un_upper2 [THEN subset_imp_le], auto)

(*Replacing k by succ(k') yields the similar rule for le!*)
lemma Un_least_lt: "[| i<k;  j<k |] ==> i \<union> j < k"
apply (rule_tac i = i and j = j in Ord_linear_le)
apply (auto simp add: Un_commute le_subset_iff subset_Un_iff lt_Ord)
done

lemma Un_least_lt_iff: "[| Ord(i); Ord(j) |] ==> i \<union> j < k  <->  i<k & j<k"
apply (safe intro!: Un_least_lt)
apply (rule_tac [2] Un_upper2_le [THEN lt_trans1])
apply (rule Un_upper1_le [THEN lt_trans1], auto)
done

lemma Un_least_mem_iff:
    "[| Ord(i); Ord(j); Ord(k) |] ==> i \<union> j \<in> k  <->  i\<in>k & j\<in>k"
apply (insert Un_least_lt_iff [of i j k])
apply (simp add: lt_def)
done

(*Replacing k by succ(k') yields the similar rule for le!*)
lemma Int_greatest_lt: "[| i<k;  j<k |] ==> i \<inter> j < k"
apply (rule_tac i = i and j = j in Ord_linear_le)
apply (auto simp add: Int_commute le_subset_iff subset_Int_iff lt_Ord)
done

lemma Ord_Un_if:
     "[| Ord(i); Ord(j) |] ==> i \<union> j = (if j<i then i else j)"
by (simp add: not_lt_iff_le le_imp_subset leI
              subset_Un_iff [symmetric]  subset_Un_iff2 [symmetric])

lemma succ_Un_distrib:
     "[| Ord(i); Ord(j) |] ==> succ(i \<union> j) = succ(i) \<union> succ(j)"
by (simp add: Ord_Un_if lt_Ord le_Ord2)

lemma lt_Un_iff:
     "[| Ord(i); Ord(j) |] ==> k < i \<union> j <-> k < i | k < j"
apply (simp add: Ord_Un_if not_lt_iff_le)
apply (blast intro: leI lt_trans2)+
done

lemma le_Un_iff:
     "[| Ord(i); Ord(j) |] ==> k \<le> i \<union> j <-> k \<le> i | k \<le> j"
by (simp add: succ_Un_distrib lt_Un_iff [symmetric])

lemma Un_upper1_lt: "[|k < i; Ord(j)|] ==> k < i \<union> j"
by (simp add: lt_Un_iff lt_Ord2)

lemma Un_upper2_lt: "[|k < j; Ord(i)|] ==> k < i \<union> j"
by (simp add: lt_Un_iff lt_Ord2)

(*See also Transset_iff_Union_succ*)
lemma Ord_Union_succ_eq: "Ord(i) ==> \<Union>(succ(i)) = i"
by (blast intro: Ord_trans)


subsection\<open>Results about Limits\<close>

lemma Ord_Union [intro,simp,TC]: "[| !!i. i\<in>A ==> Ord(i) |] ==> Ord(\<Union>(A))"
apply (rule Ord_is_Transset [THEN Transset_Union_family, THEN OrdI])
apply (blast intro: Ord_contains_Transset)+
done

lemma Ord_UN [intro,simp,TC]:
     "[| !!x. x\<in>A ==> Ord(B(x)) |] ==> Ord(\<Union>x\<in>A. B(x))"
by (rule Ord_Union, blast)

lemma Ord_Inter [intro,simp,TC]:
    "[| !!i. i\<in>A ==> Ord(i) |] ==> Ord(\<Inter>(A))"
apply (rule Transset_Inter_family [THEN OrdI])
apply (blast intro: Ord_is_Transset)
apply (simp add: Inter_def)
apply (blast intro: Ord_contains_Transset)
done

lemma Ord_INT [intro,simp,TC]:
    "[| !!x. x\<in>A ==> Ord(B(x)) |] ==> Ord(\<Inter>x\<in>A. B(x))"
by (rule Ord_Inter, blast)


(* No < version of this theorem: consider that @{term"(\<Union>i\<in>nat.i)=nat"}! *)
lemma UN_least_le:
    "[| Ord(i);  !!x. x\<in>A ==> b(x) \<le> i |] ==> (\<Union>x\<in>A. b(x)) \<le> i"
apply (rule le_imp_subset [THEN UN_least, THEN subset_imp_le])
apply (blast intro: Ord_UN elim: ltE)+
done

lemma UN_succ_least_lt:
    "[| j<i;  !!x. x\<in>A ==> b(x)<j |] ==> (\<Union>x\<in>A. succ(b(x))) < i"
apply (rule ltE, assumption)
apply (rule UN_least_le [THEN lt_trans2])
apply (blast intro: succ_leI)+
done

lemma UN_upper_lt:
     "[| a\<in>A;  i < b(a);  Ord(\<Union>x\<in>A. b(x)) |] ==> i < (\<Union>x\<in>A. b(x))"
by (unfold lt_def, blast)

lemma UN_upper_le:
     "[| a \<in> A;  i \<le> b(a);  Ord(\<Union>x\<in>A. b(x)) |] ==> i \<le> (\<Union>x\<in>A. b(x))"
apply (frule ltD)
apply (rule le_imp_subset [THEN subset_trans, THEN subset_imp_le])
apply (blast intro: lt_Ord UN_upper)+
done

lemma lt_Union_iff: "\<forall>i\<in>A. Ord(i) ==> (j < \<Union>(A)) <-> (\<exists>i\<in>A. j<i)"
by (auto simp: lt_def Ord_Union)

lemma Union_upper_le:
     "[| j \<in> J;  i\<le>j;  Ord(\<Union>(J)) |] ==> i \<le> \<Union>J"
apply (subst Union_eq_UN)
apply (rule UN_upper_le, auto)
done

lemma le_implies_UN_le_UN:
    "[| !!x. x\<in>A ==> c(x) \<le> d(x) |] ==> (\<Union>x\<in>A. c(x)) \<le> (\<Union>x\<in>A. d(x))"
apply (rule UN_least_le)
apply (rule_tac [2] UN_upper_le)
apply (blast intro: Ord_UN le_Ord2)+
done

lemma Ord_equality: "Ord(i) ==> (\<Union>y\<in>i. succ(y)) = i"
by (blast intro: Ord_trans)

(*Holds for all transitive sets, not just ordinals*)
lemma Ord_Union_subset: "Ord(i) ==> \<Union>(i) \<subseteq> i"
by (blast intro: Ord_trans)


subsection\<open>Limit Ordinals -- General Properties\<close>

lemma Limit_Union_eq: "Limit(i) ==> \<Union>(i) = i"
apply (unfold Limit_def)
apply (fast intro!: ltI elim!: ltE elim: Ord_trans)
done

lemma Limit_is_Ord: "Limit(i) ==> Ord(i)"
apply (unfold Limit_def)
apply (erule conjunct1)
done

lemma Limit_has_0: "Limit(i) ==> {} < i"
apply (unfold Limit_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma Limit_nonzero: "Limit(i) ==> i \<noteq> {}"
by (drule Limit_has_0, blast)

lemma Limit_has_succ: "[| Limit(i);  j<i |] ==> succ(j) < i"
by (unfold Limit_def, blast)

lemma Limit_succ_lt_iff [simp]: "Limit(i) ==> succ(j) < i <-> (j<i)"
apply (safe intro!: Limit_has_succ)
apply (frule lt_Ord)
apply (blast intro: lt_trans)
done

lemma zero_not_Limit [iff]: "~ Limit({})"
by (simp add: Limit_def)

lemma Limit_has_1: "Limit(i) ==> 1 < i"
by (blast intro: Limit_has_0 Limit_has_succ)

lemma increasing_LimitI: "[| {}<l; \<forall>x\<in>l. \<exists>y\<in>l. x<y |] ==> Limit(l)"
apply (unfold Limit_def, simp add: lt_Ord2, clarify)
apply (drule_tac i=y in ltD)
apply (blast intro: lt_trans1 [OF _ ltI] lt_Ord2)
done

lemma non_succ_LimitI:
  assumes i: "{}<i" and nsucc: "\<And>y. succ(y) \<noteq> i"
  shows "Limit(i)"
proof -
  have Oi: "Ord(i)" using i by (simp add: lt_def)
  { fix y
    assume yi: "y<i"
    hence Osy: "Ord(succ(y))" by (simp add: lt_Ord Ord_succ)
    have "~ i \<le> y" using yi by (blast dest: le_imp_not_lt)
    hence "succ(y) < i" using nsucc [of y]
      by (blast intro: Ord_linear_lt [OF Osy Oi]) }
  thus ?thesis using i Oi by (auto simp add: Limit_def)
qed

lemma succ_LimitE [elim!]: "Limit(succ(i)) ==> P"
apply (rule lt_irrefl)
apply (rule Limit_has_succ, assumption)
apply (erule Limit_is_Ord [THEN Ord_succD, THEN le_refl])
done

lemma not_succ_Limit [simp]: "~ Limit(succ(i))"
by blast

lemma Limit_le_succD: "[| Limit(i);  i \<le> succ(j) |] ==> i \<le> j"
by (blast elim!: leE)


subsubsection\<open>Traditional 3-Way Case Analysis on Ordinals\<close>

lemma Ord_cases_disj: "Ord(i) ==> i={} | (\<exists>j. Ord(j) & i=succ(j)) | Limit(i)"
by (blast intro!: non_succ_LimitI Ord_0_lt)

lemma Ord_cases:
 assumes i: "Ord(i)"
 obtains ("0") "i={}" | (succ) j where "Ord(j)" "i=succ(j)" | (limit) "Limit(i)"
by (insert Ord_cases_disj [OF i], auto)

lemma trans_induct3_raw:
     "[| Ord(i);
         P({});
         !!x. [| Ord(x);  P(x) |] ==> P(succ(x));
         !!x. [| Limit(x);  \<forall>y\<in>x. P(y) |] ==> P(x)
      |] ==> P(i)"
apply (erule trans_induct)
apply (erule Ord_cases, blast+)
done

lemmas trans_induct3 = trans_induct3_raw [rule_format, case_names 0 succ limit, consumes 1]

text\<open>A set of ordinals is either empty, contains its own union, or its
union is a limit ordinal.\<close>

lemma Union_le: "[| !!x. x\<in>I ==> x\<le>j; Ord(j) |] ==> \<Union>(I) \<le> j"
  by (auto simp add: le_subset_iff Union_least)

lemma Ord_set_cases:
  assumes I: "\<forall>i\<in>I. Ord(i)"
  shows "I={} \<or> \<Union>(I) \<in> I \<or> (\<Union>(I) \<notin> I \<and> Limit(\<Union>(I)))"
proof (cases "\<Union>(I)" rule: Ord_cases)
  show "Ord(\<Union>I)" using I by (blast intro: Ord_Union)
next
  assume "\<Union>I = {}" thus ?thesis by (simp, blast intro: subst_elem)
next
  fix j
  assume j: "Ord(j)" and UIj:"\<Union>(I) = succ(j)"
  { assume "\<forall>i\<in>I. i\<le>j"
    hence "\<Union>(I) \<le> j"
      by (simp add: Union_le j)
    hence False
      by (simp add: UIj lt_not_refl) }
  then obtain i where i: "i \<in> I" "succ(j) \<le> i" using I j
    by (atomize, auto simp add: not_le_iff_lt)
  have "\<Union>(I) \<le> succ(j)" using UIj j by auto
  hence "i \<le> succ(j)" using i
    by (simp add: le_subset_iff Union_subset_iff)
  hence "succ(j) = i" using i
    by (blast intro: le_anti_sym)
  hence "succ(j) \<in> I" by (simp add: i)
  thus ?thesis by (simp add: UIj)
next
  assume "Limit(\<Union>I)" thus ?thesis by auto
qed

text\<open>If the union of a set of ordinals is a successor, then it is an element of that set.\<close>
lemma Ord_Union_eq_succD: "[|\<forall>x\<in>X. Ord(x);  \<Union>X = succ(j)|] ==> succ(j) \<in> X"
  by (drule Ord_set_cases, auto)

lemma Limit_Union [rule_format]: "[| I \<noteq> {};  \<forall>i\<in>I. Limit(i) |] ==> Limit(\<Union>I)"
apply (simp add: Limit_def lt_def)
apply (blast intro!: equalityI)
done

end
