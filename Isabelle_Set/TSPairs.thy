\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Set-Theoretic Pair Type (\<Sum>-type)\<close>
theory TSPairs
  imports
    TSBasics
    HOTG.HOTG_Pairs
begin

definition "set_dep_pair_type A B \<equiv> \<Sum>x : of_type A. of_type (B x)"
adhoc_overloading dep_pair \<rightleftharpoons> set_dep_pair_type

definition "set_pair_type A B \<equiv> of_type A \<times> of_type B"
adhoc_overloading pair \<rightleftharpoons> set_pair_type

lemma set_dep_pair_type_eq_set_dep_pair_pred [simp]:
  "(\<Sum>x : A. B x) = \<Sum>x : of_type A. of_type (B x)"
  unfolding set_dep_pair_type_def by simp

lemma set_dep_pair_type_eq_set_dep_pair_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "\<And>x. B' x \<equiv> of_type (B x)"
  shows "\<Sum>x : A. B x \<equiv> \<Sum>x : A'. B' x"
  using assms by simp

lemma set_dep_pair_type_iff_set_dep_pair_pred [iff]:
  "(\<Sum>x : A. B x) p \<longleftrightarrow> (\<Sum>x : of_type A. of_type (B x)) p"
  by simp

lemma set_pair_type_eq_set_pair_pred [simp]: "(A \<times> B) = (of_type A \<times> of_type B)"
  unfolding set_pair_type_def by simp

lemma set_pair_type_eq_set_pair_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "B' \<equiv> of_type B"
  shows "A \<times> B \<equiv> A' \<times> B'"
  using assms by simp

lemma set_pair_type_iff_set_pair_pred [iff]: "(A \<times> B) p \<longleftrightarrow> (of_type A \<times> of_type B) p"
  by simp

lemma set_set_dep_pair_set_type [type]:
  "dep_pair \<Ztypecolon> Subset A \<Rightarrow> ((x : Element A) \<Rightarrow> Subset (B x)) \<Rightarrow> Subset (\<Sum>x : A. B x)"
  by unfold_types (auto simp: of_type_type_eq_self)

lemma set_set_pair_set_type [type]: "(\<times>) \<Ztypecolon> Subset A \<Rightarrow> Subset B \<Rightarrow> Subset (A \<times> B)"
  by unfold_types auto


definition [typedef]: "Dep_pair (A :: set type) B \<equiv> type (\<Sum>x : A. B x)"
adhoc_overloading dep_pair \<rightleftharpoons> Dep_pair

lemma of_type_Dep_pair_eq_set_dep_pair_type [type_to_HOL_simp]:
  "of_type (\<Sum>x : A. B x) = (\<Sum>x : A. B x)"
  unfolding Dep_pair_def type_to_HOL_simp by simp

soft_type_translation
  "(\<Sum>x : (A :: set type). B x) p" \<rightleftharpoons> "p \<Ztypecolon> (\<Sum>x : A. B x)"
  unfolding type_to_HOL_simp by simp

lemma mem_of_dep_pairs_eq_of_type_Dep_pair_Element:
  "mem_of (\<Sum>x : A. B x) = of_type (\<Sum>x : Element A. Element (B x))"
  unfolding type_to_HOL_simp by auto

soft_type_translation
  "p \<in> \<Sum>x : A. B x" \<rightleftharpoons> "p \<Ztypecolon> \<Sum>x : Element A. Element (B x)"
  using mem_of_dep_pairs_eq_of_type_Dep_pair_Element by simp_all

definition [typedef]: "Pair (A :: set type) B \<equiv> type (A \<times> B)"
adhoc_overloading pair \<rightleftharpoons> Pair

lemma of_type_Pair_eq_set_pair_type [type_to_HOL_simp]: "of_type (A \<times> B) = (A \<times> B)"
  unfolding Pair_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: set type) \<times> B) p" \<rightleftharpoons> "p \<Ztypecolon> (A \<times> B)"
  unfolding type_to_HOL_simp by simp

lemma mem_of_pairs_eq_of_type_Pair_Element:
  "mem_of (A \<times> B) = of_type (Element A \<times> Element B)"
  unfolding type_to_HOL_simp by auto

soft_type_translation
  "p \<in> (A \<times> B)" \<rightleftharpoons> "p \<Ztypecolon> Element A \<times> Element B"
  using mem_of_pairs_eq_of_type_Pair_Element by simp_all

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
    [[ucombine add = \<open>Standard_Unification_Combine.eunif_data (K Higher_Order_Unification.unify)
      (Standard_Unification_Combine.default_metadata \<^binding>\<open>ho_unif\<close>)\<close>]]
begin

lemma Dep_PairI [type_intro]:
  assumes "is_pair p"
  and "fst p \<Ztypecolon> A"
  and "snd p \<Ztypecolon> B (fst p)"
  shows "p \<Ztypecolon> \<Sum>x : A. B x"
  by (urule set_dep_pairI) (urule assms)+

lemma Dep_pairE [elim!]:
  assumes "p \<Ztypecolon> \<Sum>x : A. B x"
  obtains x y where "x \<Ztypecolon> A" "y \<Ztypecolon> B x" "p = \<langle>x, y\<rangle>"
  using assms by (urule (e) set_dep_pairE)

lemma Dep_pair_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "(p \<Ztypecolon> \<Sum>x : A. (B x)) \<longleftrightarrow> (p \<Ztypecolon> \<Sum>x : A'. (B' x))"
  by (urule set_dep_pair_cong[THEN fun_cong]) (use assms in auto)

lemma Dep_Pair_covariant_dom: "p \<Ztypecolon> \<Sum>x : A. (B x) \<Longrightarrow> (\<And>x. x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A') \<Longrightarrow> p \<Ztypecolon> \<Sum>x : A'. (B x)"
  by auto

lemma Dep_Pair_covariant_codom:
  assumes "p \<Ztypecolon> \<Sum>x : A. (B x)"
  and "\<And>x y. p = \<langle>x, y\<rangle> \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> y \<Ztypecolon> B x \<Longrightarrow> y \<Ztypecolon> B' x"
  shows "p \<Ztypecolon> \<Sum>x : A. (B' x)"
  using assms by auto

lemma Pair_eq_Dep_pair: "(A \<times> B) = Dep_pair A (\<lambda>_. B)"
  supply set_pair_pred_eq_set_dep_pair_pred[simp]
  by (urule refl)

lemma Pair_eq_Dep_pair_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<times> B \<equiv> Dep_pair A' B'"
  by (rule eq_reflection) (use assms Pair_eq_Dep_pair in simp)

lemma Pair_iff_Dep_pair: "(p \<Ztypecolon> A \<times> B) \<longleftrightarrow> p \<Ztypecolon> \<Sum>_ : A. B"
  using Pair_eq_Dep_pair by simp
declare
  Pair_iff_Dep_pair[THEN iffD1, derive]
  Pair_iff_Dep_pair[THEN iffD2, derive]

lemma PairI [type_intro]:
  assumes "is_pair p"
  and "fst p \<Ztypecolon> A"
  and "snd p \<Ztypecolon> B"
  shows "p \<Ztypecolon> A \<times> B"
  using assms by (urule Dep_PairI)

lemma PairE [elim!]:
  assumes "p \<Ztypecolon> A \<times> B"
  obtains x y where "x \<Ztypecolon> A" "y \<Ztypecolon> B" "p = \<langle>x, y\<rangle>"
  using assms by (urule (e) Dep_pairE)

lemma Pair_covariant_dom:
  assumes "p \<Ztypecolon> A \<times> B"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A'"
  shows "p \<Ztypecolon> A' \<times> B"
  using assms by (urule Dep_Pair_covariant_dom)

lemma Pair_covariant_codom:
  assumes "p \<Ztypecolon> A \<times> B"
  and "\<And>x y. p = \<langle>x, y\<rangle> \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> y \<Ztypecolon> B \<Longrightarrow> y \<Ztypecolon> B'"
  shows "p \<Ztypecolon> A \<times> B'"
  using assms by (urule Dep_Pair_covariant_codom)

paragraph \<open>Splitting quantifiers:\<close>

lemma bex_type_dep_pair_iff_bex_bex [iff]:
  "(\<exists>p : (\<Sum>x : A. B x :: set type). P p) \<longleftrightarrow> (\<exists>x : A. \<exists>y : B x. P \<langle>x, y\<rangle>)"
  by (urule bex_set_dep_pair_iff_bex_bex)

lemma ball_type_dep_pair_iff_ball_ball [iff]:
  "(\<forall>p : (\<Sum>x : A. B x :: set type). P p) \<longleftrightarrow> (\<forall>x : A. \<forall>y : B x. P \<langle>x, y\<rangle>)"
  by (urule ball_set_dep_pair_iff_ball_ball)

lemma bex_type_pair_iff_bex_bex [iff]:
  "(\<exists>p : (A \<times> B :: set type). P p) \<longleftrightarrow> (\<exists>x : A. \<exists>y : B. P \<langle>x, y\<rangle>)"
  by (urule bex_set_pair_iff_bex_bex)

lemma ball_type_pair_iff_ball_ball [iff]:
  "(\<forall>p : (A \<times> B :: set type). P p) \<longleftrightarrow> (\<forall>x : A. \<forall>y : B. P \<langle>x, y\<rangle>)"
  by (urule ball_set_pair_iff_ball_ball)

paragraph \<open>Types\<close>

lemma mk_pair_type [type]: "mk_pair \<Ztypecolon> (x : A) \<Rightarrow> B x \<Rightarrow> \<Sum>x : A. (B x)"
  by (urule mono_set_dep_pair_mk_pair)

lemma fst_type [type]: "fst \<Ztypecolon> (\<Sum>x : A. (B x)) \<Rightarrow> A"
  by (urule mono_set_dep_pair_fst)

lemma snd_type [type]: "snd \<Ztypecolon> (p : \<Sum>x : A. B x) \<Rightarrow> B (fst p)"
  by (urule mono_set_dep_pair_snd)

lemma mono_set_dep_pair_curry: "curry \<Ztypecolon> ((p : \<Sum>x : A. (B x)) \<Rightarrow> C p) \<Rightarrow> (x : A) \<Rightarrow> (y : B x) \<Rightarrow> C \<langle>x, y\<rangle>"
  by (urule mono_set_dep_pair_curry)

lemma uncurry_type [type]:
  "uncurry \<Ztypecolon> ((x : A) \<Rightarrow> (y : B x) \<Rightarrow> C \<langle>x, y\<rangle>) \<Rightarrow> (p : \<Sum>x : A. B x) \<Rightarrow> C p"
  by (urule mono_set_dep_pair_uncurry)

lemma swap_type [type]: "swap \<Ztypecolon> A \<times> B \<Rightarrow> B \<times> A"
  by (urule mono_set_pair_curry)

end

(*TODO: if f is a lambda abstraction, the derivator must use backward_derive
rules to prove its type before being able to apply it to uncurry_type together
with Dep_fun_typeE; so we need to create this backward_derive rule to guide
the derivator*)
lemma uncurry_app_type [backward_derive]:
  assumes "f \<Ztypecolon> (a : A) \<Rightarrow> (b : B a) \<Rightarrow> C \<langle>a, b\<rangle>"
  shows "uncurry f \<Ztypecolon> (p : \<Sum>x : A. (B x)) \<Rightarrow> C p"
  by discharge_types


end
