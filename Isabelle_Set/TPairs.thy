\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Dependent Pair Type (\<Sum>-type)\<close>
theory TPairs
  imports Sets
begin

definition [typedef]: "Dep_Pair A B \<equiv> type (\<lambda>p. (\<exists>x : A. \<exists>y : B x. p = \<langle>x, y\<rangle>))"

bundle isa_set_dependent_pairs_syntax
begin
syntax
  "_Dep_Pair" :: \<open>[pttrn, set type, set \<Rightarrow> set type] \<Rightarrow> set\<close> ("\<Sum>_ : _./ _" [0, 0, 100])
end
bundle no_isa_set_dependent_pairs_syntax
begin
syntax
  "_Dep_Pair" :: \<open>[pttrn, set type, set \<Rightarrow> set type] \<Rightarrow> set\<close> ("\<Sum>_ : _./ _" [0, 0, 100])
end
unbundle isa_set_dependent_pairs_syntax

translations
  "\<Sum>x : A. B" \<rightleftharpoons> "CONST Dep_Pair A (\<lambda>x. B)"

abbreviation "Pair A B \<equiv> \<Sum>_ : A. B"

bundle isa_set_pairs_syntax begin notation Pair (infixl "\<times>" 80) end
bundle no_isa_set_pairs_syntax begin no_notation Pair (infixl "\<times>" 80) end
unbundle isa_set_pairs_syntax

lemma mem_dep_pairs_iff_Dep_Pair:
  "p \<in> (\<Sum>x \<in> A. (B x)) \<longleftrightarrow> p : \<Sum>x : Element A. (Element (B x))"
  by unfold_types auto

soft_type_translation
  "p \<in> \<Sum>x \<in> A. (B x)" \<rightleftharpoons> "p : \<Sum>x : Element A. (Element (B x))"
  using mem_dep_pairs_iff_Dep_Pair by auto

(* TODO: this translation should be automatic whenever it is needed *)
lemma Element_dep_pairs_iff_Dep_Pair:
  "p : Element (\<Sum>x \<in> A. (B x)) \<longleftrightarrow> p : \<Sum>x : Element A. (Element (B x))"
  using mem_dep_pairs_iff_Dep_Pair by (auto iff: mem_iff_Element)

lemma pair_type [type]: "pair : (x : A) \<Rightarrow> B x \<Rightarrow> \<Sum>x : A. (B x)"
  by unfold_types auto

lemma Dep_PairE [elim!]:
  assumes "p : \<Sum>x : A. (B x)"
  obtains x y where "x : A" "y : B x" "p = \<langle>x, y\<rangle>"
  using assms unfolding Dep_Pair_def meaning_of_type by auto

lemma Dep_Pair_covariant_fst:
  "p : \<Sum>x : A. (B x) \<Longrightarrow> (\<And>x. x : A \<Longrightarrow> x : A') \<Longrightarrow> p : \<Sum>x : A'. (B x)"
  by auto

lemma Dep_Pair_covariant_snd:
  assumes "p : \<Sum>x : A. (B x)"
  and "\<And>x y. x : A \<Longrightarrow> y : B x \<Longrightarrow> p = \<langle>x, y\<rangle> \<Longrightarrow> y : B' x"
  shows "p : \<Sum>x : A. (B' x)"
  using assms by force

lemma
  fst_type [type]: "fst : (\<Sum>x : A. (B x)) \<Rightarrow> A" and
  snd_type [type]: "snd : (p : \<Sum>x : A. (B x)) \<Rightarrow> B (fst p)"
  by unfold_types auto

lemma uncurry_type [type]:
  "uncurry : ((x : A) \<Rightarrow> (y : B x) \<Rightarrow> C \<langle>x, y\<rangle>) \<Rightarrow> (p : \<Sum>x : A. (B x)) \<Rightarrow> C p"
  unfolding uncurry_def by unfold_types auto

(*TODO: if f is a lambda abstraction, the derivator must use backward_derive
rules to prove its type before being able to apply it to uncurry_type together
with Dep_fun_typeE; so we need to create this backward_derive rule to guide
the derivator*)
lemma uncurry_app_type [backward_derive]:
  assumes "f : (a : A) \<Rightarrow> (b : B a) \<Rightarrow> C \<langle>a, b\<rangle>"
  shows "uncurry f : (p : \<Sum>x : A. (B x)) \<Rightarrow> C p"
  by discharge_types

lemma pair_Dep_Pair_iff [iff]: "\<langle>x, y\<rangle> : \<Sum>x : A. (B x) \<longleftrightarrow> x : A \<and> y : B x"
  by auto

lemma fst_type_if_Dep_Pair: "\<langle>x, y\<rangle> : \<Sum>x : A. (B x) \<Longrightarrow> x : A"
  using pair_Dep_Pair_iff by simp

lemma snd_type_if_Dep_Pair: "\<langle>x, y\<rangle> : \<Sum>x : A. (B x) \<Longrightarrow> y : B x"
  using pair_Dep_Pair_iff by simp

lemma Dep_Pair_cong [cong]:
  assumes "\<And>x. x : A \<longleftrightarrow> x : A'"
  and "\<And>x y. x : A' \<Longrightarrow> y : B x \<longleftrightarrow> y : B' x"
  shows "(p : \<Sum>x : A. (B x)) \<longleftrightarrow> (p : \<Sum>x : A'. (B' x))"
proof
  assume "p : \<Sum>x : A'. (B' x)"
  then obtain x y where "x : A'" "y : B' x" "p = \<langle>x, y\<rangle>" by auto
  moreover from assms have "x : A" "y : B x" by auto
  ultimately show "p : \<Sum>x : A. (B x)" by auto
qed (auto simp: assms)

lemma Dep_Pair_pair_fst_snd_eq [simp]: "p : \<Sum>x : A. (B x) \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

text \<open>Splitting quantifiers:\<close>

lemma tbex_Dep_Pair_iff_tbex_tbex [iff]:
  "(\<exists>p : \<Sum>x : A. (B x). P p) \<longleftrightarrow> (\<exists>x : A. \<exists>y : B x. P \<langle>x, y\<rangle>)"
  by auto

lemma tball_Dep_Pair_iff_tball_tball [iff]:
  "(\<forall>p : \<Sum>x : A. (B x). P p) \<longleftrightarrow> (\<forall>x : A. \<forall>y : B x. P \<langle>x, y\<rangle>)"
  by auto

lemma swap_type [type]: "swap : A \<times> B \<Rightarrow> B \<times> A"
  unfolding swap_def by discharge_types


end
