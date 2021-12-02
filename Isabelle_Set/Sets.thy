section \<open>Soft-Types for Sets\<close>

theory Sets
imports
  Soft_Types.Soft_Types_HOL
  HOTG.Universes
begin

subsection \<open>Sets, Elements, and Subsets\<close>

abbreviation Set :: "set type"
  where "Set \<equiv> Any"

definition Element :: "set \<Rightarrow> set type"
  where [typedef]: "Element A \<equiv> type (\<lambda>x. x \<in> A)"

lemma Element_covariant: "a : Element A \<Longrightarrow> A \<subseteq> B  \<Longrightarrow> a : Element B"
  by unfold_types auto

definition Subset :: "set \<Rightarrow> set type"
  where [typedef, type_simp]: "Subset A \<equiv> Element (powerset A)"

lemma Subset_covariant: "a : Subset A \<Longrightarrow> A \<subseteq> B  \<Longrightarrow> a : Subset B"
  by unfold_types auto

lemma mem_iff_Element: "a \<in> A \<longleftrightarrow> a : Element A" by unfold_types

corollary
  ElementI: "a \<in> A \<Longrightarrow> a : Element A" and
  ElementD: "a : Element A \<Longrightarrow> a \<in> A"
  by (auto iff: mem_iff_Element)

lemma Subset_iff: "A \<subseteq> B \<longleftrightarrow> A : Subset B" by unfold_types auto

corollary
  SubsetI: "A \<subseteq> B \<Longrightarrow> A : Subset B" and
  SubsetD: "A : Subset B \<Longrightarrow> A \<subseteq> B"
  by (auto iff: Subset_iff)

lemma subset_self [derive]: "A : Subset A"
  by unfold_types auto


text \<open>Declare basic soft type translations.\<close>

(*Note: soft type translations go on the right of the "\<rightleftharpoons>".
  This should either be documented, or else made unnecessary.*)
soft_type_translation
  "a \<in> A" \<rightleftharpoons> "a : Element A" by unfold_types

soft_type_translation
  "A \<subseteq> B" \<rightleftharpoons> "A : Subset B" by unfold_types auto

soft_type_translation
  "\<forall>x \<in> A. P x" \<rightleftharpoons> "\<forall>x : Element A. P x"
  by unfold_types auto

soft_type_translation
  "\<exists>x \<in> A. P x" \<rightleftharpoons> "\<exists>x : Element A. P x"
  by unfold_types auto

(* Note Kevin: Think about removing collections all together? *)
subsection \<open>Collections\<close>

definition Collection :: "set type \<Rightarrow> set type"
  where [typeclass]: "Collection T \<equiv> type (\<lambda>x. \<forall>y \<in> x. y : T)"

lemma Subset_if_Collecten_Element [derive]:
  "A : Collection (Element B) \<Longrightarrow> A : Subset B"
  by unfold_types blast

lemma Eollection_Element_if_Subset:
  "A : Subset B \<Longrightarrow> A : Collection (Element B)"
  by unfold_types blast

subsection \<open>Basic Constant Types\<close>

text \<open>
The following typing rules are less general than what could be proved, since the
\<^term>\<open>Bool\<close> soft type is trivial. But the rules also determine the behavior of
type inference.

The rule for \<^term>\<open>HOL.All\<close> currently needs to be restricted due to a deficiency
in the elaboration algorithm.
\<close>

lemma
  [type]: "(\<in>) : (Element A) \<Rightarrow> (Subset A) \<Rightarrow> Bool" and
  [type]: "powerset : Collection T \<Rightarrow> Collection (Collection T)" and
  [type]: "union : Collection (Collection T) \<Rightarrow> Collection T" and
  [type]: "repl : Collection T \<Rightarrow> (T \<Rightarrow> S) \<Rightarrow> Collection S" and

  [type]: "HOL.All : ((T :: set type) \<Rightarrow> Bool) \<Rightarrow> Bool" and
  [type]: "{} : Subset A" and
  [type]: "(\<subseteq>) : Subset A \<Rightarrow> Subset A \<Rightarrow> Bool" and
  [type]: "cons : Element A \<Rightarrow> Subset A \<Rightarrow> Subset A" and

  [type]: "(\<union>) : Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "(\<inter>) : Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "collect : Subset A \<Rightarrow> (Element A \<Rightarrow> Bool) \<Rightarrow> Subset A"

  by unfold_types auto


subsection \<open>Pi-Types\<close>

lemma Dep_fun_type_Element_if_ball [dest]:
  "\<forall>x. x \<in> A \<longrightarrow> f x \<in> B \<Longrightarrow> f : Element A \<Rightarrow> Element B"
  by unfold_types

lemma Dep_fun_type_Element_if_ball' [dest]:
  "\<forall>x \<in> A. f x \<in> B \<Longrightarrow> f : Element A \<Rightarrow> Element B"
  by unfold_types auto


subsection \<open>Ordered Pairs\<close>

lemma
  pairs_type [type]: "(\<times>) : Subset A \<Rightarrow> Subset B \<Rightarrow> Subset (A \<times> B)" and
  pair_type [type]: "pair : Element A \<Rightarrow> Element B \<Rightarrow> Element (A \<times> B)" and
  fst_type [type]: "fst : Element (A \<times> B) \<Rightarrow> Element A" and
  snd_type [type]: "snd : Element (A \<times> B) \<Rightarrow> Element B"
  by unfold_types auto

text \<open>
The following are more general but also makes elaboration more complex, so we
don't declare them by default for now.
\<close>

lemma pair_dep_type:
  "pair : (x : Element A) \<Rightarrow> Element (B x) \<Rightarrow> Element (\<Sum>x \<in> A. (B x))"
  by unfold_types auto

lemma fst_dep_type:
  "fst : Element (\<Sum>x \<in> A. (B x)) \<Rightarrow> Element A"
  by unfold_types auto

lemma snd_dep_type:
  "snd : (p : Element (\<Sum>x \<in> A. (B x))) \<Rightarrow> Element (B (fst p))"
  by unfold_types auto

lemma univ_closed_pairs_Element [derive]:
  "\<lbrakk>A : Element (univ U); B : Element (univ U)\<rbrakk> \<Longrightarrow> A \<times> B : Element (univ U)"
  by unfold_types auto

lemma univ_closed_pairs_Subset [derive]:
  "\<lbrakk>A : Subset (univ U); B : Subset (univ U)\<rbrakk> \<Longrightarrow> A \<times> B : Subset (univ U)"
  by unfold_types auto

subsection \<open>Coproduct Type\<close>

lemma Element_coprodE:
  assumes "x : Element (A \<Coprod> B)"
  obtains
      (inl) a where "a : Element A" "x = inl a"
    | (inr) b where "b : Element B" "x = inr b"
  using assms by (auto simp: mem_iff_Element[symmetric])

lemma coprod_rec_type [type]:
  "coprod_rec : (Element A \<Rightarrow> X) \<Rightarrow> (Element B \<Rightarrow> X) \<Rightarrow> Element (A \<Coprod> B) \<Rightarrow> X"
  by unfold_types auto

lemma inl_type [type]: "inl : Element A \<Rightarrow> Element (A \<Coprod> B)"
  unfolding inl_def coprod_def by unfold_types blast

lemma inr_type [type]: "inr : Element B \<Rightarrow> Element (A \<Coprod> B)"
  unfolding inr_def coprod_def by unfold_types blast


end
