section \<open>Soft-Types for Sets\<close>
theory Sets
imports
  Soft_Types.Soft_Types_HOL
  HOTG.Pairs
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
  where [typedef]: "Collection T \<equiv> type (\<lambda>x. \<forall>y \<in> x. y : T)"

lemma CollectionI: "(\<And>x. x \<in> C \<Longrightarrow> x : T) \<Longrightarrow> C : Collection T"
  by unfold_types auto

lemma Collection_memD: "C : Collection T \<Longrightarrow> x \<in> C \<Longrightarrow> x : T"
  by unfold_types auto

lemma Collection_covariant:
  assumes "C : Collection T"
  and "\<And>x. x : T \<Longrightarrow> x \<in> C \<Longrightarrow> x : T'"
  shows "C : Collection T'"
  using assms by (intro CollectionI) (auto dest: Collection_memD)

lemma Collection_covariant':
  assumes "C : Collection T"
  and "\<And>x. x : T \<Longrightarrow> x : T'"
  shows "C : Collection T'"
  using assms Collection_covariant by auto

lemma Subset_if_Collecten_Element [derive]:
  "A : Collection (Element B) \<Longrightarrow> A : Subset B"
  by unfold_types blast

lemma Collection_Element_if_Subset:
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
  [type]: "insert : Element A \<Rightarrow> Subset A \<Rightarrow> Subset A" and

  [type]: "(\<union>) : Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "(\<inter>) : Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "collect : Subset A \<Rightarrow> (Element A \<Rightarrow> Bool) \<Rightarrow> Subset A" and
  [type]: "(\<times>) : Subset A \<Rightarrow> Subset B \<Rightarrow> Subset (A \<times> B)"
  by unfold_types auto


end
