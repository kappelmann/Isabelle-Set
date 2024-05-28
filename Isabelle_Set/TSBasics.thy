\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Basic Soft-Types For Sets\<close>
theory TSBasics
  imports
    Soft_Types.Soft_Types_HOL
    HOTG.HOTG_Set_Difference
begin

abbreviation "Set :: set type \<equiv> Any"

definition [typedef]: "Element A \<equiv> type (mem_of A)"

lemma of_type_Element_eq_mem_of [type_to_HOL_simp]: "of_type (Element A) = mem_of A"
  unfolding Element_def type_to_HOL_simp by simp

lemma mem_iff_Element: "a \<in> A \<longleftrightarrow> a \<Ztypecolon> Element A" unfolding type_to_HOL_simp by simp

corollary
  shows ElementI: "a \<in> A \<Longrightarrow> a \<Ztypecolon> Element A"
  and ElementD: "a \<Ztypecolon> Element A \<Longrightarrow> a \<in> A"
  unfolding type_to_HOL_simp by simp_all

lemma Element_if_subset_if_Element:
  assumes "a \<Ztypecolon> Element A"
  and "A \<subseteq> B"
  shows "a \<Ztypecolon> Element B"
  supply type_to_HOL_simp[simp]
  using assms by (urule mem_if_subset_if_mem)

soft_type_translation
  "a \<in> A" \<rightleftharpoons> "a \<Ztypecolon> Element A" by unfold_types auto

definition [typedef, type_simp]: "Subset A \<equiv> Element (powerset A)"

lemma of_type_Subset_eq_mem_of_powerset [type_to_HOL_simp]:
  "of_type (Subset A) = ((\<supseteq>) A)"
  unfolding Subset_def type_to_HOL_simp by simp

corollary
  shows SubsetI: "A \<subseteq> B \<Longrightarrow> A \<Ztypecolon> Subset B"
  and SubsetD: "A \<Ztypecolon> Subset B \<Longrightarrow> A \<subseteq> B"
  unfolding type_to_HOL_simp by simp_all

context
  notes type_to_HOL_simp[simp]
begin

lemma Subset_covariant:
  assumes "a \<Ztypecolon> Subset A"
  and "A \<subseteq> B"
  shows "a \<Ztypecolon> Subset B"
  using assms by (urule subset_if_subset_if_subset)

lemma Subset_self [derive]: "A \<Ztypecolon> Subset A"
  by (urule subset_self)

end

soft_type_translation
  "A \<subseteq> B" \<rightleftharpoons> "A \<Ztypecolon> Subset B" by unfold_types auto

soft_type_translation
  "\<forall>x : (A :: set). P x" \<rightleftharpoons> "\<forall>x : Element A. P x"
  by auto

soft_type_translation
  "\<exists>x : (A :: set). P x" \<rightleftharpoons> "\<exists>x : Element A. P x"
  by auto

(* Note Kevin: Think about replacing Subset with Collection? *)
subsection \<open>Collections\<close>

definition Collection :: "set type \<Rightarrow> set type"
  where [typedef]: "Collection T \<equiv> type (\<lambda>X. \<forall>x : X. x \<Ztypecolon> T)"

lemma CollectionI: "(\<And>x. x \<in> X \<Longrightarrow> x \<Ztypecolon> T) \<Longrightarrow> X \<Ztypecolon> Collection T"
  by unfold_types auto

lemma Collection_memD: "X \<Ztypecolon> Collection T \<Longrightarrow> x \<in> X \<Longrightarrow> x \<Ztypecolon> T"
  by unfold_types auto

lemma Collection_covariant:
  assumes "X \<Ztypecolon> Collection T"
  and "\<And>x. x \<Ztypecolon> T \<Longrightarrow> x \<in> X \<Longrightarrow> x \<Ztypecolon> T'"
  shows "X \<Ztypecolon> Collection T'"
  using assms by (intro CollectionI) (auto dest: Collection_memD)

lemma Collection_covariant':
  assumes "X \<Ztypecolon> Collection T"
  and "\<And>x. x \<Ztypecolon> T \<Longrightarrow> x \<Ztypecolon> T'"
  shows "X \<Ztypecolon> Collection T'"
  using assms Collection_covariant by auto

lemma Subset_if_Collecten_Element [derive]:
  "A \<Ztypecolon> Collection (Element B) \<Longrightarrow> A \<Ztypecolon> Subset B"
  by unfold_types blast

lemma Collection_Element_if_Subset:
  "A \<Ztypecolon> Subset B \<Longrightarrow> A \<Ztypecolon> Collection (Element B)"
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
  [type]: "(\<in>) \<Ztypecolon> (Element A) \<Rightarrow> (Subset A) \<Rightarrow> Bool" and
  [type]: "powerset \<Ztypecolon> Collection T \<Rightarrow> Collection (Collection T)" and
  [type]: "union \<Ztypecolon> Collection (Collection T) \<Rightarrow> Collection T" and
  [type]: "repl \<Ztypecolon> Collection T \<Rightarrow> (T \<Rightarrow> S) \<Rightarrow> Collection S" and
  [type]: "image \<Ztypecolon> (T \<Rightarrow> S) \<Rightarrow> Collection T \<Rightarrow> Collection S" and

  [type]: "HOL.All \<Ztypecolon> (X \<Rightarrow> Bool) \<Rightarrow> Bool" and
  [type]: "{} \<Ztypecolon> Subset A" and
  [type]: "(\<subseteq>) \<Ztypecolon> Subset A \<Rightarrow> Subset A \<Rightarrow> Bool" and
  [type]: "insert \<Ztypecolon> Element A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "collect \<Ztypecolon> Subset A \<Rightarrow> (Element A \<Rightarrow> Bool) \<Rightarrow> Subset A" and
  [type]: "upair \<Ztypecolon> Element A \<Rightarrow> Element B \<Rightarrow> Subset (A \<union> B)" and

  [type]: "(\<union>) \<Ztypecolon> Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "(\<inter>) \<Ztypecolon> Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A" and
  [type]: "(\<setminus>) \<Ztypecolon> Subset A \<Rightarrow> Subset A \<Rightarrow> Subset A"
  by unfold_types (fastforce simp: of_type_type_eq_self)+

end
