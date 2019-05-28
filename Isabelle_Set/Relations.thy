section \<open>Binary relations and functions\<close>

theory Relations
imports Pair

begin

subsection \<open>Relations\<close>

abbreviation relation :: "[set, set] \<Rightarrow> set type"
  where "relation A B \<equiv> subset (A \<times> B)"

definition domain :: "set \<Rightarrow> set"
  where "domain R \<equiv> {fst p | p \<in> R}"

definition range :: "set \<Rightarrow> set"
  where "range R \<equiv> {snd p | p \<in> R}"

definition field :: "set \<Rightarrow> set"
  where "field R \<equiv> domain R \<union> range R"


lemma relation_subsetE [elim]: "\<lbrakk>S \<subseteq> R; R : relation A B\<rbrakk> \<Longrightarrow> S : relation A B"
  unfolding element_typedef by auto

lemma DUnion_rel: "\<Coprod>x \<in> A. (B x) : relation A (\<Union>x \<in> A. B x)"
  unfolding element_typedef by auto

lemma relation_elem_subsetI: "\<lbrakk>p \<in> R; R : relation A B\<rbrakk> \<Longrightarrow> p \<in> A \<times> B"
  unfolding element_typedef by auto


subsection \<open>Converse relations\<close>

definition converse :: "set \<Rightarrow> set"
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"


text \<open>Alternative definition for the range of a relation\<close>

lemma range_def2: "range R = domain (converse R)"
  unfolding range_def domain_def converse_def
  by auto


lemma converse_iff [simp]:
  "R : relation A B \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def element_typedef
  by auto

lemma converseI [intro!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> R; R : relation A B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> converse R; R : relation A B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]:
  "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> P; R : relation A B\<rbrakk> \<Longrightarrow> P"
  unfolding element_typedef converse_def by auto


lemma converse_typeI [intro]: "R : relation A B \<Longrightarrow> converse R : relation B A"
  unfolding element_typedef converse_def by auto

lemma converse_type [type]: "converse: relation A B \<Rightarrow> relation B A"
  using Pi_typeI[of "relation A B" converse "\<lambda>_. relation B A"]
  by auto

lemma converse_involution: "R : relation A B \<Longrightarrow> converse (converse R) = R"
  unfolding converse_def element_typedef
  by (extensionality, rule+) auto  

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by extensionality

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by extensionality


subsection \<open>Functions\<close>

definition function :: "[set, set] \<Rightarrow> set type"
  where "function A B \<equiv> Type (\<lambda>f. f : relation A B \<and> (\<forall>x \<in> A. \<exists>!y \<in> B. \<langle>x, y\<rangle> \<in> f))"


end
