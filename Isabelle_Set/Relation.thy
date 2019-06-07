section \<open>Binary relations\<close>

theory Relation
imports Pair

begin

abbreviation relation :: "[set, set] \<Rightarrow> set type"
  where "relation A B \<equiv> element (Pow (A \<times> B))"

definition domain :: "set \<Rightarrow> set"
  where "domain R \<equiv> {fst p | p \<in> R}"

definition range :: "set \<Rightarrow> set"
  where "range R \<equiv> {snd p | p \<in> R}"

definition field :: "set \<Rightarrow> set"
  where "field R \<equiv> domain R \<union> range R"


lemma relation_type_iff [iff_st]: "R : relation A B \<longleftrightarrow> R \<subseteq> A \<times> B"
  by stauto

lemma relation_typeI [intro_st]: "R \<subseteq> A \<times> B \<Longrightarrow> R : relation A B"
  by stauto

lemma relation_typeE [elim_st]: "R : relation A B \<Longrightarrow> R \<subseteq> A \<times> B"
  by stauto

lemma relation_elem_conv [simp]: "\<lbrakk>R : relation A B; p \<in> R\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by stauto


text \<open>Various relations\<close>

lemma empty_relation [intro]: "{} : relation A B"
  by stauto

lemma subset_relation [elim]: "\<lbrakk>S \<subseteq> R; R : relation A B\<rbrakk> \<Longrightarrow> S : relation A B"
  by stauto

lemma DUnion_relation: "\<Coprod>x \<in> A. (B x) : relation A (\<Union>x \<in> A. (B x))"
  by stauto

lemma Collect_relation:
  assumes "f : element X \<Rightarrow> element A" and "g : element X \<Rightarrow> element B"
  shows "{\<langle>f x, g x\<rangle>. x \<in> X} : relation A B"
  using assms by stauto

lemma relation_Cons_iff [iff]:
  assumes "x : element A" and "y : element B"
  shows "Cons \<langle>x, y\<rangle> X : relation A B \<longleftrightarrow> X : relation A B"
  using assms by stauto


subsection \<open>Domain and range\<close>

lemma domainI: "\<lbrakk>\<langle>x, y\<rangle> \<in> R; R : relation A B\<rbrakk> \<Longrightarrow> x \<in> domain R"
  unfolding domain_def by auto

lemma domainE: "\<lbrakk>x \<in> domain R; R: relation A B\<rbrakk> \<Longrightarrow> \<exists>y. \<langle>x, y\<rangle> \<in> R"
proof -
  assume assms: "x \<in> domain R" "R: relation A B"
  then obtain p where "p \<in> R" and "x = fst p" unfolding domain_def by auto
  with assms have "\<langle>x, snd p\<rangle> \<in> R" by stauto
  thus ?thesis ..
qed

lemma rangeI: "\<lbrakk>\<langle>x, y\<rangle> \<in> R; R : relation A B\<rbrakk> \<Longrightarrow> y \<in> range R"
  unfolding range_def by auto

lemma rangeE: "\<lbrakk>y \<in> range R; R: relation A B\<rbrakk> \<Longrightarrow> \<exists>x. \<langle>x, y\<rangle> \<in> R"
proof -
  assume assms: "y \<in> range R" "R: relation A B"
  then obtain p where "p \<in> R" and "y = snd p" unfolding range_def by auto
  with assms have "\<langle>fst p, y\<rangle> \<in> R" by stauto
  thus ?thesis ..
qed

lemma domain_empty [simp]: "domain {} = {}"
  unfolding domain_def by auto

lemma range_empty [simp]: "range {} = {}"
  unfolding range_def by auto

lemma domain_subset: "R : relation A B \<Longrightarrow> domain R \<subseteq> A"
  unfolding domain_def by stauto

lemma range_subset: "R : relation A B \<Longrightarrow> range R \<subseteq> B"
  unfolding range_def by stauto

lemma domain_Collect [simp]: "domain {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  unfolding domain_def by auto

lemma range_Collect [simp]: "range {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  unfolding range_def by auto

lemma domain_Cons [simp]: "domain (Cons \<langle>x, y\<rangle> A) = Cons x (domain A)"
  unfolding domain_def by extensionality

lemma range_Cons [simp]: "range (Cons \<langle>x, y\<rangle> A) = Cons y (range A)"
  unfolding range_def by extensionality


subsection \<open>Converse relations\<close>

definition converse :: "set \<Rightarrow> set"
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"


text \<open>Alternative definition for the range of a relation\<close>

lemma range_def2: "range R = domain (converse R)"
  unfolding range_def domain_def converse_def
  by auto


lemma converse_iff [simp]:
  "R : relation A B \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def by stauto

lemma converseI [intro!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> R; R : relation A B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> converse R; R : relation A B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]:
  "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> P; R : relation A B\<rbrakk> \<Longrightarrow> P"
  unfolding converse_def by stauto


lemma converse_typeI [intro]: "R : relation A B \<Longrightarrow> converse R : relation B A"
  unfolding converse_def by stauto

lemma converse_type [type]: "converse: relation A B \<Rightarrow> relation B A"
  by stauto

lemma converse_involution: "R : relation A B \<Longrightarrow> converse (converse R) = R"
  by extensionality stauto

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by extensionality

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by extensionality


subsection \<open>Properties of relations\<close>

abbreviation reflexive :: "set \<Rightarrow> bool"
  where "reflexive R \<equiv> \<forall>x \<in> domain R. \<langle>x, x\<rangle> \<in> R"

abbreviation irreflexive :: "set \<Rightarrow> bool"
  where "irreflexive R \<equiv> \<forall>x \<in> domain R. \<langle>x, x\<rangle> \<notin> R"

abbreviation symmetric :: "set \<Rightarrow> bool"
  where "symmetric R \<equiv> \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

abbreviation antisymmetric :: "set \<Rightarrow> bool"
  where "antisymmetric R \<equiv>
    \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

abbreviation transitive :: "set \<Rightarrow> bool"
  where "transitive R \<equiv>
    \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<forall>z \<in> domain R. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

abbreviation total :: "set \<Rightarrow> bool"
  where "total R \<equiv> \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<langle>x, y\<rangle> \<in> R \<or> x = y \<or> \<langle>y, x\<rangle> \<in> R"

(* Should define these properties as adjectives. But how exactly?... *)


subsection \<open>Partial orders\<close>

definition partial_order :: "set \<Rightarrow> set type"
  where "partial_order P \<equiv> relation P P \<bar> Type (\<lambda>R. reflexive R \<and> antisymmetric R \<and> transitive R)"

definition strict_partial_order :: "set \<Rightarrow> set type"
  where "strict_partial_order P \<equiv> relation P P \<bar> Type (\<lambda>R. irreflexive R \<and> transitive R)"


end
