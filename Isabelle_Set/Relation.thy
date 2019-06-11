section \<open>Binary relations\<close>

theory Relation
imports Pair

begin


definition relations :: "[set, set] \<Rightarrow> set"
  where "relations A B \<equiv> Pow (A \<times> B)"

definition domain :: "set \<Rightarrow> set"
  where "domain R \<equiv> {fst p | p \<in> R}"

definition range :: "set \<Rightarrow> set"
  where "range R \<equiv> {snd p | p \<in> R}"

definition field :: "set \<Rightarrow> set"
  where "field R \<equiv> domain R \<union> range R"


lemma relations_iff [iff]: "R \<in> relations A B \<longleftrightarrow> R \<subseteq> A \<times> B"
  unfolding relations_def by auto

lemma relationsI: "R \<subseteq> A \<times> B \<Longrightarrow> R \<in> relations A B"
  by auto

lemma relationsE [elim]: "R \<in> relations A B \<Longrightarrow> R \<subseteq> A \<times> B"
  by auto

lemma relation_elem_conv [simp]: "\<lbrakk>R \<in> relations A B; p \<in> R\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  unfolding relations_def by auto

lemma relations_fst: "\<lbrakk>R \<in> relations A B; p \<in> R\<rbrakk> \<Longrightarrow> fst p \<in> A"
  by auto

lemma relations_snd: "\<lbrakk>R \<in> relations A B; p \<in> R\<rbrakk> \<Longrightarrow> snd p \<in> B"
  by auto


text \<open>Various relations\<close>

lemma empty_relation [intro]: "{} \<in> relations A B"
  unfolding relations_def by auto

lemma subset_relation [elim]: "\<lbrakk>S \<subseteq> R; R \<in> relations A B\<rbrakk> \<Longrightarrow> S \<in> relations A B"
  unfolding relations_def by auto

lemma DUnion_relation: "\<Coprod>x \<in> A. (B x) \<in> relations A (\<Union>x \<in> A. (B x))"
  unfolding relations_def by auto

lemma Collect_relation:
  assumes "f : element X \<Rightarrow> element A" and "g : element X \<Rightarrow> element B"
  shows "{\<langle>f x, g x\<rangle>. x \<in> X} \<in> relations A B"
  unfolding relations_def using assms by stauto

lemma relation_Cons_iff [iff]:
  assumes "x : element A" and "y : element B"
  shows "Cons \<langle>x, y\<rangle> X \<in> relations A B \<longleftrightarrow> X \<in> relations A B"
  unfolding relations_def using assms by stauto


subsection \<open>Domain and range\<close>

lemma domainI: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> x \<in> domain R"
  unfolding domain_def by auto

lemma domainE: "\<lbrakk>x \<in> domain R; R \<in> relations A B\<rbrakk> \<Longrightarrow> \<exists>y. \<langle>x, y\<rangle> \<in> R"
proof -
  assume assms: "x \<in> domain R" "R \<in> relations A B"
  then obtain p where "p \<in> R" and "x = fst p" unfolding domain_def by auto
  with assms have "\<langle>x, snd p\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma rangeI: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> y \<in> range R"
  unfolding range_def by auto

lemma rangeE:
  assumes "y \<in> range R" and "R \<in> relations A B"
  shows "\<exists>x. \<langle>x, y\<rangle> \<in> R"
proof -
  from assms(1) obtain p where "p \<in> R" and "y = snd p" unfolding range_def by auto
  with assms(2) have "\<langle>fst p, y\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma domain_empty [simp]: "domain {} = {}"
  unfolding domain_def by auto

lemma range_empty [simp]: "range {} = {}"
  unfolding range_def by auto

lemma domain_subset: "R \<in> relations A B \<Longrightarrow> domain R \<subseteq> A"
  unfolding domain_def relations_def by auto

lemma range_subset: "R \<in> relations A B \<Longrightarrow> range R \<subseteq> B"
  unfolding range_def relations_def by auto

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

lemma range_is_converse_domain: "range R = domain (converse R)"
  unfolding range_def domain_def converse_def
  by auto

lemma converse_iff [simp]:
  "R \<in> relations A B \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def by auto

lemma converseI [intro!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> R; R \<in> relations A B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> converse R; R \<in> relations A B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]:
  "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> P; R \<in> relations A B\<rbrakk> \<Longrightarrow> P"
  unfolding converse_def by auto

lemma converse_relation [intro]: "R \<in> relations A B \<Longrightarrow> converse R \<in> relations B A"
  unfolding converse_def relations_def by auto

lemma converse_involution: "R \<in> relations A B \<Longrightarrow> converse (converse R) = R"
  unfolding converse_def by extensionality

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by extensionality

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by extensionality

lemma converse_type [type]: "converse : element (relations A B) \<Rightarrow> element (relations B A)"
  by stauto


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


subsection \<open>Partial orders\<close>

definition partial_order :: "set \<Rightarrow> set type"
  where "partial_order P \<equiv>
    reflexive \<cdot> transitive \<cdot> antisymmetric \<cdot> element (relations P P)"

definition strict_partial_order :: "set \<Rightarrow> set type"
  where "strict_partial_order P \<equiv>
    irreflexive \<cdot> transitive \<cdot> element (relations P P)"


end
