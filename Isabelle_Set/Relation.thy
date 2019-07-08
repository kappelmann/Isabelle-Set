section \<open>Binary relations\<close>

theory Relation
imports Pair

begin


definition domain :: "set \<Rightarrow> set"
  where "domain R \<equiv> {fst p | p \<in> R}"

definition range :: "set \<Rightarrow> set"
  where "range R \<equiv> {snd p | p \<in> R}"

definition field :: "set \<Rightarrow> set"
  where "field R \<equiv> domain R \<union> range R"


lemma relation_elem_conv [simp]: "\<lbrakk>R \<subseteq> A \<times> B; p \<in> R\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

lemma elem_relation_elim: "R \<subseteq> A \<times> B \<Longrightarrow> p \<in> R  \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> p = \<langle>a, b\<rangle> \<Longrightarrow> Q) \<Longrightarrow> Q"
  by auto

text \<open>Various relations\<close>

lemma DUnion_relation: "\<Coprod>x \<in> A. (B x) \<subseteq> A \<times> (\<Union>x \<in> A. (B x))"
  by auto

lemma Collect_relation:
  assumes "f : element X \<Rightarrow> element A" and "g : element X \<Rightarrow> element B"
  shows "{\<langle>f x, g x\<rangle>. x \<in> X} \<subseteq> A \<times> B"
  using assms by squash_types auto

lemma relation_Cons_iff [iff]:
  assumes "x : element A" and "y : element B"
  shows "Cons \<langle>x, y\<rangle> X \<subseteq> A \<times> B \<longleftrightarrow> X \<subseteq> A \<times> B"
  using assms by squash_types auto


subsection \<open>Domain and range\<close>

lemma domainI: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> x \<in> domain R"
  unfolding domain_def by auto

lemma domainE: "\<lbrakk>x \<in> domain R; R \<subseteq> A \<times> B\<rbrakk> \<Longrightarrow> \<exists>y. \<langle>x, y\<rangle> \<in> R"
proof -
  assume assms: "x \<in> domain R" "R \<subseteq> A \<times> B"
  then obtain p where "p \<in> R" and "x = fst p" unfolding domain_def by auto
  with assms have "\<langle>x, snd p\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma rangeI: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> y \<in> range R"
  unfolding range_def by auto

lemma rangeE:
  assumes "y \<in> range R" and "R \<subseteq> A \<times> B"
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

lemma domain_subset: "R \<subseteq> A \<times> B \<Longrightarrow> domain R \<subseteq> A"
  unfolding domain_def by auto

lemma range_subset: "R \<subseteq> A \<times> B \<Longrightarrow> range R \<subseteq> B"
  unfolding range_def by auto

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
  "R \<subseteq> A \<times> B \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def by auto

lemma converseI [intro!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> R; R \<subseteq> A \<times> B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> converse R;  R \<subseteq> A \<times> B\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]:
  "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> P; R \<subseteq> A \<times> B\<rbrakk> \<Longrightarrow> P"
  unfolding converse_def by auto

lemma converse_relation [intro]: "R \<subseteq> A \<times> B \<Longrightarrow> converse R \<subseteq> B \<times> A"
  unfolding converse_def by auto

lemma converse_involution: "R \<subseteq> A \<times> B \<Longrightarrow> converse (converse R) = R"
  unfolding converse_def by extensionality

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by extensionality

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by extensionality

lemma converse_type [type]: "converse : subset (A \<times> B) \<Rightarrow> subset (B \<times> A)"
  by squash_types auto


subsection \<open>Properties of relations\<close>

definition reflexive :: "set \<Rightarrow> bool"
  where "reflexive R \<equiv> \<forall>x \<in> domain R. \<langle>x, x\<rangle> \<in> R"

definition irreflexive :: "set \<Rightarrow> bool"
  where "irreflexive R \<equiv> \<forall>x \<in> domain R. \<langle>x, x\<rangle> \<notin> R"

definition symmetric :: "set \<Rightarrow> bool"
  where "symmetric R \<equiv> \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

definition antisymmetric :: "set \<Rightarrow> bool"
  where "antisymmetric R \<equiv>
    \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

definition transitive :: "set \<Rightarrow> bool"
  where "transitive R \<equiv>
    \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<forall>z \<in> domain R. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

definition total :: "set \<Rightarrow> bool"
  where "total R \<equiv> \<forall>x \<in> domain R. \<forall>y \<in> domain R. \<langle>x, y\<rangle> \<in> R \<or> x = y \<or> \<langle>y, x\<rangle> \<in> R"


subsection \<open>Partial and total orders\<close>

definition partial_order :: "set \<Rightarrow> set type"
  where partial_order_typedef:
  "partial_order P \<equiv> reflexive \<cdot> transitive \<cdot> antisymmetric \<cdot> subset (P \<times> P)"

definition strict_partial_order :: "set \<Rightarrow> set type"
  where strict_partial_order_typedef:
  "strict_partial_order P \<equiv> irreflexive \<cdot> transitive \<cdot> subset (P \<times> P)"

definition total_order :: "set \<Rightarrow> set type"
  where total_order_typedef:
  "total_order P \<equiv> total \<cdot> partial_order P"


subsection \<open>Soft typing\<close>

definition relation :: "set type"
  where relation_typedef: "relation \<equiv> Type (\<lambda>R. \<forall>z \<in> R. \<exists>x y. z = \<langle>x, y\<rangle>)"

definition domained :: "set \<Rightarrow> set \<Rightarrow> bool" ("(_-domained)" [1000])
  where "A-domained \<equiv> \<lambda>R. domain R \<subseteq> A"

definition valued :: "set \<Rightarrow> set \<Rightarrow> bool" ("(_-valued)" [1000])
  where "B-valued \<equiv> \<lambda>R. range R \<subseteq> B"

lemma relations_relation_type [elim]:
  "R \<subseteq> A \<times> B \<Longrightarrow> R : A-domained \<cdot> B-valued \<cdot> relation"
  unfolding domained_def valued_def domain_def range_def relation_typedef adjective_def
  by squash_types auto


end
