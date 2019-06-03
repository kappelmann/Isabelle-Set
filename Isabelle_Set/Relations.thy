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

lemma relation_collectI: "{\<langle>f x, g x\<rangle>. x \<in> A} : relation"
  unfolding relation_typedef by auto

lemma domainE: 
  assumes "R: relation" "a \<in> domain R"
  shows "\<exists>y. \<langle>a, y\<rangle> \<in> R"
proof -
  from `a \<in> domain R` obtain p where "p \<in> R" "a = fst p" unfolding domain_def by auto
  with `R: relation`
  have "\<langle>a, snd p\<rangle> \<in> R" unfolding relation_typedef by auto
  thus ?thesis ..
qed


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

lemma domain_Collect [simp]: "domain {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  unfolding domain_def by auto

lemma domain_Cons [simp]: "domain (Cons \<langle>x, y\<rangle> A) = Cons x (domain A)"
  unfolding domain_def by extensionality

lemma domain_empty [simp]: "domain {} = {}"
  unfolding domain_def by auto

lemma empty_relation[intro]: "{} : relation"
  unfolding relation_typedef by auto

lemma relation_Cons [simp]: "Cons \<langle>x, y\<rangle> A : relation \<longleftrightarrow> A : relation"
  unfolding relation_typedef by auto


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

(* Should define these properties as adjectives. But how exactly... *)


subsection \<open>Partial orders\<close>

definition porder :: "set \<Rightarrow> set type"
  where "porder P \<equiv> relation P P \<bar> Type (\<lambda>R. reflexive R \<and> antisymmetric R \<and> transitive R)"

definition sporder :: "set \<Rightarrow> set type"
  where "sporder P \<equiv> relation P P \<bar> Type (\<lambda>R. irreflexive R \<and> transitive R)"


subsection \<open>Functions\<close>

definition function :: "[set, set] \<Rightarrow> set type"
  where "function A B \<equiv> relation A B \<bar> Type (\<lambda>f. \<forall>x \<in> A. \<exists>!y \<in> B. \<langle>x, y\<rangle> \<in> f)"


end
