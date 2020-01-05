chapter \<open>Binary relations\<close>

theory Relation
imports Ordered_Pairs

begin

definition dom :: "set \<Rightarrow> set"
  where "dom R \<equiv> {fst p | p \<in> R}"

definition rng :: "set \<Rightarrow> set"
  where "rng R \<equiv> {snd p | p \<in> R}"

definition fld :: "set \<Rightarrow> set"
  where "fld R \<equiv> dom R \<union> rng R"


section \<open>Domain and range\<close>

lemma domI [intro]: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> x \<in> dom R"
  unfolding dom_def by auto

lemma domE [elim]:
  assumes "x \<in> dom R" and "R \<subseteq> A \<times> B"
  shows "\<exists>y. \<langle>x, y\<rangle> \<in> R"
proof -
  from assms(1) obtain p where "p \<in> R" and "x = fst p" unfolding dom_def by auto
  with assms(2) have "\<langle>x, snd p\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma dom_iff [iff]:
  "R \<subseteq> A \<times> B \<Longrightarrow> x \<in> dom R \<longleftrightarrow> (\<exists>y. \<langle>x, y\<rangle> \<in> R)"
  by auto

lemma not_in_domE: "\<lbrakk>x \<notin> dom R; \<not>(\<exists>y. \<langle>x, y\<rangle> \<in> R) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding dom_def by force

lemma rngI: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> y \<in> rng R"
  unfolding rng_def by auto

lemma rngE:
  assumes "y \<in> rng R" and "R \<subseteq> A \<times> B"
  shows "\<exists>x. \<langle>x, y\<rangle> \<in> R"
proof -
  from assms(1) obtain p where "p \<in> R" and "y = snd p" unfolding rng_def by auto
  with assms(2) have "\<langle>fst p, y\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma dom_empty [simp]: "dom {} = {}"
  unfolding dom_def by auto

lemma rng_empty [simp]: "rng {} = {}"
  unfolding rng_def by auto

lemma dom_subset: "R \<subseteq> A \<times> B \<Longrightarrow> dom R \<subseteq> A"
  unfolding dom_def by auto

lemma rng_subset: "R \<subseteq> A \<times> B \<Longrightarrow> rng R \<subseteq> B"
  unfolding rng_def by auto

lemma bin_union_dom: "dom (R \<union> S) = dom R \<union> dom S"
  unfolding dom_def by (rule extensionality) auto

lemma collect_dom [simp]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  unfolding dom_def by auto

lemma collect_rng [simp]: "rng {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  unfolding rng_def by auto

lemma cons_dom [simp]: "dom (cons \<langle>x, y\<rangle> A) = cons x (dom A)"
  unfolding dom_def by (rule extensionality) auto

lemma cons_rng [simp]: "rng (cons \<langle>x, y\<rangle> A) = cons y (rng A)"
  unfolding rng_def by (rule extensionality) auto


section \<open>Converse relations\<close>

definition converse :: "set \<Rightarrow> set"
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"

lemma rng_is_converse_dom: "rng R = dom (converse R)"
  unfolding rng_def dom_def converse_def
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
  unfolding converse_def by (rule extensionality) auto

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by (rule extensionality) auto

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by (rule extensionality) auto

lemma converse_type [type]: "converse : subset (A \<times> B) \<Rightarrow> subset (B \<times> A)"
  by unfold_types auto


section \<open>Relations on a set\<close>

definition "reflexive A R \<equiv> \<forall>x \<in> A. \<langle>x, x\<rangle> \<in> R"

definition "irreflexive A R \<equiv> \<forall>x \<in> A. \<langle>x, x\<rangle> \<notin> R"

definition "symmetric A R \<equiv> \<forall>x \<in> A. \<forall>y \<in> A. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

definition "antisymmetric A R \<equiv>
  \<forall>x \<in> A. \<forall>y \<in> A. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

definition "transitive A R \<equiv>
  \<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

definition "total A R \<equiv> \<forall>x \<in> A. \<forall>y \<in> A. \<langle>x, y\<rangle> \<in> R \<or> x = y \<or> \<langle>y, x\<rangle> \<in> R"

definition "partially_ordered A R \<equiv>
  reflexive A R \<and> antisymmetric A R \<and> transitive A R"

definition "linearly_ordered A R \<equiv> total A R \<and> partially_ordered A R"


section \<open>Well-founded and well-ordered relations\<close>

definition "well_founded A R \<equiv>
  \<forall>X. X \<subseteq> A \<and> X \<noteq> {} \<longrightarrow> (\<exists>a \<in> X. \<not>(\<exists>x \<in> X. \<langle>x, a\<rangle> \<in> R))"

lemma well_foundedI:
  "(\<And>X. \<lbrakk>X \<subseteq> A; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>a \<in> X. \<not>(\<exists>x \<in> X. \<langle>x, a\<rangle> \<in> R)) \<Longrightarrow> well_founded A R"
  unfolding well_founded_def by auto

definition "well_ordered A R \<equiv> linearly_ordered A R \<and> well_founded A R"


end
