section \<open>Binary relations\<close>

theory Relation
imports Ordered_Pair

begin

definition dom :: "set \<Rightarrow> set"
  where "dom R \<equiv> {fst p | p \<in> R}"

definition rng :: "set \<Rightarrow> set"
  where "rng R \<equiv> {snd p | p \<in> R}"

definition fld :: "set \<Rightarrow> set"
  where "fld R \<equiv> dom R \<union> rng R"


subsection \<open>Domain and range\<close>

lemma domI: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> x \<in> dom R"
  unfolding dom_def by auto

lemma domE:
  assumes "x \<in> dom R" and "R \<subseteq> A \<times> B"
  shows "\<exists>y. \<langle>x, y\<rangle> \<in> R"
proof -
  from assms(1) obtain p where "p \<in> R" and "x = fst p" unfolding dom_def by auto
  with assms(2) have "\<langle>x, snd p\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

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

lemma collect_dom [simp]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  unfolding dom_def by auto

lemma collect_rng [simp]: "rng {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  unfolding rng_def by auto

lemma cons_dom [simp]: "dom (cons \<langle>x, y\<rangle> A) = cons x (dom A)"
  unfolding dom_def by (rule extensionality) auto

lemma cons_rng [simp]: "rng (cons \<langle>x, y\<rangle> A) = cons y (rng A)"
  unfolding rng_def by (rule extensionality) auto


subsection \<open>Converse relations\<close>

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

lemma converse_rel [intro]: "R \<subseteq> A \<times> B \<Longrightarrow> converse R \<subseteq> B \<times> A"
  unfolding converse_def by auto

lemma converse_involution: "R \<subseteq> A \<times> B \<Longrightarrow> converse (converse R) = R"
  unfolding converse_def by auto

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by (rule extensionality) auto

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by (rule extensionality) auto

lemma converse_type [type]: "converse : subset (A \<times> B) \<Rightarrow> subset (B \<times> A)"
  by squash_types auto


subsection \<open>Properties of relations\<close>

definition reflexive :: "set \<Rightarrow> bool"
  where "reflexive R \<equiv> \<forall>x \<in> dom R. \<langle>x, x\<rangle> \<in> R"

definition irreflexive :: "set \<Rightarrow> bool"
  where "irreflexive R \<equiv> \<forall>x \<in> dom R. \<langle>x, x\<rangle> \<notin> R"

definition symmetric :: "set \<Rightarrow> bool"
  where "symmetric R \<equiv> \<forall>x \<in> dom R. \<forall>y \<in> dom R. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

definition antisymmetric :: "set \<Rightarrow> bool"
  where "antisymmetric R \<equiv>
    \<forall>x \<in> dom R. \<forall>y \<in> dom R. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

definition transitive :: "set \<Rightarrow> bool"
  where "transitive R \<equiv>
    \<forall>x \<in> dom R. \<forall>y \<in> dom R. \<forall>z \<in> dom R. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

definition total :: "set \<Rightarrow> bool"
  where "total R \<equiv> \<forall>x \<in> dom R. \<forall>y \<in> dom R. \<langle>x, y\<rangle> \<in> R \<or> x = y \<or> \<langle>y, x\<rangle> \<in> R"



subsection \<open>Some specific results\<close>

lemma Pair_subset: "\<Sum>x\<in> A. (B x) \<subseteq> A \<times> (\<Union>x\<in> A. (B x))"
  by auto

lemma collect_relT:
  assumes "f : element X \<Rightarrow> element A" and "g : element X \<Rightarrow> element B"
  shows "{\<langle>f x, g x\<rangle>. x \<in> X} \<subseteq> A \<times> B"
  using assms by squash_types auto

lemma cons_rel_iff [iff]:
  assumes "x : element A" and "y : element B"
  shows "cons \<langle>x, y\<rangle> X \<subseteq> A \<times> B \<longleftrightarrow> X \<subseteq> A \<times> B"
  using assms by squash_types auto


end
