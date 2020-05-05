chapter \<open>Binary relations\<close>

theory BinRel
imports Ordered_Pairs

begin


section \<open>Generic notion of a binary relation\<close>

text \<open>No specific domain and range information; compare section below.\<close>

definition [typedef]:
  "BinRel \<equiv> type (\<lambda>R. \<forall>u \<in> R. u = \<langle>fst u, snd u\<rangle>)"

lemma BinRelI [intro]:
  "(\<And>u. u \<in> R \<Longrightarrow> u = \<langle>fst u, snd u\<rangle>) \<Longrightarrow> R: BinRel"
  by unfold_types auto

lemma BinRelI' [intro]:
  "(\<And>u. u \<in> R \<Longrightarrow> \<exists>x y. u = \<langle>x, y\<rangle>) \<Longrightarrow> R: BinRel"
  apply (rule BinRelI)
  using fst_def snd_def by fastforce

lemma subset_prodset_imp_BinRel [intro]:
  "R \<subseteq> A \<times> B \<Longrightarrow> R: BinRel"
  by unfold_types auto

lemma BinRel_elem_eq [simp]:
  "\<lbrakk>R: BinRel; u \<in> R\<rbrakk> \<Longrightarrow> \<langle>fst u, snd u\<rangle> = u"
  by unfold_types auto


section \<open>Domain\<close>

definition "dom R \<equiv> {fst p | p \<in> R}"

lemma domI [intro]:
  "r \<in> R \<Longrightarrow> fst r \<in> dom R"
  unfolding dom_def by auto

lemma domI' [intro]: "\<exists>y. \<langle>x, y\<rangle> \<in> R \<Longrightarrow> x \<in> dom R"
  unfolding dom_def by auto

lemma domE [elim]:
  assumes "x \<in> dom R" and "R: BinRel"
  shows "\<exists>y. \<langle>x, y\<rangle> \<in> R"
proof -
  from assms(1) obtain p where "p \<in> R" and "x = fst p" unfolding dom_def by auto
  with assms(2) have "\<langle>x, snd p\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma dom_iff [iff]:
  "R: BinRel \<Longrightarrow> x \<in> dom R \<longleftrightarrow> (\<exists>y. \<langle>x, y\<rangle> \<in> R)"
  by auto

lemma not_in_domE: "\<lbrakk>x \<notin> dom R; \<not>(\<exists>y. \<langle>x, y\<rangle> \<in> R) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding dom_def by force

lemma dom_singleton_opair [simp]:
  "dom {\<langle>x, y\<rangle>} = {x}"
  unfolding dom_def by auto


section \<open>Range\<close>

definition "rng R \<equiv> {snd p | p \<in> R}"

lemma rngI [intro]:
  "r \<in> R \<Longrightarrow> snd r \<in> rng R"
  unfolding rng_def by auto

lemma rngI' [intro]: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> y \<in> rng R"
  unfolding rng_def by auto

lemma rngE [elim]:
  assumes "y \<in> rng R" and "R: BinRel"
  shows "\<exists>x. \<langle>x, y\<rangle> \<in> R"
proof -
  from assms(1) obtain p where "p \<in> R" and "y = snd p" unfolding rng_def by auto
  with assms(2) have "\<langle>fst p, y\<rangle> \<in> R" by auto
  thus ?thesis ..
qed

lemma BinRel_imp_subset_prodset [elim]:
  assumes "R: BinRel"
  shows "R \<subseteq> dom R \<times> rng R"
proof
  fix x assume "x \<in> R"
  from assms have "x = \<langle>fst x, snd x\<rangle>" by auto
  with \<open>x \<in> R\<close> show "x \<in> dom R \<times> rng R" by auto
qed

lemma rng_iff [iff]:
  "R: BinRel \<Longrightarrow> y \<in> rng R \<longleftrightarrow> (\<exists>x. \<langle>x, y\<rangle> \<in> R)"
  by auto


section \<open>Field\<close>

definition "fld R \<equiv> dom R \<union> rng R"

lemma fldI1: "\<langle>a, b\<rangle> \<in> R \<Longrightarrow> a \<in> fld R"
  unfolding fld_def by auto

lemma fldI2: "\<langle>a, b\<rangle> \<in> R \<Longrightarrow> b \<in> fld R"
  unfolding fld_def by auto


section \<open>Basic equalities\<close>

lemma dom_empty [simp]: "dom {} = {}"
  unfolding dom_def by auto

lemma rng_empty [simp]: "rng {} = {}"
  unfolding rng_def by auto

lemma union_dom: "dom (\<Union>X) = \<Union>{dom x | x \<in> X}"
  unfolding dom_def by (rule equalityI) auto

lemma bin_union_dom: "dom (R \<union> S) = dom R \<union> dom S"
  unfolding dom_def by (rule equalityI) auto

lemma collect_dom [simp]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  unfolding dom_def by auto

lemma collect_rng [simp]: "rng {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  unfolding rng_def by auto

lemma cons_dom [simp]: "dom (cons \<langle>x, y\<rangle> A) = cons x (dom A)"
  unfolding dom_def by (rule extensionality) auto

lemma cons_rng [simp]: "rng (cons \<langle>x, y\<rangle> A) = cons y (rng A)"
  unfolding rng_def by (rule extensionality) auto


section \<open>Relations from A to B\<close>

definition [typedef]: "Relation A B \<equiv> Subset (A \<times> B)"

lemma RelationI [derive]:
  "R: Subset (A \<times> B) \<Longrightarrow> R: Relation A B"
  unfolding Relation_def .

lemma Relation_imp_BinRel [derive]:
  "R: Relation A B \<Longrightarrow> R: BinRel"
  unfolding Relation_def by auto

(*Note the issue with standard typechecking blindly using soft type rules:
  loops occur if the following is declared [derive].*)
lemma BinRel_imp_Relation:
  "R: BinRel \<Longrightarrow> R: Relation (dom R) (rng R)"
  by (intro RelationI SubsetI BinRel_imp_subset_prodset)

lemma dom_type [type]:
  "dom: Relation A B \<Rightarrow> Subset A"
  by unfold_types auto

lemma rng_type [type]:
  "rng: Relation A B \<Rightarrow> Subset B"
  by unfold_types auto

text \<open>Set model of \<^term>\<open>Relation A B\<close>.\<close>

definition "relation A B \<equiv> powerset (A \<times> B)"

lemma relation_models_Relation [iff]:
  "R \<in> relation A B \<longleftrightarrow> R: Relation A B"
  unfolding relation_def by unfold_types

text \<open>Set relation from HOL relation.\<close>

definition "relation_graph A R \<equiv> {p \<in> A \<times> A | R (fst p) (snd p)}"

lemma relation_graph_iff [iff]:
  "\<langle>x, y\<rangle> \<in> relation_graph A R \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> R x y"
  unfolding relation_graph_def by auto


section \<open>Converse relations\<close>

definition converse :: "set \<Rightarrow> set"
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"

lemma dom_converse_eq_rng: "dom (converse R) = rng R"
  unfolding rng_def dom_def converse_def
  by auto

lemma converse_iff [simp]:
  "R: BinRel \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def by auto

lemma converseI [intro!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> R; R: BinRel\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> converse R; R: BinRel\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]:
  "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> P; R: BinRel\<rbrakk> \<Longrightarrow> P"
  unfolding converse_def by auto

lemma converse_prod [simp]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by (rule extensionality) auto

lemma converse_empty [simp]: "converse {} = {}"
  unfolding converse_def by (rule extensionality) auto

lemma converse_type [type]: "converse: Relation A B \<Rightarrow> Relation B A"
  by unfold_types auto

lemma converse_involution: "R: Relation A B \<Longrightarrow> converse (converse R) = R"
  unfolding converse_def by unfold_types (rule extensionality, auto)


section \<open>Diagonal of a set\<close>

definition "diag A \<equiv> {\<langle>a, a\<rangle> | a \<in> A}"

lemma diag_Relation [type]: "diag A: Relation A A"
  unfolding diag_def by (intro RelationI SubsetI) auto

lemma
  diagI: "a \<in> A \<Longrightarrow> \<langle>a, a\<rangle> \<in> diag A" and
  diagE1: "u \<in> diag A \<Longrightarrow> fst u \<in> A" and
  diagE2: "u \<in> diag A \<Longrightarrow> snd u \<in> A" and
  diag_fst_eq_snd: "u \<in> diag A \<Longrightarrow> fst u = snd u"
  unfolding diag_def by auto


section \<open>Composition\<close>

definition rel_comp (infixr "\<circ>\<^sub>r" 60)
  where "S \<circ>\<^sub>r R \<equiv> {u \<in> dom R \<times> rng S | \<exists>z. \<langle>fst u, z\<rangle> \<in> R \<and> \<langle>z, snd u\<rangle> \<in> S}"

lemma rel_comp_Relation [derive]:
  "\<lbrakk>R: Relation A B; S: Relation B C\<rbrakk> \<Longrightarrow> S \<circ>\<^sub>r R: Relation A C"
  by unfold_types (auto simp: rel_comp_def)

text \<open>Need a version with weaker premises too:\<close>

lemma rel_comp_Relation' [derive]:
  "\<lbrakk>R: Relation A B; S: Relation C D; C: Subset B\<rbrakk> \<Longrightarrow> S \<circ>\<^sub>r R: Relation A D"
  unfolding rel_comp_def
  by unfold_types auto

lemma rel_comp_BinRel [derive]:
  "\<lbrakk>R: BinRel; S: BinRel; dom S: Subset (rng R)\<rbrakk>
    \<Longrightarrow> S \<circ>\<^sub>r R: Relation (dom R) (rng S)"
  by (drule BinRel_imp_Relation)+ (rule rel_comp_Relation')

lemma rel_compI [intro]:
  "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, z\<rangle> \<in> S \<Longrightarrow> \<langle>x, z\<rangle> \<in> S \<circ>\<^sub>r R"
  unfolding rel_comp_def by auto

lemma rel_compE [elim]:
  assumes "p \<in> S \<circ>\<^sub>r R"
  obtains z where "\<langle>fst p, z\<rangle> \<in> R" and "\<langle>z, snd p\<rangle> \<in> S"
  using assms unfolding rel_comp_def by auto


section \<open>Predicates on relations\<close>

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
