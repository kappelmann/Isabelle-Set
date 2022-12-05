section \<open>Binary Relations\<close>
theory Bin_Rels
imports Sets
begin

subsection \<open>Basic Setup\<close>

text \<open>No specific domain and range information; compare section below.\<close>

definition [typedef]: "Bin_Rel \<equiv> type (\<lambda>R. \<forall>p \<in> R. p = \<langle>fst p, snd p\<rangle>)"

lemma Bin_RelI [intro]:
  "(\<And>p. p \<in> R \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p) \<Longrightarrow> R : Bin_Rel"
  by unfold_types auto

lemma Bin_RelI' [intro]:
  "(\<And>p. p \<in> R \<Longrightarrow> \<exists>x y. \<langle>x, y\<rangle> = p) \<Longrightarrow> R : Bin_Rel"
  using fst_def snd_def by (intro Bin_RelI) fastforce

lemma Bin_Rel_if_subset_pairs [intro]:
  "R \<subseteq> A \<times> B \<Longrightarrow> R : Bin_Rel"
  by unfold_types auto

lemma Bin_Rel_fst_snd_eq [simp]:
  "\<lbrakk>R : Bin_Rel; p \<in> R\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by unfold_types auto

lemma Bin_Rel_if_subset_dep_pairs: "R \<subseteq> \<Sum>x \<in> A. (B x) \<Longrightarrow> R : Bin_Rel"
  by auto

lemma Bin_Rel_if_Subset_dep_pairs [derive]:
  "R : Subset(\<Sum>x \<in> A. (B x)) \<Longrightarrow> R : Bin_Rel"
  using Bin_Rel_if_subset_dep_pairs by auto


subsection \<open>Domain\<close>

definition "dom R \<equiv> {fst p | p \<in> R}"

lemma fst_mem_dom_if_mem [intro]: "r \<in> R \<Longrightarrow> fst r \<in> dom R"
  unfolding dom_def by auto

lemma mem_domI [intro]: "\<exists>y. \<langle>x, y\<rangle> \<in> R \<Longrightarrow> x \<in> dom R"
  unfolding dom_def by auto

lemma Bin_Rel_ex_snd_mem_if_mem_dom [elim]:
  assumes "x \<in> dom R" and "R : Bin_Rel"
  obtains y where "\<langle>x, y\<rangle> \<in> R"
proof -
  assume h: "(\<And>y. \<langle>x, y\<rangle> \<in> R \<Longrightarrow> thesis)"
  from \<open>x \<in> dom R\<close> obtain p where "p \<in> R" and "x = fst p"
    unfolding dom_def by auto
  with \<open>R : Bin_Rel\<close> have "\<langle>x, snd p\<rangle> \<in> R" by auto
  then show thesis by (rule h)
qed

lemma Bin_Rel_mem_dom_iff: "R : Bin_Rel \<Longrightarrow> x \<in> dom R \<longleftrightarrow> (\<exists>y. \<langle>x, y\<rangle> \<in> R)"
  by auto

lemma not_mem_domE:
  assumes "x \<notin> dom R"
  obtains "\<And>y. \<langle>x, y\<rangle> \<notin> R"
  using assms unfolding dom_def by force

lemma dom_singleton_pair_eq [iff]: "dom {\<langle>x, y\<rangle>} = {x}"
  unfolding dom_def by auto


subsection \<open>Range\<close>

definition "rng R \<equiv> {snd p | p \<in> R}"

lemma snd_mem_rng_if_mem [intro]:
  "r \<in> R \<Longrightarrow> snd r \<in> rng R"
  unfolding rng_def by auto

lemma mem_rngI [intro]: "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> y \<in> rng R"
  unfolding rng_def by auto

lemma Bin_Rel_ex_fst_mem_if_mem_rng [elim]:
  assumes "y \<in> rng R" and "R : Bin_Rel"
  shows "\<exists>x. \<langle>x, y\<rangle> \<in> R"
proof -
  from \<open>y \<in> rng R\<close> obtain p where "p \<in> R" and "y = snd p"
    unfolding rng_def by auto
  with \<open>R : Bin_Rel\<close> have "\<langle>fst p, y\<rangle> \<in> R" by auto
  then show ?thesis by blast
qed

lemma Bin_Rel_subset_pairs_dom_rng:
  assumes "R : Bin_Rel"
  shows "R \<subseteq> dom R \<times> rng R"
proof
  fix x assume "x \<in> R"
  from assms have x_eq: "x = \<langle>fst x, snd x\<rangle>" by auto
  with \<open>x \<in> R\<close> show "x \<in> dom R \<times> rng R"
    by (subst x_eq, intro iffD2[OF mem_dep_pairs_iff]) auto
qed

lemma Bin_Rel_mem_rng_iff:
  "R : Bin_Rel \<Longrightarrow> y \<in> rng R \<longleftrightarrow> (\<exists>x. \<langle>x, y\<rangle> \<in> R)"
  by auto


subsection \<open>Field\<close>

definition "fld R \<equiv> dom R \<union> rng R"

lemma mem_fld_fst: "\<langle>a, b\<rangle> \<in> R \<Longrightarrow> a \<in> fld R"
  unfolding fld_def by auto

lemma mem_fld_snd: "\<langle>a, b\<rangle> \<in> R \<Longrightarrow> b \<in> fld R"
  unfolding fld_def by auto


subsection \<open>Basic equalities\<close>

lemma dom_empty_eq [iff]: "dom {} = {}"
  unfolding dom_def by auto

lemma rng_empty_eq [iff]: "rng {} = {}"
  unfolding rng_def by auto

lemma dom_union_eq [simp]: "dom (\<Union>X) = \<Union>{dom x | x \<in> X}"
  unfolding dom_def by auto

lemma dom_bin_bin_union_eq [iff]: "dom (R \<union> S) = dom R \<union> dom S"
  unfolding dom_def by auto

lemma dom_collect_eq [iff]: "dom {\<langle>f x, g x\<rangle> | x \<in> A} = {f x | x \<in> A}"
  unfolding dom_def by auto

lemma rng_collect_eq [iff]: "rng {\<langle>f x, g x\<rangle> | x \<in> A} = {g x | x \<in> A}"
  unfolding rng_def by auto

lemma dom_insert_eq [simp]: "dom (cons \<langle>x, y\<rangle> A) = cons x (dom A)"
  unfolding dom_def by (auto simp add: repl_insert_eq)

lemma rng_insert_eq [simp]: "rng (cons \<langle>x, y\<rangle> A) = cons y (rng A)"
  unfolding rng_def by (auto simp add: repl_insert_eq)


subsection \<open>Relations With Specified Domain and Range\<close>

definition [typedef]: "Relation A B \<equiv> Subset (A \<times> B)"

lemma Relation_covariant_dom: "R : Relation A B \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> R : Relation A' B"
  unfolding Relation_def using Subset_covariant by auto

lemma Relation_covariant_rng: "R : Relation A B \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> R : Relation A B'"
  unfolding Relation_def using Subset_covariant by auto

lemma RelationI [derive]:
  "R : Subset (A \<times> B) \<Longrightarrow> R : Relation A B"
  unfolding Relation_def by assumption

lemma Bin_Rel_if_Relation [derive]:
  "R : Relation A B \<Longrightarrow> R : Bin_Rel"
  unfolding Relation_def using Bin_Rel_if_subset_dep_pairs by auto

(*Note the issue with standard typechecking blindly using soft type rules:
  loops occur if the following is declared [derive].*)
lemma Relation_if_Bin_Rel:
  "R : Bin_Rel \<Longrightarrow> R : Relation (dom R) (rng R)"
  by (intro RelationI SubsetI Bin_Rel_subset_pairs_dom_rng)

lemma dom_type [type]: "dom : Relation A B \<Rightarrow> Subset A"
  unfolding dom_def by unfold_types auto

lemma rng_type [type]: "rng : Relation A B \<Rightarrow> Subset B"
  unfolding rng_def by unfold_types auto

text \<open>Set model of \<^term>\<open>Relation A B\<close>.\<close>

definition "relations A B = powerset (A \<times> B)"

lemma Relation_if_mem_relations [iff]: "R \<in> relations A B \<longleftrightarrow> R : Relation A B"
  unfolding relations_def by unfold_types

text \<open>Set relation from HOL relation.\<close>

definition "relation_graph D R \<equiv> {p \<in> D \<times> D | R (fst p) (snd p)}"

lemma pair_mem_relation_graph_iff [iff]:
  "\<langle>x, y\<rangle> \<in> relation_graph D R \<longleftrightarrow> x \<in> D \<and> y \<in> D \<and> R x y"
  unfolding relation_graph_def by auto


subsection \<open>Converse relations\<close>

definition converse :: "set \<Rightarrow> set"
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"

lemma converse_prod [iff]: "converse (A \<times> B) = B \<times> A"
  unfolding converse_def by (rule eq_if_subset_if_subset) auto

lemma converse_empty [iff]: "converse {} = {}"
  unfolding converse_def by (rule eq_if_subset_if_subset) auto

lemma dom_converse_eq_rng: "dom (converse R) = rng R"
  unfolding dom_def rng_def converse_def by auto

lemma Bin_Rel_pair_mem_converse_iff_mem [iff]:
  "R : Bin_Rel \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def by auto

lemma Bin_Rel_mem_converseE [elim]:
  assumes "p \<in> converse R" "R : Bin_Rel"
  obtains x y where "p = \<langle>y, x\<rangle>" and "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding converse_def by auto

lemma converse_type [type]: "converse : Relation A B \<Rightarrow> Relation B A"
  by unfold_types auto

lemma converse_converse_eq_self: "R : Relation A B \<Longrightarrow> converse (converse R) = R"
  (*TODO: this should be provable without using the dest rule by the type checker*)
  unfolding converse_def by (auto dest: Bin_Rel_if_Relation)

subsection \<open>Diagonal of a set\<close>

definition "diag A \<equiv> {\<langle>a, a\<rangle> | a \<in> A}"

lemma diag_type [type]: "diag : (A : Set) \<Rightarrow> Relation A A"
  unfolding diag_def by (auto intro!: RelationI SubsetI)

lemma
  pair_mem_diag_if_mem: "a \<in> A \<Longrightarrow> \<langle>a, a\<rangle> \<in> diag A" and
  fst_mem_if_mem_diag: "u \<in> diag A \<Longrightarrow> fst u \<in> A" and
  snd_mem_if_mem_diag: "u \<in> diag A \<Longrightarrow> snd u \<in> A" and
  fst_eq_snd_if_mem_diag: "u \<in> diag A \<Longrightarrow> fst u = snd u"
  unfolding diag_def by auto


subsection \<open>Composition\<close>

definition "rel_comp S R \<equiv>
  {u \<in> dom R \<times> rng S | \<exists>z. \<langle>fst u, z\<rangle> \<in> R \<and> \<langle>z, snd u\<rangle> \<in> S}"

bundle isa_set_rel_comp_syntax begin notation rel_comp (infixr "\<circ>\<^sub>r" 60) end
bundle no_isa_set_rel_comp_syntax begin no_notation rel_comp (infixr "\<circ>\<^sub>r" 60) end
unbundle isa_set_rel_comp_syntax

lemma rel_comp_type [type]:
  "rel_comp : (S : Relation B C) \<Rightarrow> (R : Relation A B) \<Rightarrow> Relation A C"
  (*TODO: this should work by just using the type-checker*)
  unfolding rel_comp_def by (unfold_types) auto

lemma rel_comp_Relation_if_Bin_Rel [derive]:
  assumes "S : Bin_Rel" "R : Bin_Rel"
  and "dom S : Subset (rng R)"
  shows "S \<circ>\<^sub>r R : Relation (dom R) (rng S)"
proof -
  have "S : Relation (rng R) (rng S)"
    by (rule Relation_covariant_dom[OF Relation_if_Bin_Rel]) discharge_types
  then show ?thesis by (auto dest: Relation_if_Bin_Rel)
qed

lemma mem_rel_comp_if_mem_if_mem [intro]:
  "\<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, z\<rangle> \<in> S \<Longrightarrow> \<langle>x, z\<rangle> \<in> S \<circ>\<^sub>r R"
  unfolding rel_comp_def by auto

lemma mem_rel_compE [elim]:
  assumes "p \<in> S \<circ>\<^sub>r R"
  obtains z where "\<langle>fst p, z\<rangle> \<in> R" and "\<langle>z, snd p\<rangle> \<in> S"
  using assms unfolding rel_comp_def by auto


subsection \<open>Predicates on relations\<close>

definition "reflexive D R \<equiv> \<forall>x \<in> D. \<langle>x, x\<rangle> \<in> R"

definition "irreflexive D R \<equiv> \<forall>x \<in> D. \<langle>x, x\<rangle> \<notin> R"

definition "symmetric D R \<equiv> \<forall>x \<in> D. \<forall>y \<in> D. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

definition "antisymmetric D R \<equiv>
  \<forall>x \<in> D. \<forall>y \<in> D. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

definition "transitive D R \<equiv>
  \<forall>x \<in> D. \<forall>y \<in> D. \<forall>z \<in> D. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

definition "total D R \<equiv> \<forall>x \<in> D. \<forall>y \<in> D. \<langle>x, y\<rangle> \<in> R \<or> x = y \<or> \<langle>y, x\<rangle> \<in> R"

definition "partially_ordered D R \<equiv>
  reflexive D R \<and> antisymmetric D R \<and> transitive D R"

definition "linearly_ordered D R \<equiv> total D R \<and> partially_ordered D R"


subsection \<open>Well-founded and well-ordered relations\<close>

definition "well_founded D R \<equiv>
  \<forall>X. X \<subseteq> D \<and> X \<noteq> {} \<longrightarrow> (\<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<notin> R)"

lemma well_foundedI:
  "(\<And>X. \<lbrakk>X \<subseteq> D; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<notin> R) \<Longrightarrow> well_founded D R"
  unfolding well_founded_def by auto

definition "well_ordered D R \<equiv> linearly_ordered D R \<and> well_founded D R"


end
