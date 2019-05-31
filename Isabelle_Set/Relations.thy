section \<open>Relations and functions\<close>

theory Relations
imports Pair

begin

subsection \<open>Relations\<close>

definition relation :: type
  where relation_typedef: "relation = Type (\<lambda>R. \<forall>z \<in> R. \<exists>x y. z = \<langle>x, y\<rangle>)"
(* redefine as subset (A \<times> B)? *)

definition domain :: "set \<Rightarrow> set"
  where "domain R \<equiv> {fst p | p \<in> R}"

definition range :: "set \<Rightarrow> set"
  where "range R \<equiv> {snd p | p \<in> R}"

definition field :: "set \<Rightarrow> set"
  where "field R \<equiv> domain R \<union> range R"


subsection \<open>Various results on relations\<close>

lemma relation_elem_conv:
  "\<lbrakk>x \<in> R; R : relation\<rbrakk> \<Longrightarrow> \<langle>fst x, snd x\<rangle> = x"
  unfolding relation_typedef by auto

lemma relation_subsetI:
  "R : relation \<Longrightarrow> R \<subseteq> domain R \<times> range R"
unfolding domain_def range_def
proof auto
  let ?dom = "{fst x | x \<in> R}" and ?rng = "{snd x | x \<in> R}"
  fix x assume R: "R : relation" and x: "x \<in> R"
  hence "fst x \<in> ?dom" and "snd x \<in> ?rng"
    by auto
  hence "\<langle>fst x, snd x\<rangle> \<in> ?dom \<times> ?rng" by auto
  thus "x \<in> ?dom \<times> ?rng" using R x relation_elem_conv by auto
qed

lemma relation_subsetE [elim]: "\<lbrakk>A \<subseteq> R; R : relation\<rbrakk> \<Longrightarrow> A : relation"
  unfolding relation_typedef by auto

lemma DUnion_rel: "\<Coprod>x \<in> A. (B x) : relation"
  unfolding relation_typedef by auto

corollary cartesian_prod_rel: "A \<times> B : relation"
  by (fact DUnion_rel)

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

definition converse :: "set \<Rightarrow> set" \<comment>\<open>converse of relation\<close>
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"


text \<open>Alternative definition for the range of a relation\<close>

lemma range_def2: "range R = domain (converse R)"
  unfolding range_def domain_def converse_def
  by auto


lemma converse_iff [simp]:
  "R : relation \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def relation_typedef
  by auto

lemma converseI [intro!]:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> R; R : relation\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD:
  "\<lbrakk>\<langle>a, b\<rangle> \<in> converse R; R : relation\<rbrakk> \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]:
  "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> R\<rbrakk> \<Longrightarrow> P; R : relation\<rbrakk> \<Longrightarrow> P"
  unfolding relation_typedef converse_def by auto

lemma converse_subset:
  "R \<subseteq> A \<times> B \<Longrightarrow> converse R \<subseteq> B \<times> A"
  unfolding converse_def by (auto simp: relation_typedef)

(* Our first example of a soft type rule! *)
(* lemma converse_type: "converse: relation \<Rightarrow> relation"
  sorry *)

lemma converse_rel: "R : relation \<Longrightarrow> converse R : relation"
  using
    relation_subsetI[of R]
    converse_subset[of R "domain R" "range R"]
    relation_subsetE
    cartesian_prod_rel
  by auto

lemma converse_involution: "R : relation \<Longrightarrow> converse (converse R) = R"
  unfolding converse_def
  by extensionality (auto simp: relation_elem_conv)

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


end
