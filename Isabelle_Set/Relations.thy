section \<open>Relations\<close>

theory Relations
imports Pair

begin

subsection \<open>Relations and functions\<close>

definition is_binrel :: "set \<Rightarrow> bool" \<comment>\<open>recognizes sets of pairs\<close>
  where "is_binrel r \<equiv> \<forall>z \<in> r. \<exists>x y. z = \<langle>x, y\<rangle>"

definition relation :: "set type" \<comment>\<open>type of binary relations\<close>
  where relation_typedef: "relation = Type is_binrel"


definition converse :: "set \<Rightarrow> set" \<comment>\<open>converse of relation\<close>
  where "converse R \<equiv> {\<langle>snd p, fst p\<rangle> | p \<in> R}"

definition domain :: "set \<Rightarrow> set"
  where "domain R \<equiv> {fst p | p \<in> R}"

definition range :: "set \<Rightarrow> set"
  where "range R \<equiv> {snd p | p \<in> R}"

definition field :: "set \<Rightarrow> set"
  where "field R \<equiv> domain R \<union> range R"


lemma range_alt_def: "R : relation \<Longrightarrow> range R = domain (range R)"
  sorry

lemma converse_iff [simp]: "R : relation \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  unfolding converse_def relation_typedef is_binrel_def
  by auto

lemma converseI [intro!]: "R : relation \<Longrightarrow> \<langle>a, b\<rangle> \<in> R \<Longrightarrow> \<langle>b, a\<rangle> \<in> converse R"
  by auto

lemma converseD: "R : relation \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<Longrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma converseE [elim!]: "\<lbrakk>p \<in> converse R; \<And>x y. \<lbrakk>p = \<langle>y, x\<rangle>; \<langle>x, y\<rangle> \<in> r\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  sorry

lemma converse_subset: "r \<subseteq> A \<times> B \<Longrightarrow> converse R \<subseteq> B \<times> A"
  by auto

(* TODO

lemma converse_converse: "r \<subseteq> Sigma A B \<Longrightarrow> converse (converse r) = r"
by blast

lemma converse_prod [simp]: "converse(A\<times>B) = B\<times>A"
by blast

lemma converse_empty [simp]: "converse({}) = {}"
by blast
*)

end