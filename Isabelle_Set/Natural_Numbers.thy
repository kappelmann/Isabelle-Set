theory Natural_Numbers
imports Ordinal

begin

definition "nat_op N = {{}} \<union> Repl N succ"

lemma nat_op_monop: "nat_op : monop (Univ {})"
  unfolding nat_op_def by squash_types (auto intro!: monotoneI)


definition NAT ("\<nat>") where
  "\<nat> = lfp (Univ {}) nat_op"

lemma NAT_unfold: "\<nat> = { {} } \<union> { succ n | n \<in> \<nat>}"
  unfolding NAT_def
  by (subst lfp_unfold[OF _ nat_op_monop]) (auto simp: nat_op_def)


lemma zero_nat[simp]: "{} \<in> \<nat>"
  by (subst NAT_unfold) auto

lemma succ_nat[simp]: "n \<in> \<nat> \<Longrightarrow> succ n \<in> \<nat>"
  by (subst NAT_unfold) auto

lemma nat_induct[case_names 0 succ, induct set: NAT]:
  assumes nat: "n \<in> \<nat>"
  and "P {}"
  and "\<And>n. n \<in> \<nat> \<Longrightarrow> P n \<Longrightarrow> P (succ n)"
shows "P n"
  apply (rule Set_Lattice.def_lfp_induct[OF any_typeI nat_op_monop NAT_def, unfolded nat_op_def])
   by (insert assms) auto

definition nat_typedef[squash]: "nat = element \<nat>"

lemma nat_induct_typed[case_names 0 succ, induct set: NAT]:
  assumes nat: "n : nat"
  and "P {}"
  and "\<And>n. n : nat \<Longrightarrow> P n \<Longrightarrow> P (succ n)"
shows "P n"
  using assms nat_induct by squash_types auto

lemma nat_is_ord: "x : nat \<Longrightarrow> x : Ord"
  by (induct x rule: nat_induct_typed) (auto intro: succ_Ord)

lemma zero_type: "{} : nat" by squash_types auto
lemma succ_type: "succ : nat \<Rightarrow> nat" by squash_types auto


subsection \<open>Less-than relation\<close>

text \<open>This symbol will later be overloaded, but we skip this for now...\<close>

(* inductive package *)
axiomatization less_than (infix "<" 50) where
  less_than1: "n : nat \<Longrightarrow> n < Succ n" and
  less_than2: "n : nat \<Longrightarrow> m : nat \<Longrightarrow> n < m \<Longrightarrow> n < Succ m"


end
