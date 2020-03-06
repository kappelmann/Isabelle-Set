chapter \<open>Ordinals\<close>

theory Ordinal
imports Subset

begin

text \<open>
  The class of ordinal numbers is defined abstractly, as the \<in>-transitive sets
  whose members are also \<in>-transitive.
\<close>

definition [typedef]:
  "Ord \<equiv> type (\<lambda>x. mem_transitive x \<and> (\<forall>y \<in> x. mem_transitive y))"

lemma OrdI:
  "mem_transitive X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> mem_transitive x) \<Longrightarrow> X: Ord"
  unfolding Ord_def by (auto simp: has_type_type)

text \<open>Basic properties of ordinals:\<close>

lemma Ord_mem_closed [elim]: "x : Ord \<Longrightarrow> y \<in> x \<Longrightarrow> y : Ord"
  by unfold_types (fastforce simp: mem_transitive_def)

lemma Ord_mem_transitive: "x: Ord \<Longrightarrow> mem_transitive x"
  by unfold_types

lemma Ord_mem_transitive' [elim]: "x : Ord \<Longrightarrow> y \<in> x \<Longrightarrow> y \<subseteq> x"
  by unfold_types (fastforce simp: mem_transitive_def)

lemma [derive]: "x: Ord \<Longrightarrow> y: element x \<Longrightarrow> y: subset x"
  by (fold element_type_iff subset_type_iff) (fact Ord_mem_transitive')

(*Adapted from a proof by Chad Brown*)
lemma Ord_trichotomy_aux:
  "X : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> X \<notin> Y \<Longrightarrow> Y \<notin> X \<Longrightarrow> X = Y"
proof (induction X Y rule: mem_double_induct)
  fix X Y
  assume
    ord: "X : Ord" "Y : Ord" and
    IH1: "\<And>x. x \<in> X \<Longrightarrow> x : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> x \<notin> Y \<Longrightarrow> Y \<notin> x \<Longrightarrow> x = Y" and
    IH2: "\<And>y. y \<in> Y \<Longrightarrow> X : Ord \<Longrightarrow> y : Ord \<Longrightarrow> X \<notin> y \<Longrightarrow> y \<notin> X \<Longrightarrow> X = y" and
    *: "X \<notin> Y" "Y \<notin> X"
  show "X = Y"
  proof (rule equalityI)
    fix x assume "x \<in> X"
    with ord have "x \<subseteq> X" "x : Ord" by (auto elim!: Ord_mem_transitive')
    with * ord IH1 \<open>x \<in> X\<close> show "x \<in> Y" by blast
  next
    fix y assume "y \<in> Y"
    with ord have "y \<subseteq> Y" "y : Ord" by (auto elim!: Ord_mem_transitive')
    with * ord IH2 \<open>y \<in> Y\<close> show "y \<in> X" by blast
  qed
qed

lemma Ord_trichotomy: "\<lbrakk>X: Ord; Y: Ord\<rbrakk> \<Longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X"
  using Ord_trichotomy_aux by auto

lemma emptyset_Ord [type]: "{} : Ord"
  by unfold_types auto


section \<open>Successor ordinals\<close>

definition succ where "succ x \<equiv> x \<union> {x}"

lemma succ_Ord [derive]: "x : Ord \<Longrightarrow> succ x : Ord"
  unfolding succ_def by unfold_types (fastforce simp: mem_transitive_def)

text \<open>Simp rules\<close>

lemma succ_empty [simp]: "succ {} = {{}}"
  by (auto simp: succ_def)

lemma succ_succ_empty [simp]: "succ (succ {}) = {{}} \<union> {succ {}}"
  by (auto simp: succ_def)

lemma succ_neq [simp]: "x \<noteq> succ x"
  by (auto simp: succ_def)

lemma succ_not_empty [simp]: "succ x \<noteq> {}"
  unfolding succ_def by auto

lemmas empty_not_succ = succ_not_empty[symmetric, simp]

lemmas
  succ_emptyE = notE[OF succ_not_empty] and
  empty_succE = notE[OF empty_not_succ]

lemma succ_inject [dest]: "succ x = succ y \<Longrightarrow> x = y"
proof (rule ccontr)
  assume succ_eq: "succ x = succ y"
  assume neq: "x \<noteq> y"

  have "x \<in> succ x" unfolding succ_def by blast
  with succ_eq have "x \<in> succ y" by simp
  with neq have "x \<in> y" unfolding succ_def by blast

  have "y \<in> succ y" unfolding succ_def by blast
  with succ_eq have "y \<in> succ x" by simp
  with neq have "y \<in> x" unfolding succ_def by blast

  from \<open>x \<in> y\<close> \<open>y \<in> x\<close> show False using mem_asym by blast
qed

lemma succ_inject' [simp]:
  "x \<noteq> y \<Longrightarrow> succ x \<noteq> succ y"
  by auto

lemma succ_mem [simp]: "x \<in> succ x"
  unfolding succ_def by auto

lemma [derive]: "x: element (succ x)"
  by unfold_types auto

lemma succ_memI [simp]: "x \<in> y \<Longrightarrow> x \<in> succ y"
  unfolding succ_def by auto

lemma [derive]: "x : element y \<Longrightarrow> x : element (succ y)"
  by unfold_types auto

lemma succ_mem_not_eq [simp]:
  "x \<in> succ y \<Longrightarrow> x \<noteq> (succ y)"
  by (rule mem_imp_not_eq)

lemma succ_not_mem [simp]:
  "succ x \<notin> x"
  unfolding succ_def by (blast dest: mem_asym)

lemma succ_cases [elim]:
  assumes "x \<in> succ y"
      and "\<And>x. x \<in> y \<Longrightarrow> P x"
      and "P y"
  shows "P x"
  using assms unfolding succ_def by auto

lemma Univ_succ_closed [intro]: "x \<in> Univ X \<Longrightarrow> succ x \<in> Univ X"
  unfolding succ_def by auto

lemma [derive]: "x : element (Univ X) \<Longrightarrow> succ x : element (Univ X)"
  by unfold_types auto


section \<open>\<omega>, the smallest infinite ordinal\<close>

definition "omega_op X = {{}} \<union> Repl X succ"

lemma omega_op_monop: "omega_op : monop V"
  unfolding omega_op_def by (fast intro: monopI)

definition omega ("\<omega>")
  where "\<omega> = lfp V omega_op"

lemma omega_unfold: "\<omega> = {{}} \<union> {succ n | n \<in> \<omega>}"
  unfolding omega_def
  by (subst lfp_unfold[OF omega_op_monop]) (auto simp: omega_op_def)

lemma empty_in_omega [simp]: "{} \<in> \<omega>"
  by (subst omega_unfold, auto)

lemma succ_omega [simp]: "n \<in> \<omega> \<Longrightarrow> succ n \<in> \<omega>"
  by (subst omega_unfold, auto)

lemma [type]: "{}: element \<omega>" by unfold_types auto
lemma [type]: "succ: element \<omega> \<Rightarrow> element \<omega>" by unfold_types auto

lemma omega_cases_raw:
  assumes "n \<in> \<omega>"
      and "P {}"
      and "\<And>n. n \<in> \<omega> \<Longrightarrow> P (succ n)"
  shows "P n"
  by (rule def_lfp_induct)
     (auto intro: assms omega_op_monop omega_def simp: omega_op_def)

lemma omega_cases [case_names empty succ]:
  assumes "n \<in> \<omega>"
  obtains "n = {}" | k where "k \<in> \<omega>" "n = succ k"
  using assms omega_cases_raw[where ?P="\<lambda>k. n = k \<longrightarrow> thesis"] by blast

lemma omega_induct [case_names empty succ, induct set: omega]:
  assumes "n \<in> \<omega>"
      and "P {}"
      and "\<And>n. \<lbrakk>n \<in> \<omega>; P n\<rbrakk> \<Longrightarrow> P (succ n)"
  shows "P n"
  by (rule def_lfp_induct)
     (auto intro: assms omega_op_monop omega_def simp: omega_op_def)

lemma omega_empty_in_succ:
  "n \<in> \<omega> \<Longrightarrow> {} \<in> succ n"
  by (induction n rule: omega_induct) (auto simp: succ_def)

lemma omega_succ_mem_monotone [intro]:
  "\<lbrakk>n \<in> \<omega>; m \<in> n\<rbrakk> \<Longrightarrow> succ m \<in> succ n"
  by (induction n rule: omega_induct) (auto simp: succ_def)

(*Characterizes the elements of \<omega> as {} or succ n for some n \<in> \<omega>*)
lemma omega_elems [rule_format]:
  "n \<in> \<omega> \<Longrightarrow> n \<noteq> {} \<longrightarrow> (\<exists>!m\<in> \<omega>. n = succ m)"
  by (erule omega_cases) auto

lemma omega_Ord: "\<omega>: Ord"
proof (rule OrdI, unfold mem_transitive_def; rule allI, rule impI)
  fix x assume "x \<in> \<omega>"
  thus "x \<subseteq> \<omega>"
    by (induction x rule: omega_induct) (auto simp: succ_def)

  fix y assume "y \<in> x"
  with \<open>x \<in> \<omega>\<close> show "y \<subseteq> x"
    by (induction x rule: omega_induct) (auto simp: succ_def)
qed

lemma omega_elem_Ord: "n \<in> \<omega> \<Longrightarrow> n: Ord"
  using omega_Ord Ord_mem_closed by auto

lemma omega_elem_mem_transitive: "n \<in> \<omega> \<Longrightarrow> mem_transitive n"
  using omega_elem_Ord Ord_mem_transitive by auto

lemma omega_elem_mem_transitive': "\<lbrakk>n \<in> \<omega>; m \<in> n; k \<in> m\<rbrakk> \<Longrightarrow> k \<in> n"
  using omega_elem_mem_transitive unfolding mem_transitive_def by auto

lemma [derive]: "n: element \<omega> \<Longrightarrow> mem_transitive n"
  by unfold_types (fact omega_elem_mem_transitive)

lemma omega_elem_subset: "n \<in> \<omega> \<Longrightarrow> n \<subseteq> \<omega>"
  using omega_Ord Ord_mem_transitive' by auto

lemma omega_mem_transitive: "x \<in> \<omega> \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> \<omega>"
  using omega_elem_subset by auto

lemma [derive]: "x: element \<omega> \<Longrightarrow> y: element x \<Longrightarrow> y: element \<omega>"
  by unfold_types (fact omega_mem_transitive)

lemma omega_succ_mem_monotoneE:
  assumes "n \<in> \<omega>" and "succ m \<in> succ n"
  shows "m \<in> n"
proof -
  have "mem_transitive (succ n)" using assms by auto
  hence "succ m \<subseteq> succ n" using assms mem_transitiveE by auto
  hence "m \<in> n \<union> {n}" unfolding succ_def by auto
  then show "m \<in> n" using assms by auto
qed


end
