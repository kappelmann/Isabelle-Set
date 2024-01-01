theory Ordinal
  imports
    SOrders
    Order_Set
    Pairs
begin

(*don't know which \<le> should be consistent with,
 this one is followed with subsection \<open>Syntactic orders\<close> *)
definition Transset where "Transset x \<equiv> \<forall>y \<in> x. y \<le> x"

definition SOrd where "SOrd x \<equiv> Transset x \<and> (\<forall>y \<in>  x. Transset y)"

(*no 0 defined in this theory*)
lemma Transset_empty [iff]: "Transset {}"
  by (auto simp: Transset_def)

(*similar with x + 1 and adduction*)
definition SOsucc where "SOsucc x = insert x x"

definition Oless_eq where "Oless_eq x y \<equiv> x \<subseteq> y"

lemma Transset_succ [intro]:
  assumes "Transset x" shows "Transset (SOsucc x)"
  using assms
  by (auto simp: Transset_def SOsucc_def Oless_eq_def)

lemma Transset_Sup:
  assumes "\<And>x. x \<in> X \<Longrightarrow> Transset x" shows "Transset (\<Union>X)"
  sorry

lemma Transset_sup:
  assumes "Transset x" "Transset y" shows "Transset (x \<union> y)"
  using Transset_def assms by auto

lemma rev_vsubsetD: "c \<in> a \<Longrightarrow> a \<le> b \<Longrightarrow> c \<in> b"
  by fastforce

lemma Transset_inf: "\<lbrakk>Transset i; Transset j\<rbrakk> \<Longrightarrow> Transset (i \<inter> j)"
  by (auto simp: Transset_def rev_vsubsetD)

lemma Transset_VPow: "Transset(i) \<Longrightarrow> Transset( powerset (i))"
  by (auto simp: Transset_def)

lemma Transset_Inf: "(\<And>i. i \<in> A \<Longrightarrow> Transset i) \<Longrightarrow> Transset (\<Inter> A)"
  by (auto simp: Transset_def) 

lemma SOrd_empty [iff]: "SOrd {}"
  by (auto simp: SOrd_def)

lemma SOrd_succ [intro]:
  assumes "SOrd x" shows "SOrd (SOsucc x)"
  sorry

lemma SOrd_trans: "\<lbrakk> i \<in> j;  j \<in> k;  SOrd k \<rbrakk>  \<Longrightarrow> i \<in> k"
  using SOrd_def Transset_def by auto

lemma SOrd_in_SOrd: "\<lbrakk> SOrd k;  m \<in> k \<rbrakk>  \<Longrightarrow> SOrd m"
  using SOrd_def SOrd_trans by blast

(*important*)
lemma foundation: "wf {\<langle>x, y\<rangle>| x \<in> y}"
  sorry

lemma Ord_induct [consumes 1, case_names step]:
  assumes k: "SOrd k"
      and step: "\<And>x.\<lbrakk> SOrd x; \<And>y. y \<in> x \<Longrightarrow> P y \<rbrakk>  \<Longrightarrow> P x"
    shows "P k"
  using foundation k
proof (induction k rule: mem_induction)
  case (mem X)
  then show ?case 
    using SOrd_in_SOrd local.step by auto
qed

definition SLimit :: "set \<Rightarrow> bool"
  where "SLimit i \<equiv> SOrd i \<and> {} \<in>  i \<and> (\<forall>y. y \<in> i \<longrightarrow> SOsucc y \<in> i)"

lemma Ord_induct3 [consumes 1, case_names 0 succ Limit, induct type: set]:
  assumes a: "SOrd a"
      and P: "P {}" "\<And>a. \<lbrakk> SOrd a; P a \<rbrakk> \<Longrightarrow> P (SOsucc a)"
             "\<And>a. \<lbrakk> SLimit a; \<And>b. b \<in> \<alpha> \<Longrightarrow> P b \<rbrakk> \<Longrightarrow> P (\<Union>b \<in> a. b)"
           shows "P a"
  using a
proof (induction a rule: Ord_induct)
  case (step x)
  then show ?case sorry
qed


end