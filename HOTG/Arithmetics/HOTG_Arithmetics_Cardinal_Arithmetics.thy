\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Compatibility of Set Arithmetics and Cardinal Arithmetics\<close>
theory HOTG_Arithmetics_Cardinal_Arithmetics
  imports
    HOTG_Bounded_Definite_Description
    HOTG_Cardinals_Addition
    HOTG_Cardinals_Multiplication
    HOTG_Addition
    HOTG_Multiplication
begin

unbundle no HOL_groups_syntax
  and no HOL_order_syntax

lemma cardinality_lift_eq_cardinality_right [simp]: "|lift X Y| = |Y|"
proof (intro cardinality_eq_if_equipollent equipollentI)
  let ?f = "\<lambda>z. (THE y : Y. z = X + y)"
  let ?g = "((+) X)"
  from injective_on_if_inverse_on show "bijection_on (lift X Y) Y ?f ?g"
    by (urule bijection_onI dep_mono_wrt_predI where chained = insert)+
    (auto intro: pred_btheI[of "\<lambda>x. x \<in> Y"] simp: lift_eq_repl_add mem_of_eq)
qed

text\<open>The next theorem shows that set addition is compatible with cardinality addition.\<close>

theorem cardinality_add_eq_cardinal_add: "|X + Y| = X \<oplus> Y"
  unfolding add_eq_bin_union_lift
  by (subst cardinality_bin_union_eq_cardinal_add_if_disjoint[OF disjoint_lift_self_right],
    subst cardinality_cardinal_add_eq_cardinal_add[symmetric])
  (simp add: cardinality_lift_eq_cardinality_right)

text\<open>The next theorems show that set multiplication is compatible with cardinality multiplication.\<close>

lemma mul_equipollent_pair: "X * Y \<approx> X \<times> Y"
proof -
  define f :: "set \<Rightarrow> set" where "f \<equiv> \<lambda>\<langle>x, y\<rangle>. X * y + x"
  have "injective_on (X \<times> Y :: set) f"
  proof (urule injective_onI)
    fix p\<^sub>1 p\<^sub>2 presume asms: "p\<^sub>1 \<in> X \<times> Y" "p\<^sub>2 \<in> X \<times> Y" "f p\<^sub>1 = f p\<^sub>2"
    then obtain x\<^sub>1 y\<^sub>1 where "x\<^sub>1 \<in> X" "y\<^sub>1 \<in> Y" "p\<^sub>1 = \<langle>x\<^sub>1, y\<^sub>1\<rangle>" by auto
    moreover from asms obtain x\<^sub>2 y\<^sub>2 where "x\<^sub>2 \<in> X" "y\<^sub>2 \<in> Y" "p\<^sub>2 = \<langle>x\<^sub>2, y\<^sub>2\<rangle>" by auto
    ultimately have "X * y\<^sub>1 + x\<^sub>1 = X * y\<^sub>2 + x\<^sub>2" using f_def \<open>f p\<^sub>1 = f p\<^sub>2\<close> by auto
    moreover have "x\<^sub>1 < X \<and> x\<^sub>2 < X" using \<open>x\<^sub>1 \<in> X\<close> \<open>x\<^sub>2 \<in> X\<close> lt_if_mem by auto
    ultimately have "x\<^sub>1 = x\<^sub>2 \<and> y\<^sub>1 = y\<^sub>2" using eq_if_mul_add_eq_mul_add_if_lt by blast
    then show "p\<^sub>1 = p\<^sub>2" using \<open>p\<^sub>1 = \<langle>x\<^sub>1, y\<^sub>1\<rangle>\<close> \<open>p\<^sub>2 = \<langle>x\<^sub>2, y\<^sub>2\<rangle>\<close> by auto
  qed auto
  then obtain g where "bijection_on (X \<times> Y) (image f (X \<times> Y)) f g"
    using bijection_on_image_the_inverse_on_if_injective_on by blast
  moreover have "image f (X \<times> Y) = X * Y"
    unfolding mul_eq_idx_union_repl_mul_add[of X Y] f_def by fastforce
  ultimately show ?thesis by (intro equipollentI) fastforce
qed

theorem cardinality_mul_eq_cardinal_mul: "|X * Y| = X \<otimes> Y"
  unfolding cardinal_mul_eq_cardinality_pair
  by (intro cardinality_eq_if_equipollent mul_equipollent_pair)

end

