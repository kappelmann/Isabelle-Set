theory HOTG_Order_Type
  imports 
    HOTG_Ordinals_Base
    HOTG_Replacement_Predicates
    HOTG_Binary_Relations_Wellorder
    HOTG_Functions_Bijection
    HOTG_Functions_Injective
    Binary_Relation_Isomorphism
begin

unbundle no_HOL_ascii_syntax

lemma bex_ordinal_rel_isomorphic_if_wellorder_on:
  fixes X :: set and R :: "set \<Rightarrow> set \<Rightarrow> bool" (infixl "\<prec>" 50)
  assumes "wellorder_on X (\<prec>)"
  shows "\<exists>\<nu> : ordinal. rel_isomorphic (mem_of X) (mem_of \<nu>) (\<prec>) (\<in>)"
proof -
  let ?step = "\<lambda>nr x. {\<alpha> | y \<in> X, y \<prec> x \<and> \<alpha> = nr y}"
  define nr :: "set \<Rightarrow> set" where "nr = wfrec_on X (\<prec>) ?step"
  define \<nu> :: set where "\<nu> = image nr X"
  have nr_eq: "nr x = ?step nr x" if "x \<in> X" for x
  proof -
    have "R\<restriction>\<^bsub>mem_of X\<^esub>\<upharpoonleft>\<^bsub>mem_of X\<^esub> y x" if "y \<in> X" "y \<prec> x" for y
      using \<open>x \<in> X\<close> that by blast
    then have "(fun_rel_restrict nr R\<restriction>\<^bsub>mem_of X\<^esub>\<upharpoonleft>\<^bsub>mem_of X\<^esub> x) y = nr y" if "y \<in> X" "y \<prec> x" for y
      using that by auto
    moreover have "nr x = ?step (fun_rel_restrict nr R\<restriction>\<^bsub>mem_of X\<^esub>\<upharpoonleft>\<^bsub>mem_of X\<^esub> x) x"
      using assms by (fastforce simp: nr_def wfrec_on_eq)
    ultimately show ?thesis by auto
  qed
  then have nr_hom: "nr y \<in> nr x" if "x \<in> X" "y \<in> X" "y \<prec> x" for x y using that by blast
  have "mem_trans_closed (nr x)" if "x \<in> X" for x
  proof -
    have "\<beta> \<in> nr x" if "\<alpha> \<in> nr x" "\<beta> \<in> \<alpha>" for \<alpha> \<beta>
    proof -
      obtain y where "y \<in> X" "y \<prec> x" "\<alpha> = nr y" using \<open>\<alpha> \<in> nr x\<close> \<open>x \<in> X\<close> nr_eq by blast
      then obtain z where "z \<in> X" "z \<prec> y" "\<beta> = nr z" using \<open>\<beta> \<in> \<alpha>\<close> nr_eq by blast
      have "z \<prec> x" using \<open>z \<prec> y\<close> \<open>y \<prec> x\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>z \<in> X\<close> assms 
        by (blast dest: transitive_onD)
      then show ?thesis using \<open>\<beta> = nr z\<close> \<open>x \<in> X\<close> \<open>z \<in> X\<close> nr_hom by auto
    qed
    then show ?thesis by blast
  qed
  then have "mem_trans_closed \<alpha>" if "\<alpha> \<in> \<nu>" for \<alpha> using that unfolding \<nu>_def nr_eq by auto
  moreover have "mem_trans_closed \<nu>" unfolding \<nu>_def using nr_eq by force
  ultimately have "ordinal \<nu>" by (blast intro: ordinal_if_mem_trans_closedI)
  have "injective_on X nr"
  proof (urule injective_onI)
    fix x y presume "x \<in> X" "y \<in> X" "nr x = nr y"
    then show "x = y" using nr_hom assms by (blast elim!: connected_onE)
  qed auto
  then obtain e where "bijection_on X \<nu> nr e" 
    unfolding \<nu>_def using bijection_on_has_inverse_on_the_inverse_on_if_injective_on by auto
  then have "rel_isomorphism (mem_of X) (mem_of \<nu>) (\<prec>) (\<in>) nr e"
    using nr_hom assms \<open>ordinal \<nu>\<close> wellorder_on_mem_if_ordinal  
    by (blast intro!: rel_isomorphism_if_strict_linear_order_onI)
  then show ?thesis using \<open>ordinal \<nu>\<close> by blast
qed

lemma rel_isomorphism_trivial_if_ordinal_to_ordinal:
  assumes "ordinal \<alpha>" "ordinal \<alpha>'" and iso: "rel_isomorphism (mem_of \<alpha>) (mem_of \<alpha>') (\<in>) (\<in>) \<phi> \<psi>"
  shows "\<beta> \<in> \<alpha> \<Longrightarrow> \<phi> \<beta> = \<beta>"
proof (induction rule: mem_induction)
  case (mem \<beta>)
  have "\<gamma> \<in> \<phi> \<beta>" if "\<gamma> \<in> \<beta>" for \<gamma>
  proof -
    from that have "\<gamma> \<in> \<alpha>" using \<open>\<beta> \<in> \<alpha>\<close> \<open>ordinal \<alpha>\<close> by (blast elim: ordinal_mem_trans_closedE)
    then have "\<phi> \<gamma> \<in> \<phi> \<beta>" using \<open>\<beta> \<in> \<alpha>\<close> that iso by blast
    then show ?thesis using \<open>\<gamma> \<in> \<alpha>\<close> that mem.IH by auto
  qed
  moreover have "\<gamma> \<in> \<beta>" if "\<gamma> \<in> \<phi> \<beta>" for \<gamma>
  proof -
    from that have "\<phi> \<beta> \<in> \<alpha>'" using \<open>\<beta> \<in> \<alpha>\<close> iso mono_wrt_pred_if_bijection_on_left by blast
    moreover then have "\<gamma> \<in> \<alpha>'" using \<open>ordinal \<alpha>'\<close> that by (blast elim: ordinal_mem_trans_closedE)
    ultimately have "\<psi> \<gamma> \<in> \<beta>" using \<open>\<beta> \<in> \<alpha>\<close> that iso inverse_on_if_bijection_on_left_right 
      by (blast dest: inverse_onD)
    then have "\<phi> (\<psi> \<gamma>) = \<psi> \<gamma>" using \<open>\<beta> \<in> \<alpha>\<close> \<open>ordinal \<alpha>\<close> mem.IH 
      by (blast elim: ordinal_mem_trans_closedE)
    then have "\<gamma> = \<psi> \<gamma>" using \<open>\<gamma> \<in> \<alpha>'\<close> iso inverse_on_if_bijection_on_right_left 
      by (blast dest!: inverse_onD)
    then show ?thesis using \<open>\<psi> \<gamma> \<in> \<beta>\<close> by auto
  qed
  ultimately show ?case by blast
qed

corollary eq_if_rel_isomorphic_if_ordinal_if_ordinal:
  assumes ord: "ordinal \<alpha>" "ordinal \<alpha>'" "rel_isomorphic (mem_of \<alpha>) (mem_of \<alpha>') (\<in>) (\<in>)"
  shows "\<alpha> = \<alpha>'"
proof -
  from assms obtain \<phi> \<psi> where iso: "rel_isomorphism (mem_of \<alpha>) (mem_of \<alpha>') (\<in>) (\<in>) \<phi> \<psi>" by auto
  then have "\<forall>\<beta> : \<alpha>. \<phi> \<beta> = \<beta>" using ord rel_isomorphism_trivial_if_ordinal_to_ordinal by blast
  then have "image \<phi> \<alpha> = \<alpha>" by auto
  moreover have "image \<phi> \<alpha> = \<alpha>'" using iso image_eq_if_bijection_on_left_right by auto
  ultimately show ?thesis by auto
qed

definition order_type :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set" ("\<bbbO> _ _") where
"(\<bbbO> X R) = (THE \<alpha> : ordinal. rel_isomorphic (mem_of X) (mem_of \<alpha>) R (\<in>))"

lemma 
  assumes "wellorder_on X R"
  shows
    ordinal_order_type_if_wellorder_on: "ordinal \<bbbO> X R" and
    rel_isomorphic_order_type_if_wellorder_on: "rel_isomorphic (mem_of X) (mem_of \<bbbO> X R) R (\<in>)" and
    eq_order_type_if_ordinal_rel_isomorphic_if_wellorder_on:
      "\<And>\<beta>. ordinal \<beta> \<Longrightarrow> rel_isomorphic (mem_of X) (mem_of \<beta>) R (\<in>) \<Longrightarrow> \<beta> = \<bbbO> X R" 
proof -
  obtain \<alpha> where "ordinal \<alpha>" and iso_\<alpha>: "rel_isomorphic (mem_of X) (mem_of \<alpha>) R (\<in>)"
    using assms bex_ordinal_rel_isomorphic_if_wellorder_on by blast
  moreover have "\<alpha> = \<beta>" if "ordinal \<beta>" "rel_isomorphic (mem_of X) (mem_of \<beta>) R (\<in>)" for \<beta>
  proof -
    from that have "rel_isomorphic (mem_of \<alpha>) (mem_of \<beta>) (\<in>) (\<in>)" 
      using iso_\<alpha> rel_isomorphic_if_rel_isomorphic by blast
    then show ?thesis  using \<open>ordinal \<alpha>\<close> \<open>ordinal \<beta>\<close> 
        eq_if_rel_isomorphic_if_ordinal_if_ordinal by blast
  qed
  ultimately have bex1: "\<exists>!\<alpha> : ordinal. rel_isomorphic (mem_of X) (mem_of \<alpha>) R (\<in>)" by blast
  then show "ordinal \<bbbO> X R" unfolding order_type_def by (auto intro!: pred_btheI)
  moreover from bex1 show "rel_isomorphic (mem_of X) (mem_of \<bbbO> X R) R (\<in>)"
    unfolding order_type_def by (auto intro!: pred_btheI')
  ultimately show "\<And>\<beta>. ordinal \<beta> \<Longrightarrow> rel_isomorphic (mem_of X) (mem_of \<beta>) R (\<in>) \<Longrightarrow> \<beta> = \<bbbO> X R"
    using bex1 by auto
qed

lemma order_type_eq_iff_rel_isomorphic_if_wellorder_on:
  assumes "wellorder_on X R" "wellorder_on Y S"
  shows "(\<bbbO> X R) = (\<bbbO> Y S) \<longleftrightarrow> rel_isomorphic (mem_of X) (mem_of Y) R S"
proof
  assume "(\<bbbO> X R) = (\<bbbO> Y S)"
  then have "rel_isomorphic (mem_of X) (mem_of \<bbbO> Y S) R (\<in>)"
    using \<open>wellorder_on X R\<close> rel_isomorphic_order_type_if_wellorder_on by force
  then show "rel_isomorphic (mem_of X) (mem_of Y) R S" using \<open>wellorder_on Y S\<close> 
      rel_isomorphic_order_type_if_wellorder_on rel_isomorphic_if_rel_isomorphic by blast
next
  assume "rel_isomorphic (mem_of X) (mem_of Y) R S"
  then have "rel_isomorphic (mem_of X) (mem_of \<bbbO> Y S) R (\<in>)" using \<open>wellorder_on Y S\<close> 
      rel_isomorphic_order_type_if_wellorder_on rel_isomorphic_if_rel_isomorphic by blast
  moreover have "ordinal \<bbbO> Y S" using \<open>wellorder_on Y S\<close> ordinal_order_type_if_wellorder_on by blast
  ultimately show "(\<bbbO> X R) = (\<bbbO> Y S)" 
    using \<open>wellorder_on X R\<close> eq_order_type_if_ordinal_rel_isomorphic_if_wellorder_on by force
qed

lemma order_type_eq_self_if_ordinal:
  assumes "ordinal \<alpha>"
  shows "(\<bbbO> \<alpha> (\<in>)) = \<alpha>"
proof -
  have "wellorder_on \<alpha> (\<in>)" using assms wellorder_on_mem_if_ordinal by blast
  moreover have "rel_isomorphic (mem_of \<alpha>) (mem_of \<alpha>) (\<in>) (\<in>)" using rel_isomorphic_self by blast
  ultimately show ?thesis using assms eq_order_type_if_ordinal_rel_isomorphic_if_wellorder_on by auto
qed

end