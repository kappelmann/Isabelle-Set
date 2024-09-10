\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order Types\<close>
theory HOTG_Order_Types
  imports
    HOTG_Functions_Bijection
    HOTG_Order_Isomorphisms
    HOTG_Ordinals_Base
    HOTG_Wellfounded_Recursion
begin

unbundle no_HOL_ascii_syntax

definition order_type :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set" where
  "order_type X R \<equiv> THE \<alpha> : ordinal. order_isomorphic_on X \<alpha> R (\<in>)"

context
begin

interpretation galois L R l r for L R l r .

lemma bex_ordinal_order_isomorphic_on_if_wellorder_on:
  fixes X :: set and R :: "set \<Rightarrow> set \<Rightarrow> bool" (infixl "\<prec>" 50)
  assumes wello: "wellorder_on X (\<prec>)"
  shows "\<exists>\<alpha> : ordinal. order_isomorphic_on X \<alpha> (\<prec>) (\<in>)"
proof -
  let ?step = "\<lambda>nr x. {\<alpha> | y \<in> X, y \<prec> x \<and> \<alpha> = nr y}"
  define nr where "nr \<equiv> wf_rec_on X (\<prec>) ?step"
  define \<alpha> where "\<alpha> \<equiv> image nr X"
  have nr_eq: "nr x = ?step nr x" if "x \<in> X" for x
    using assms that by (fastforce simp: nr_def wf_rec_on_eq_app_fun_restrict_fun_rel_restrictI)
  then have mono_nr: "((\<prec>)\<up>\<^bsub>X\<^esub> \<Rightarrow> (\<in>)\<up>\<^bsub>\<alpha>\<^esub>) nr"
    unfolding \<alpha>_def by (fastforce intro!: rel_restrict_leftI rel_restrict_rightI)
  have "ordinal \<alpha>"
  proof (intro ordinal_if_mem_trans_closedI)
    show "mem_trans_closed \<alpha>" unfolding \<alpha>_def using nr_eq by force
    have "mem_trans_closed (nr x)" if "x \<in> X" for x
    proof (intro mem_trans_closedI')
      fix \<beta> \<gamma> assume "\<beta> \<in> nr x" "\<gamma> \<in> \<beta>"
      obtain y where "y \<in> X" "y \<prec> x" "\<beta> = nr y" using \<open>\<beta> \<in> nr x\<close> \<open>x \<in> X\<close> nr_eq by blast
      then obtain z where "z \<in> X" "z \<prec> y" "\<gamma> = nr z" using \<open>\<gamma> \<in> \<beta>\<close> nr_eq by blast
      have "z \<prec> x" using \<open>z \<prec> y\<close> \<open>y \<prec> x\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>z \<in> X\<close> assms
        by (blast dest: transitive_onD)
      then show "\<gamma> \<in> nr x" using \<open>\<gamma> = nr z\<close> \<open>x \<in> X\<close> \<open>z \<in> X\<close> mono_nr by fastforce
    qed
    then show "mem_trans_closed \<beta>" if "\<beta> \<in> \<alpha>" for \<beta> using that unfolding \<alpha>_def nr_eq by auto
  qed
  obtain e where bij: "bijection_on X \<alpha> nr e"
  proof -
    have "injective_on X nr"
    proof (urule injective_onI)
      fix x y presume prems: "x \<in> X" "y \<in> X" "nr x = nr y"
      with wello consider "x \<prec> y \<or> y \<prec> x" | "x = y" by blast
      then show "x = y" using mono_nr prems by cases auto
    qed simp_all
    then show ?thesis
      using that bijection_on_has_inverse_on_the_inverse_on_if_injective_on unfolding \<alpha>_def by auto
  qed
  moreover then have "inverse_on (in_field (\<in>)\<up>\<^bsub>\<alpha>\<^esub>) e nr"
  proof -
    from bij have "inverse_on \<alpha> e nr" by auto
    moreover have "in_field (\<in>)\<up>\<^bsub>\<alpha>\<^esub> \<le> mem_of \<alpha>" by fastforce
    ultimately show ?thesis using antimono_inverse_on by blast
  qed
  moreover have "(in_field (\<in>)\<up>\<^bsub>\<alpha>\<^esub> \<Rightarrow> in_field (\<prec>)\<up>\<^bsub>X\<^esub>) e"
  proof (intro mono_wrt_predI)
    fix x assume "in_field (\<in>)\<up>\<^bsub>\<alpha>\<^esub> x"
    then obtain x' where prems: "x \<in> \<alpha>" "x' \<in> \<alpha>" "x' \<in> x \<or> x \<in> x'" "x \<noteq> x'" by force
    moreover with bij have "e x \<in> X" "e x' \<in> X" "injective_on \<alpha> e"
      using injective_on_if_bijection_on_right by auto
    moreover with prems have "e x \<prec> e x' \<or> e x' \<prec> e x" using wello by (blast dest: injective_onD)
    ultimately show "in_field (\<prec>)\<up>\<^bsub>X\<^esub> (e x)" by auto
  qed
  moreover from wello have "connected_on (in_field (\<prec>)\<up>\<^bsub>X\<^esub>) (\<prec>)\<up>\<^bsub>X\<^esub>" by fastforce
  moreover from asymmetric_mem have "asymmetric (\<in>)\<up>\<^bsub>\<alpha>\<^esub>" by fastforce
  ultimately have "((\<in>)\<up>\<^bsub>\<alpha>\<^esub> \<Rightarrow> (\<prec>)\<up>\<^bsub>X\<^esub>) e" using mono_nr
    by (urule mono_wrt_rel_if_connected_on_if_asymmetric_if_mono_if_inverse_on where chained = insert)
    auto
  with \<open>ordinal \<alpha>\<close> bij mono_nr show ?thesis
    by (intro bexI exI) (fastforce intro!: order_isomorphic_onI order_isomorphism_onI bexI)
qed

context
  fixes \<alpha> \<beta> l r
  assumes ords: "ordinal \<alpha>" "ordinal \<beta>"
  and iso: "order_isomorphism_on \<alpha> \<beta> (\<in>) (\<in>) l r"
begin

lemma app_eq_if_order_isomorphic_on_if_ordinals: "\<alpha>' \<in> \<alpha> \<Longrightarrow> l \<alpha>' = \<alpha>'"
proof (induction \<alpha>' rule: mem_induction)
  case (mem \<alpha>') show ?case
  proof (rule eqI)
    fix \<beta>' assume asm: "\<beta>' \<in> \<alpha>'"
    then have "\<beta>' \<in> \<alpha>" using \<open>\<alpha>' \<in> \<alpha>\<close> \<open>ordinal \<alpha>\<close> by (blast elim: ordinal_mem_trans_closedE)
    moreover with iso have "l \<beta>' \<in> l \<alpha>'" using \<open>\<alpha>' \<in> \<alpha>\<close> asm by blast
    ultimately show "\<beta>' \<in> l \<alpha>'" using mem.IH asm by auto
  next
    fix \<beta>' assume asm: "\<beta>' \<in> l \<alpha>'"
    moreover with iso have "l \<alpha>' \<in> \<beta>" using \<open>\<alpha>' \<in> \<alpha>\<close> by blast
    moreover then have "\<beta>' \<in> \<beta>" using \<open>ordinal \<beta>\<close> asm by (blast elim: ordinal_mem_trans_closedE)
    ultimately have "r \<beta>' \<in> r (l \<alpha>')" using iso by blast
    with iso have "r \<beta>' \<in> \<alpha>'" using \<open>\<alpha>' \<in> \<alpha>\<close> using inverse_on_if_bijection_on_left_right
      by (force dest: inverse_onD)
    with mem.IH have "l (r \<beta>') = r \<beta>'" using \<open>\<alpha>' \<in> \<alpha>\<close> \<open>ordinal \<alpha>\<close>
      by (blast elim: ordinal_mem_trans_closedE)
    with iso have "\<beta>' = r \<beta>'" using \<open>\<beta>' \<in> \<beta>\<close> inverse_on_if_bijection_on_right_left
      by (force dest: inverse_onD)
    then show "\<beta>' \<in> \<alpha>'" using \<open>r \<beta>' \<in> \<alpha>'\<close> by auto
  qed
qed

corollary eq_if_order_isomorphic_on_if_ordinals: "\<alpha> = \<beta>"
proof -
  from app_eq_if_order_isomorphic_on_if_ordinals have "image l \<alpha> = \<alpha>" by auto
  moreover from iso have "image l \<alpha> = \<beta>" using image_eq_if_bijection_on_left_right by blast
  ultimately show ?thesis by auto
qed

end

lemma bex1_ordinal_order_isomorphic_on_if_wellorder_on:
  assumes "wellorder_on (X :: set) R"
  shows "\<exists>!\<alpha> : ordinal. order_isomorphic_on X \<alpha> R (\<in>)"
proof -
  from bex_ordinal_order_isomorphic_on_if_wellorder_on obtain \<alpha>
    where "ordinal \<alpha>" and iso: "order_isomorphic_on X \<alpha> R (\<in>)" using assms by blast
  moreover have "\<alpha> = \<beta>" if "ordinal \<beta>" "order_isomorphic_on X \<beta> R (\<in>)" for \<beta>
  proof -
    from iso that have "order_isomorphic_on \<alpha> \<beta> (\<in>) (\<in>)"
      using order_isomorphic_on_if_order_isomorphic_on order_isomorphic_on_trans by blast
    with eq_if_order_isomorphic_on_if_ordinals show ?thesis using \<open>ordinal \<alpha>\<close> \<open>ordinal \<beta>\<close> by blast
  qed
  ultimately show ?thesis by blast
qed

lemma
  assumes "wellorder_on X R"
  shows ordinal_order_type_if_wellorder_on [intro]: "ordinal (order_type X R)"
  and order_isomorphic_on_order_type_if_wellorder_on [intro]:
    "order_isomorphic_on X (order_type X R) R (\<in>)"
  and eq_order_type_if_order_isomorphic_on_if_ordinal_if_wellorder_on:
    "\<And>\<alpha>. ordinal \<alpha> \<Longrightarrow> order_isomorphic_on X \<alpha> R (\<in>) \<Longrightarrow> \<alpha> = order_type X R"
proof -
  from assms have bex1: "\<exists>!\<alpha> : ordinal. order_isomorphic_on X \<alpha> R (\<in>)"
    using bex1_ordinal_order_isomorphic_on_if_wellorder_on by blast
  then show "ordinal (order_type X R)" unfolding order_type_def by (auto intro!: pred_btheI)
  moreover from bex1 show "order_isomorphic_on X (order_type X R) R (\<in>)"
    unfolding order_type_def by (auto intro!: pred_btheI')
  ultimately show "\<And>\<alpha>. ordinal \<alpha> \<Longrightarrow> order_isomorphic_on X \<alpha> R (\<in>) \<Longrightarrow> \<alpha> = order_type X R"
    using bex1 by auto
qed

lemma order_isomorphic_on_if_order_type_eq_if_wellorders_on:
  assumes "wellorder_on X R" "wellorder_on Y S"
  and "order_type X R = order_type Y S"
  shows "order_isomorphic_on X Y R S"
proof -
  from assms have "order_isomorphic_on X (order_type Y S) R (\<in>)"
    using \<open>wellorder_on X R\<close> order_isomorphic_on_order_type_if_wellorder_on by force
  moreover have "order_isomorphic_on Y (order_type Y S) S (\<in>)"
    using \<open>wellorder_on Y S\<close> order_isomorphic_on_order_type_if_wellorder_on by force
  ultimately show ?thesis using
    order_isomorphic_on_if_order_isomorphic_on order_isomorphic_on_trans
    by blast
qed

lemma order_type_eq_if_order_isomorphic_on_if_wellorders_on:
  assumes "wellorder_on X R" "wellorder_on Y S"
  and iso: "order_isomorphic_on X Y R S"
  shows "order_type X R = order_type Y S"
proof -
  from \<open>wellorder_on X R\<close> have "order_isomorphic_on X (order_type X R) R (\<in>)"
    by (rule order_isomorphic_on_order_type_if_wellorder_on)
  with iso have "order_isomorphic_on Y (order_type X R) S (\<in>)"
    using order_isomorphic_on_if_order_isomorphic_on order_isomorphic_on_trans
    by blast
  moreover have "ordinal (order_type X R)" using \<open>wellorder_on X R\<close> by blast
  ultimately show ?thesis using \<open>wellorder_on Y S\<close>
    by (intro eq_order_type_if_order_isomorphic_on_if_ordinal_if_wellorder_on)
    auto
qed

corollary order_type_eq_iff_order_isomorphic_on_if_wellorders_on:
  assumes "wellorder_on X R" "wellorder_on Y S"
  shows "order_type X R = order_type Y S \<longleftrightarrow> order_isomorphic_on X Y R S"
  using assms order_isomorphic_on_if_order_type_eq_if_wellorders_on
    order_type_eq_if_order_isomorphic_on_if_wellorders_on
  by blast

lemma order_type_eq_self_if_ordinal [simp]:
  assumes "ordinal \<alpha>"
  shows "order_type \<alpha> (\<in>) = \<alpha>"
proof -
  have "wellorder_on \<alpha> (\<in>)" using assms wellorder_on_mem_if_ordinal by blast
  moreover have "order_isomorphic_on \<alpha> \<alpha> (\<in>) (\<in>)" using order_isomorphic_on_self by blast
  ultimately show ?thesis
    using assms eq_order_type_if_order_isomorphic_on_if_ordinal_if_wellorder_on by auto
qed

corollary order_type_order_type_eq_order_type [simp]:
  assumes "wellorder_on X R"
  shows "(order_type (order_type X R) (\<in>)) = order_type X R"
  using assms ordinal_order_type_if_wellorder_on order_type_eq_self_if_ordinal by auto

end

end