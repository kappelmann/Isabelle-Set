theory Binary_Relations_Wellorder
  imports
    Binary_Relations_Strict_Linear_Order
    Transport.Binary_Relations_Wellfounded
    Transport.Functions_Bijection
    Transport.Functions_Restrict
    Transport.Wellfounded_Recursion
begin

consts wellfounded_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  wellfounded_on_pred \<equiv> "wellfounded_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellfounded_on_pred (D :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) 
    \<equiv> \<forall>P. (\<exists>x : D. P x) \<longrightarrow> (\<exists>m : D. P m \<and> (\<forall>y : D. R y m \<longrightarrow> \<not> P y))"
end

lemma wellfounded_onI:
  assumes "\<And>P x. D x \<Longrightarrow> P x \<Longrightarrow> (\<exists>m : D. P m \<and> (\<forall>y : D. R y m \<longrightarrow> \<not> P y))"
  shows "wellfounded_on D R"
  using assms unfolding wellfounded_on_pred_def by blast

lemma wellfounded_onE:
  assumes "wellfounded_on D R" "D x" "P x"
  obtains m where "D m" "P m" "\<And>y. D y \<Longrightarrow> R y m \<Longrightarrow> \<not> P y"
proof -
  from assms obtain m where "D m" "P m" "\<forall>y : D. R y m \<longrightarrow> \<not> P y"
    unfolding wellfounded_on_pred_def by auto
  then show ?thesis using that by blast
qed

lemma wellfounded_on_induct [consumes 1, case_names step]:
  assumes "wellfounded_on D R" "D z"
  assumes step: "\<And>x. D x \<Longrightarrow> (\<And>y. D y \<Longrightarrow> R y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P z"
proof (rule ccontr)
  assume "\<not> P z"
  then obtain m where "D m" "\<not> P m" "\<And>y. D y \<Longrightarrow> R y m \<Longrightarrow> P y"
    using \<open>D z\<close> \<open>wellfounded_on D R\<close> by (blast elim!: wellfounded_onE[where P = "\<lambda>x. \<not> P x"])
  then show "False" using step by auto
qed

lemma wellfounded_rel_restrict_if_wellfounded_on:
  assumes "wellfounded_on D R"
  shows "wellfounded R\<restriction>\<^bsub>D\<^esub>\<upharpoonleft>\<^bsub>D\<^esub>"
proof (intro wellfoundedI)
  fix P and x :: 'a assume "P x"
  show "\<exists>m : P. \<forall>y. R\<restriction>\<^bsub>D\<^esub>\<upharpoonleft>\<^bsub>D\<^esub> y m \<longrightarrow> \<not> P y"
  proof (cases "\<exists>s : D. P s")
    case True
    then show ?thesis using assms by (fast elim!: wellfounded_onE)
  next
    case False
    then show ?thesis using \<open>P x\<close> by blast
  qed
qed

consts wfrec_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"

overloading
  wfrec_on_pred \<equiv> "wfrec_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
begin
  definition "wfrec_on_pred (D :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (step :: (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b))
    \<equiv> wfrec R\<restriction>\<^bsub>D\<^esub>\<upharpoonleft>\<^bsub>D\<^esub> step"
end

lemma wfrec_on_eq:
  fixes step
  assumes "wellfounded_on D R" "D x"
  defines "f \<equiv> wfrec_on D R step"
  shows "f x = step (fun_restrict (fun_rel_restrict f R x) D) x"
proof -
  have wf: "wellfounded R\<restriction>\<^bsub>D\<^esub>\<upharpoonleft>\<^bsub>D\<^esub>" using assms wellfounded_rel_restrict_if_wellfounded_on by blast
  then have "f x = step (fun_rel_restrict f R\<restriction>\<^bsub>D\<^esub>\<upharpoonleft>\<^bsub>D\<^esub> x) x"
    by (simp only: f_def wfrec_step_eq wfrec_eq_wfrec_stepI wfrec_on_pred_def)
  moreover have "fun_rel_restrict f R\<restriction>\<^bsub>D\<^esub>\<upharpoonleft>\<^bsub>D\<^esub> x = fun_restrict (fun_rel_restrict f R x) D"
    using \<open>D x\<close> unfolding fun_rel_restrict_eq_fun_restrict fun_restrict_eq_if by force
  ultimately show ?thesis by simp                      
qed

lemma wellfounded_on_pullback:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool"
  assumes wellfounded: "wellfounded_on A R" and "(B \<Rightarrow> A) f"
  shows "wellfounded_on B (rel_map f R)"                  
proof (intro wellfounded_onI)
  fix P and x :: 'b assume "B x" "P x"
  moreover define Q where "Q a \<longleftrightarrow> (\<exists>b : B. f b = a \<and> P b)" for a
  ultimately have "A (f x)" "Q (f x)" using \<open>(B \<Rightarrow> A) f\<close> by auto
  then obtain m\<^sub>Q where "A m\<^sub>Q" "Q m\<^sub>Q" and min: "\<And>a. A a \<Longrightarrow> R a m\<^sub>Q \<Longrightarrow> \<not> Q a" 
    using wellfounded by (blast elim!: wellfounded_onE)
  from \<open>Q m\<^sub>Q\<close> obtain m\<^sub>P where "B m\<^sub>P" "f m\<^sub>P = m\<^sub>Q" "P m\<^sub>P" unfolding Q_def by blast
  have "\<not> P b" if "B b" "rel_map f R b m\<^sub>P" for b
  proof -
    from that have "R (f b) m\<^sub>Q" using \<open>f m\<^sub>P = m\<^sub>Q\<close> by auto
    then have "\<not> Q (f b)" using \<open>B b\<close> \<open>(B \<Rightarrow> A) f\<close> min by blast
    then show ?thesis unfolding Q_def using \<open>B b\<close> by blast
  qed
  then show "\<exists>m : B. P m \<and> (\<forall>b : B. rel_map f R b m \<longrightarrow> \<not> P b)" using \<open>B m\<^sub>P\<close> \<open>P m\<^sub>P\<close> by blast
qed

corollary wellfounded_on_subdomain [intro]:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellfounded_on A R" "B \<le> A"
  shows "wellfounded_on B R"
proof -
  have "(B \<Rightarrow> A) id" using \<open>B \<le> A\<close> by force
  then have "wellfounded_on B (rel_map id R)" using assms wellfounded_on_pullback by blast
  moreover have "rel_map id R = R" by force
  ultimately show ?thesis by simp
qed

lemma wellfounded_on_subrelation [intro]:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellfounded_on D R" "S \<le> R"
  shows "wellfounded_on D S"
proof (intro wellfounded_onI)
  fix P and x :: 'a assume "D x" "P x"
  then obtain m where "D m" "P m" "\<And>y. D y \<Longrightarrow> R y m \<Longrightarrow> \<not> P y" 
    using assms by (force elim!: wellfounded_onE)
  then show "\<exists>m : D. P m \<and> (\<forall>y : D. S y m \<longrightarrow> \<not> P y)" using \<open>S \<le> R\<close> by blast
qed

lemma wellfounded_iff_wellfounded_on_top [iff]:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  shows "wellfounded R \<longleftrightarrow> wellfounded_on (\<top> :: 'a \<Rightarrow> bool) R"
proof
  show "wellfounded R \<Longrightarrow> wellfounded_on (\<top> :: 'a \<Rightarrow> bool) R" 
    by (force intro!: wellfounded_onI elim!: wellfoundedE)
next
  show "wellfounded_on (\<top> :: 'a \<Rightarrow> bool) R \<Longrightarrow> wellfounded R" 
    using wellfounded_rel_restrict_if_wellfounded_on by force
qed

corollary wellfounded_on_if_wellfounded [intro]:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellfounded R"
  shows "wellfounded_on D R"
  using assms by force

consts wellorder_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  wellorder_on_pred \<equiv> "wellorder_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellorder_on_pred (D :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) 
    \<equiv> strict_linear_order_on D R \<and> wellfounded_on D R"
end

lemma wellorder_onI [intro]:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "strict_linear_order_on D R" "wellfounded_on D R"
  shows "wellorder_on D R"
  using assms unfolding wellorder_on_pred_def by blast

lemma wellorder_onE [elim]:
  fixes D :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellorder_on D R"
  obtains "strict_linear_order_on D R" "wellfounded_on D R"
  using assms unfolding wellorder_on_pred_def by blast

lemma wellorder_on_pullback:
  fixes A :: "'a \<Rightarrow> bool"
  assumes "wellorder_on A R" "(B \<Rightarrow> A) e" "injective_on B e"
  shows "wellorder_on B (rel_map e R)" 
  using assms strict_linear_order_on_pullback wellfounded_on_pullback by fastforce

lemma wellorder_on_subrelation [intro]:
  fixes A :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "wellorder_on A R" "B \<le> A"
  shows "wellorder_on B R" 
  using assms by (blast intro: strict_linear_order_on_subdomain)

end