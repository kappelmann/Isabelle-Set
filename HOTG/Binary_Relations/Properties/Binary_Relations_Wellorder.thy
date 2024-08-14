theory Binary_Relations_Wellorder
  imports
    Binary_Relations_Strict_Linear_Order
    Transport.Binary_Relations_Wellfounded
    Transport.Functions_Bijection
begin

definition wellorder_on :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"wellorder_on P R \<longleftrightarrow> strict_linear_order_on P R \<and> wellfounded R"

lemma wellorder_onI [intro]:
  assumes "strict_linear_order_on P R" "wellfounded R"
  shows "wellorder_on P R"
  using assms wellorder_on_def by blast

lemma wellorder_onD [dest]:
  assumes "wellorder_on P R"
  shows "strict_linear_order_on P R" "wellfounded R"
  using assms wellorder_on_def by auto

lemma wellorder_pullback:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes wellorder: "wellorder_on A R"
  assumes bij: "bijection_on B A f g"
  shows "wellorder_on B (\<lambda>x y. B x \<and> B y \<and> R (f x) (f y))" 
proof -
  let ?S = "\<lambda>x y. B x \<and> B y \<and> R (f x) (f y)"
  have "strict_linear_order_on B ?S"
    using strict_linear_order_pullback[of A R B f] mono_wrt_pred_if_bijection_on_left[OF bij]
      injective_on_if_bijection_on_left[OF bij] wellorder by blast
  moreover have "wellfounded ?S"
  proof (intro wellfoundedI)
    fix P and x :: 'b assume "P x"
    then show "\<exists>m : P. \<forall>y. ?S y m \<longrightarrow> \<not> P y"
    proof (cases "\<exists>e : B. P e")
      case True
      then obtain e where "B e" "P e" by blast
      define Q where "Q a \<longleftrightarrow> A a \<and> P (g a)" for a
      then have "Q (f e)" unfolding Q_def using mono_wrt_pred_if_bijection_on_left[OF bij]
        using inverse_on_if_bijection_on_left_right[OF bij] \<open>B e\<close> \<open>P e\<close> by (auto dest: inverse_onD)
      moreover have "wellfounded R" using wellorder by blast
      ultimately obtain m where "Q m" and min: "\<forall>z. R z m \<longrightarrow> \<not> Q z" 
        using wellfoundedE[where P=Q] by auto
      have "\<not> P y" if "?S y (g m)" for y
      proof -
        from that have "R (f y) m" using inverse_on_if_bijection_on_right_left[OF bij] 
            \<open>Q m\<close> unfolding Q_def by (auto dest: inverse_onD)
        then have "\<not> Q (f y)" using min by blast
        then show ?thesis unfolding Q_def using that
          mono_wrt_pred_if_bijection_on_left[OF bij] inverse_on_if_bijection_on_left_right[OF bij]
          by (auto dest: inverse_onD)
      qed
      then show ?thesis using \<open>Q m\<close> unfolding Q_def by auto
    next
      case False
      then have "\<not> ?S y x" for y using \<open>P x\<close> by blast
      then show ?thesis using \<open>P x\<close> by blast
    qed
  qed
  ultimately show ?thesis by blast
qed

end