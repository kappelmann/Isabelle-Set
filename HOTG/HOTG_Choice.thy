theory HOTG_Choice
  imports 
    HOTG_Transfinite_Recursion 
    HOTG_Equipollence 
    HOTG_Set_Difference 
    HOTG_Bounded_Definite_Description
    HOTG_Ordinals_Base
begin

unbundle no_HOL_order_syntax

text \<open>The axiom of choice.\<close>
axiomatization where
  choice: "\<forall>\<S>. \<emptyset> \<notin> \<S> \<longrightarrow> (\<exists>\<CC>. \<forall>X : \<S>. \<CC> X \<in> X)"

lemma choice_function_exists:
  assumes "\<emptyset> \<notin> \<S>"
  obtains \<CC> where "\<forall>X : \<S>. \<CC> X \<in> X"
  using assms choice by fastforce

lemma choice_iff: "\<emptyset> \<notin> \<S> \<longleftrightarrow> (\<exists>\<CC>. \<forall>X : \<S>. \<CC> X \<in> X)"
  using choice by blast

theorem some_ordinal_not_mem:
  fixes X :: set
  obtains \<alpha> where "ordinal \<alpha>" "\<alpha> \<notin> X"
proof -
  (* Proof based on Burali-Forti paradox *)
  have "\<not> (\<forall>\<alpha> : ordinal. \<alpha> \<in> X)"              
  proof
    assume "\<forall>\<alpha> : ordinal. \<alpha> \<in> X"
    moreover define Ord where "Ord = {\<alpha> \<in> X | ordinal \<alpha>}"
    ultimately have mem_Ord: "\<alpha> \<in> Ord \<longleftrightarrow> ordinal \<alpha>" for \<alpha> by blast
    then have "mem_trans_closed Ord" using ordinal_if_mem_if_ordinal by force
    moreover have "\<forall>\<alpha> : Ord. mem_trans_closed \<alpha>" 
      using mem_Ord by (auto elim: ordinal_mem_trans_closedE)
    ultimately have "ordinal Ord" by (auto intro: ordinal_if_mem_trans_closedI)
    then have "Ord \<in> Ord" using mem_Ord by blast
    then show "False" by blast
  qed
  then show ?thesis using that by blast
qed

(* This requires the axiom of choice. It is, in fact, equivalent to the axiom of choice over ZF 
since it implies the well ordering theorem. *)
lemma equipollent_some_ordinal:
  fixes X :: set
  obtains \<nu> where "ordinal \<nu>" "X \<approx> \<nu>"
proof -
  (* Proof idea: form X into an ordered sequence e\<^sub>\<alpha> indexed by ordinals \<alpha> *)
  obtain \<CC> where "\<forall>Y : (powerset X \<setminus> {\<emptyset>}). \<CC> Y \<in> Y" (* choice function *)
    using choice_function_exists[of "powerset X \<setminus> {\<emptyset>}"] by auto 
  then have \<CC>_mem: "\<CC> Y \<in> Y" if "Y \<subseteq> X" "Y \<noteq> \<emptyset>" for Y using that by auto
  define \<Omega> where "\<Omega> = X" (* "end of sequence" symbol *)
  let ?R = "\<lambda>e \<alpha>. if X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>} \<noteq> \<emptyset> then \<CC> (X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>}) else \<Omega>"
  define e where "e = transfrec ?R"
  have e_eq: "e \<alpha> = ?R e \<alpha>" for \<alpha>
    using transfrec_eq[of ?R \<alpha>] repl_fun_restrict_set_eq_repl e_def[symmetric] by auto
  have e_mem_if_nonempty: "e \<alpha> \<in> X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>}" if "X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>} \<noteq> \<emptyset>" for \<alpha>
  proof -
    from that have "e \<alpha> = \<CC> (X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>})" using e_eq[of \<alpha>] by auto
    then show ?thesis using that \<CC>_mem by auto
  qed
  have e_inj: "\<alpha> = \<beta>" if "e \<alpha> \<noteq> \<Omega>" "e \<alpha> = e \<beta>" "ordinal \<alpha>" "ordinal \<beta>" for \<alpha> \<beta>
    using \<open>ordinal \<alpha>\<close> \<open>ordinal \<beta>\<close>
  proof (cases rule: mem_eq_mem_if_ordinalE)
    case 1
    have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>} \<noteq> \<emptyset>" using \<open>e \<alpha> \<noteq> \<Omega>\<close> \<open>e \<alpha> = e \<beta>\<close> e_eq[of \<beta>] by force
    then have "e \<beta> \<in> X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>}" using e_mem_if_nonempty by auto
    then have "False" using \<open>\<alpha> \<in> \<beta>\<close> \<open>e \<alpha> = e \<beta>\<close> by blast
    then show ?thesis by blast
  next
    case 3
    have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>} \<noteq> \<emptyset>" using \<open>e \<alpha> \<noteq> \<Omega>\<close> e_eq[of \<alpha>] by force
    then have "e \<alpha> \<in> X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>}" using e_mem_if_nonempty by auto
    then have "False" using \<open>\<beta> \<in> \<alpha>\<close> \<open>e \<alpha> = e \<beta>\<close> by blast
    then show ?thesis by blast
  qed
  define Y where "Y = {x \<in> X | \<exists>\<alpha> : ordinal. x = e \<alpha>}"
  have "\<Omega> \<notin> Y" using \<Omega>_def Y_def by blast
  define nr where "nr x = (THE \<alpha> : ordinal. x = e \<alpha>)" for x (* maps x to its index in the sequence *)
  have ordinal_nr: "ordinal (nr y)" and e_nr_eq_self: "e (nr y) = y" and
    nr_unique: "\<And>\<gamma>. ordinal \<gamma> \<and> y = e \<gamma> \<Longrightarrow> \<gamma> = nr y" if "y \<in> Y" for y
  proof -
    from that obtain \<alpha> where "ordinal \<alpha>" "y = e \<alpha>" using Y_def by blast
    moreover have "\<alpha> = \<beta>" if "ordinal \<beta>" "y = e \<beta>" for \<beta>
    proof -
      have "e \<alpha> \<noteq> \<Omega>" using \<open>y = e \<alpha>\<close> \<open>y \<in> Y\<close> \<open>\<Omega> \<notin> Y\<close> by auto
      then show ?thesis using e_inj \<open>y = e \<alpha>\<close> \<open>y = e \<beta>\<close> \<open>ordinal \<alpha>\<close> \<open>ordinal \<beta>\<close> by auto
    qed
    ultimately have ex1_nr: "\<exists>!\<gamma> : ordinal. y = e \<gamma>" by (auto intro!: ex1I)
    then show "ordinal (nr y)" "e (nr y) = y" using nr_def by (auto elim!: pred_bthe_if_ex1E)
    then show "\<And>\<gamma>. ordinal \<gamma> \<and> y = e \<gamma> \<Longrightarrow> \<gamma> = nr y" using ex1_nr by (blast elim!: ex1E dest: bex1D)
  qed
  from nr_unique have nr_e_eq_self: "nr (e \<alpha>) = \<alpha>" if "ordinal \<alpha>" "e \<alpha> \<in> Y" for \<alpha> 
    using that by auto
  define \<nu> where "\<nu> = {nr y | y \<in> Y}"
  have e_mem_Y: "e \<alpha> \<in> Y" and nr_e_eq_self': "nr (e \<alpha>) = \<alpha>" if "\<alpha> \<in> \<nu>" for \<alpha>
  proof -
    from \<open>\<alpha> \<in> \<nu>\<close> obtain y where hy: "y \<in> Y" "\<alpha> = nr y" using \<nu>_def by auto
    then show "e \<alpha> \<in> Y" using e_nr_eq_self by auto
    then show "nr (e \<alpha>) = \<alpha>" using nr_e_eq_self hy ordinal_nr by auto
  qed
  have "\<exists>\<alpha> : ordinal. x = e \<alpha>" if "x \<in> X" for x
  proof -
    obtain \<beta> where "ordinal \<beta>" "\<beta> \<notin> \<nu>" using some_ordinal_not_mem by blast
    have "X \<setminus> {e \<alpha> | \<alpha> \<in> \<beta>} = \<emptyset>"
    proof (rule ccontr)
      assume "X \<setminus> {e \<alpha> | \<alpha> \<in> \<beta>} \<noteq> \<emptyset>"
      then have "e \<beta> \<in> Y" using e_mem_if_nonempty \<open>ordinal \<beta>\<close> Y_def by auto
      then have "nr (e \<beta>) = \<beta>" using nr_e_eq_self \<open>ordinal \<beta>\<close> by auto
      moreover have "nr (e \<beta>) \<in> \<nu>" using \<nu>_def \<open>e \<beta> \<in> Y\<close> by blast
      ultimately show "False" using \<open>\<beta> \<notin> \<nu>\<close> by auto
    qed
    then obtain \<alpha> where "\<alpha> \<in> \<beta>" "x = e \<alpha>" using \<open>x \<in> X\<close> by blast
    then show ?thesis using ordinal_if_mem_if_ordinal \<open>ordinal \<beta>\<close> by blast
  qed
  then have "X = Y" unfolding Y_def by auto
  have "bijection_on Y \<nu> nr e"
  proof (urule bijection_onI)
    show "(mem_of Y \<Rightarrow> mem_of \<nu>) nr" unfolding \<nu>_def by auto
  qed (auto simp: e_mem_Y nr_e_eq_self' e_nr_eq_self)
  moreover have "ordinal \<nu>"
  proof (intro ordinal_if_mem_trans_closedI)
    have "\<beta> \<in> \<nu>" if "\<alpha> \<in> \<nu>" "\<beta> \<in> \<alpha>" for \<alpha> \<beta>
    proof -
      have "e \<alpha> \<noteq> \<Omega>" using e_mem_Y \<open>\<alpha> \<in> \<nu>\<close> \<open>\<Omega> \<notin> Y\<close> by blast 
      have "ordinal \<alpha>" "ordinal \<beta>" using ordinal_nr \<nu>_def that ordinal_if_mem_if_ordinal by auto
      then have "\<beta> \<subseteq> \<alpha>" using \<open>\<beta> \<in> \<alpha>\<close> by (auto elim: ordinal_mem_trans_closedE)
      then have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>} \<subseteq> X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>}" by blast
      moreover have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>} \<noteq> \<emptyset>" using \<open>e \<alpha> \<noteq> \<Omega>\<close> e_eq[of \<alpha>] by force
      ultimately have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>} \<noteq> \<emptyset>" by auto
      then have "e \<beta> \<in> Y" using e_mem_if_nonempty \<open>ordinal \<beta>\<close> Y_def by auto
      then show ?thesis unfolding \<nu>_def using nr_e_eq_self \<open>ordinal \<beta>\<close> by blast
    qed
    then show "mem_trans_closed \<nu>" by auto
  next
    fix \<alpha> assume "\<alpha> \<in> \<nu>"
    then show "mem_trans_closed \<alpha>" using ordinal_nr \<nu>_def by (auto elim: ordinal_mem_trans_closedE)
  qed
  ultimately show ?thesis using that \<open>X = Y\<close> by auto
qed

end