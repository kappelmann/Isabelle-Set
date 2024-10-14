\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOTG_Ordinals_Equipollent
  imports
    HOTG_Choice
    HOTG_Equipollence_Base
    HOTG_Epsilon_Recursion
    HOTG_Ordinals_Base
    HOTG_Set_Difference
begin

unbundle no HOL_ascii_syntax

text \<open>The following requires the axiom of choice. It is in fact equivalent to the axiom of choice
over ZF since it implies the well ordering theorem.\<close>

(*TODO: could be prettified using more lemmas about injective_on and the_inverse_on*)
lemma bex_ordinal_equipollent: "\<exists>\<gamma> : ordinal. X \<approx> \<gamma>"
proof -
  (* Proof idea: form X into an ordered sequence e\<^sub>\<alpha> indexed by ordinals \<alpha> *)
  obtain f :: "set \<Rightarrow> set" where "((X : powerset X \<setminus> {\<emptyset>}) \<Rightarrow> X) f"
    by (rule choice_if_empty_not_memE[of "powerset X \<setminus> {\<emptyset>}"]) auto
  then have f_mem: "f Y \<in> Y" if "Y \<subseteq> X" "Y \<noteq> \<emptyset>" for Y using that by auto
  define \<Omega> where "\<Omega> = X" (* "end of sequence" symbol *)
  let ?step = "\<lambda>e \<alpha>. if X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>} \<noteq> \<emptyset> then f (X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>}) else \<Omega>"
  define e where "e = mem_rec ?step"
  have e_eq: "e \<alpha> = ?step e \<alpha>" for \<alpha>
    unfolding e_def using mem_rec_eq[of ?step \<alpha>] repl_fun_restrict_set_eq_repl by auto
  have e_mem_if_nonempty: "e \<alpha> \<in> X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>}" if "X \<setminus> {e \<beta> | \<beta> \<in> \<alpha>} \<noteq> \<emptyset>" for \<alpha>
  proof -
    from that have "e \<alpha> = f (X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>})" using e_eq[of \<alpha>] by auto
    then show ?thesis using that f_mem by auto
  qed
  have e_inj: "\<alpha> = \<beta>" if "e \<alpha> \<noteq> \<Omega>" "e \<alpha> = e \<beta>" "ordinal \<alpha>" "ordinal \<beta>" for \<alpha> \<beta>
    using \<open>ordinal \<alpha>\<close> \<open>ordinal \<beta>\<close>
  proof (cases rule: mem_eq_mem_if_ordinalE)
    case 1
    then have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>} \<noteq> \<emptyset>" using \<open>e \<alpha> \<noteq> \<Omega>\<close> \<open>e \<alpha> = e \<beta>\<close> e_eq[of \<beta>] by force
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
  define Y where "Y = {x \<in> X | has_inverse_on ordinal e x}"
  have "\<Omega> \<notin> Y" using \<Omega>_def Y_def by blast
  define nr where "nr = the_inverse_on ordinal e" (* maps x to its index in the sequence *)
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
    then show "ordinal (nr y)" "e (nr y) = y" unfolding nr_def the_inverse_on_pred_def
      by (auto elim!: pred_bthe_if_ex1E)
    then show "\<And>\<gamma>. ordinal \<gamma> \<and> y = e \<gamma> \<Longrightarrow> \<gamma> = nr y" using ex1_nr by (blast elim!: ex1E dest: bex1D)
  qed
  from nr_unique have nr_e_eq_self: "nr (e \<alpha>) = \<alpha>" if "ordinal \<alpha>" "e \<alpha> \<in> Y" for \<alpha>
    using that by auto
  define \<gamma> where "\<gamma> = {nr y | y \<in> Y}"
  have e_mem_Y: "e \<alpha> \<in> Y" and nr_e_eq_self': "nr (e \<alpha>) = \<alpha>" if "\<alpha> \<in> \<gamma>" for \<alpha>
  proof -
    from \<open>\<alpha> \<in> \<gamma>\<close> obtain y where hy: "y \<in> Y" "\<alpha> = nr y" using \<gamma>_def by auto
    then show "e \<alpha> \<in> Y" using e_nr_eq_self by auto
    then show "nr (e \<alpha>) = \<alpha>" using nr_e_eq_self hy ordinal_nr by auto
  qed
  have "has_inverse_on ordinal e x" if "x \<in> X" for x
  proof -
    obtain \<beta> where "ordinal \<beta>" "\<beta> \<notin> \<gamma>" using bex_ordinal_not_mem by blast
    have "X \<setminus> {e \<alpha> | \<alpha> \<in> \<beta>} = \<emptyset>"
    proof (rule ccontr)
      assume "X \<setminus> {e \<alpha> | \<alpha> \<in> \<beta>} \<noteq> \<emptyset>"
      then have "e \<beta> \<in> Y" using e_mem_if_nonempty \<open>ordinal \<beta>\<close> Y_def by auto
      then have "nr (e \<beta>) = \<beta>" using nr_e_eq_self \<open>ordinal \<beta>\<close> by auto
      moreover have "nr (e \<beta>) \<in> \<gamma>" using \<gamma>_def \<open>e \<beta> \<in> Y\<close> by blast
      ultimately show "False" using \<open>\<beta> \<notin> \<gamma>\<close> by auto
    qed
    then obtain \<alpha> where "\<alpha> \<in> \<beta>" "x = e \<alpha>" using \<open>x \<in> X\<close> by blast
    then show ?thesis using ordinal_if_mem_if_ordinal \<open>ordinal \<beta>\<close> by blast
  qed
  then have "X = Y" unfolding Y_def by auto
  have "bijection_on Y \<gamma> nr e"
  proof (urule bijection_onI)
    show "(mem_of Y \<Rightarrow> mem_of \<gamma>) nr" unfolding \<gamma>_def by auto
  qed (auto simp: e_mem_Y nr_e_eq_self' e_nr_eq_self)
  moreover have "ordinal \<gamma>"
  proof (intro ordinal_if_mem_trans_closedI)
    have "\<beta> \<in> \<gamma>" if "\<alpha> \<in> \<gamma>" "\<beta> \<in> \<alpha>" for \<alpha> \<beta>
    proof -
      have "e \<alpha> \<noteq> \<Omega>" using e_mem_Y \<open>\<alpha> \<in> \<gamma>\<close> \<open>\<Omega> \<notin> Y\<close> by blast
      have "ordinal \<alpha>" "ordinal \<beta>" using ordinal_nr \<gamma>_def that ordinal_if_mem_if_ordinal by auto
      then have "\<beta> \<subseteq> \<alpha>" using \<open>\<beta> \<in> \<alpha>\<close> by (auto elim: ordinal_mem_trans_closedE)
      then have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>} \<subseteq> X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>}" by blast
      moreover have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<alpha>} \<noteq> \<emptyset>" using \<open>e \<alpha> \<noteq> \<Omega>\<close> e_eq[of \<alpha>] by force
      ultimately have "X \<setminus> {e \<gamma> | \<gamma> \<in> \<beta>} \<noteq> \<emptyset>" by auto
      then have "e \<beta> \<in> Y" using e_mem_if_nonempty \<open>ordinal \<beta>\<close> Y_def by auto
      then show ?thesis unfolding \<gamma>_def using nr_e_eq_self \<open>ordinal \<beta>\<close> by blast
    qed
    then show "mem_trans_closed \<gamma>" by auto
  next
    fix \<alpha> assume "\<alpha> \<in> \<gamma>"
    then show "mem_trans_closed \<alpha>" using ordinal_nr \<gamma>_def by (auto elim: ordinal_mem_trans_closedE)
  qed
  ultimately show ?thesis using \<open>X = Y\<close> by auto
qed

text \<open>The wellordering theorem:\<close>

theorem ex_rel_wellorder_on: "\<exists>(R :: set \<Rightarrow> set \<Rightarrow> bool). wellorder_on (X :: set) R"
proof -
  obtain \<alpha> where "ordinal \<alpha>" "X \<approx> \<alpha>" using bex_ordinal_equipollent by blast
  then obtain nr e :: "set \<Rightarrow> set" where "bijection_on X \<alpha> nr e" by auto
  then have "(X \<Rightarrow> \<alpha>) nr" "injective_on X nr"
    using injective_on_if_bijection_on_left by auto
  then show ?thesis using wellorder_on_rel_map_if_injective_on_if_mono_wrt_pred_if_wellorder_on
    wellorder_on_mem_if_ordinal \<open>ordinal \<alpha>\<close> by blast
qed

end