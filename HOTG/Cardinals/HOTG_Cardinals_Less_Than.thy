\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory HOTG_Cardinals_Less_Than
  imports
    HOTG_Cantor_Schroeder_Bernstein
begin

lemma cardinality_le_if_injective_onI:
  assumes "(X \<Rightarrow> Y) (f :: _ \<Rightarrow> _)"
  and inj_f: "injective_on X f"
  shows "|X| \<le> |Y|"
proof (rule ccontr)
  assume "\<not>(|X| \<le> |Y|)"
  then have "|Y| < |X|" using ordinal_cardinality lt_if_not_le_if_ordinal by blast
  then have "|Y| \<subseteq> |X|" using ordinal_cardinality le_iff_subset_if_ordinal le_if_lt by blast
  obtain g\<^sub>X h\<^sub>X :: "set \<Rightarrow> set" where bijX: "bijection_on |X| X g\<^sub>X h\<^sub>X"
    using cardinality_equipollent_self by blast
  obtain g\<^sub>Y h\<^sub>Y :: "set \<Rightarrow> set" where bijY: "bijection_on |Y| Y g\<^sub>Y h\<^sub>Y"
    using cardinality_equipollent_self by blast
  have "(|X| \<Rightarrow> X) g\<^sub>X" "injective_on |X| g\<^sub>X" using injective_on_if_bijection_on_left bijX by auto
  with inj_f have "injective_on |X| (f \<circ> g\<^sub>X)" using injective_on_comp_if_injective_onI by auto
  moreover have "(|X| \<Rightarrow> Y) (f \<circ> g\<^sub>X)" using \<open>(|X| \<Rightarrow> X) g\<^sub>X\<close> \<open>(X \<Rightarrow> Y) f\<close> by force
  moreover from bijY have "(Y \<Rightarrow> |Y|) h\<^sub>Y" "injective_on Y h\<^sub>Y"
    using injective_on_if_bijection_on_right by auto
  ultimately have "injective_on |X| (h\<^sub>Y \<circ> (f \<circ> g\<^sub>X))" using injective_on_comp_if_injective_onI by auto
  moreover have "(|X| \<Rightarrow> |Y|) (h\<^sub>Y \<circ> (f \<circ> g\<^sub>X))" using \<open>(|X| \<Rightarrow> Y) (f \<circ> g\<^sub>X)\<close> \<open>(Y \<Rightarrow> |Y|) h\<^sub>Y\<close> by force
  ultimately have "|X| \<approx> |Y|"
    using \<open>|Y| \<subseteq> |X|\<close> equipollent_if_subset_if_injective_on_if_mono_wrt by blast
  then have "|X| = |Y|" using cardinality_eq_if_equipollent by force
  then show "False" using \<open>\<not>(|X| \<le> |Y|)\<close> by auto
qed

lemma injective_on_if_cardinality_leE:
  assumes "|X| \<le> |Y|"
  obtains f :: "_ \<Rightarrow> _" where "(X \<Rightarrow> Y) f" "injective_on X f"
proof -
  obtain g\<^sub>X h\<^sub>X :: "set \<Rightarrow> set" where bijX: "bijection_on |X| X g\<^sub>X h\<^sub>X"
    using cardinality_equipollent_self by blast
  obtain g\<^sub>Y h\<^sub>Y :: "set \<Rightarrow> set" where bijY: "bijection_on |Y| Y g\<^sub>Y h\<^sub>Y"
    using cardinality_equipollent_self by blast
  have "(X \<Rightarrow> |X|) h\<^sub>X" "injective_on X h\<^sub>X" using injective_on_if_bijection_on_right bijX by auto
  have "(|Y| \<Rightarrow> Y) g\<^sub>Y" "injective_on |Y| g\<^sub>Y" using injective_on_if_bijection_on_left bijY by auto
  from assms have "|X| \<subseteq> |Y|" using ordinal_cardinality le_iff_subset_if_ordinal by blast
  then have "(X \<Rightarrow> |Y|) h\<^sub>X" using \<open>(X \<Rightarrow> |X|) h\<^sub>X\<close> by auto
  then have "injective_on X (g\<^sub>Y \<circ> h\<^sub>X)"
    using \<open>injective_on X h\<^sub>X\<close> \<open>injective_on |Y| g\<^sub>Y\<close> injective_on_comp_if_injective_onI by auto
  moreover have "(X \<Rightarrow> Y) (g\<^sub>Y \<circ> h\<^sub>X)" using \<open>(X \<Rightarrow> |Y|) h\<^sub>X\<close> \<open>(|Y| \<Rightarrow> Y) g\<^sub>Y\<close> by force
  ultimately show ?thesis using that by auto
qed

corollary cardinality_le_iff_ex_injective_on:
  "|X| \<le> |Y| \<longleftrightarrow> (\<exists>(f :: _ \<Rightarrow> _) : X \<Rightarrow> Y. injective_on X f)"
  using cardinality_le_if_injective_onI by (auto elim: injective_on_if_cardinality_leE)

end