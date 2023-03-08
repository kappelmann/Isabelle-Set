\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Right Unique\<close>
theory SBinary_Relations_Right_Unique
  imports
    SBinary_Relation_Functions
begin

consts set_right_unique_on :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  set_right_unique_on_pred \<equiv> "set_right_unique_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_right_unique_on_set \<equiv> "set_right_unique_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_right_unique_on_pred P R \<equiv>
    \<forall>x y y'. P x \<and> \<langle>x, y\<rangle> \<in> R \<and> \<langle>x, y'\<rangle> \<in> R \<longrightarrow> y = y'"
  definition "set_right_unique_on_set A R \<equiv> set_right_unique_on (mem_of A) R"
end

lemma set_right_unique_on_set_iff_set_right_unique_on [iff]:
  "set_right_unique_on A R \<longleftrightarrow> set_right_unique_on (mem_of A) R"
  unfolding set_right_unique_on_set_def by simp

lemma set_right_unique_onI [intro]:
  assumes "\<And>x y y'. P x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x, y'\<rangle> \<in> R \<Longrightarrow> y = y'"
  shows "set_right_unique_on P R"
  using assms unfolding set_right_unique_on_pred_def by blast

lemma set_right_unique_onD:
  assumes "set_right_unique_on P R"
  and "P x"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>x, y'\<rangle> \<in> R"
  shows "y = y'"
  using assms unfolding set_right_unique_on_pred_def by blast

lemma antimono_set_right_unique_on_pred:
  "antimono (\<lambda>P. set_right_unique_on (P :: set \<Rightarrow> bool) R)"
  by (intro antimonoI) (auto dest: set_right_unique_onD)

lemma antimono_set_right_unique_on_set:
  "antimono (\<lambda>R. set_right_unique_on (P :: set \<Rightarrow> bool) R)"
  by (intro antimonoI) (auto dest: set_right_unique_onD)

lemma set_right_unique_on_glueI:
  fixes P :: "set \<Rightarrow> bool"
  assumes "\<And>R R'. R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> set_right_unique_on P (glue {R, R'})"
  shows "set_right_unique_on P (glue \<R>)"
proof
  fix x y y' assume "P x" "\<langle>x, y\<rangle> \<in> glue \<R>" "\<langle>x, y'\<rangle> \<in> glue \<R>"
  with assms obtain R R' where "R \<in> \<R>" "R' \<in> \<R>" "\<langle>x, y\<rangle> \<in> R" "\<langle>x, y'\<rangle> \<in> R'"
    and runique: "set_right_unique_on P (glue {R, R'})"
    by auto
  then have "\<langle>x, y\<rangle> \<in> (glue {R, R'})" "\<langle>x, y'\<rangle> \<in> (glue {R, R'})" by auto
  with \<open>P x\<close> runique show "y = y'" by (intro set_right_unique_onD)
qed

lemma set_right_unique_on_compI:
  fixes P :: "set \<Rightarrow> bool"
  assumes "set_right_unique_on P R"
  and "set_right_unique_on (rng (R\<restriction>\<^bsub>P\<^esub>) \<inter> dom S) S"
  shows "set_right_unique_on P (S \<circ> R)"
  using assms by (auto dest: set_right_unique_onD)


end
