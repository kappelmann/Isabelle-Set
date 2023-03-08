\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Bounded Quantifiers\<close>
theory Bounded_Quantifiers
  imports Order_Set
begin

definition ball :: \<open>set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where "ball A P \<equiv> (\<forall>x. x \<in> A \<longrightarrow> P x)"

definition bex :: \<open>set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where "bex A P \<equiv> \<exists>x. x \<in> A \<and> P x"

definition bex1 :: \<open>set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where "bex1 A P \<equiv> \<exists>!x. x \<in> A \<and> P x"

bundle hotg_bounded_quantifiers_syntax
begin
syntax
  "_ball"  :: \<open>[idts, set, bool] \<Rightarrow> bool\<close> ("(2\<forall>_ \<in> _./ _)" 10)
  "_ball2" :: \<open>[idts, set, bool] \<Rightarrow> bool\<close>
  "_bex"   :: \<open>[idts, set, bool] \<Rightarrow> bool\<close> ("(2\<exists>_ \<in> _./ _)" 10)
  "_bex2"  :: \<open>[idts, set, bool] \<Rightarrow> bool\<close>
  "_bex1"  :: \<open>[idt, set, bool] \<Rightarrow> bool\<close> ("(2\<exists>!_ \<in> _./ _)" 10)
end
bundle no_hotg_bounded_quantifiers_syntax
begin
no_syntax
  "_ball"  :: \<open>[idts, set, bool] \<Rightarrow> bool\<close> ("(2\<forall>_ \<in> _./ _)" 10)
  "_ball2" :: \<open>[idts, set, bool] \<Rightarrow> bool\<close>
  "_bex"   :: \<open>[idts, set, bool] \<Rightarrow> bool\<close> ("(2\<exists>_ \<in> _./ _)" 10)
  "_bex2"  :: \<open>[idts, set, bool] \<Rightarrow> bool\<close>
  "_bex1"  :: \<open>[idt, set, bool] \<Rightarrow> bool\<close> ("(2\<exists>!_ \<in> _./ _)" 10)
end
unbundle hotg_bounded_quantifiers_syntax
translations
  "\<forall>x xs \<in> A. P" \<rightharpoonup> "CONST ball A (\<lambda>x. _ball2 xs A P)"
  "_ball2 x A P" \<rightharpoonup> "\<forall>x \<in> A. P"
  "\<forall>x \<in> A. P" \<rightleftharpoons> "CONST ball A (\<lambda>x. P)"

  "\<exists>x xs \<in> A. P" \<rightharpoonup> "CONST bex A (\<lambda>x. _bex2 xs A P)"
  "_bex2 x A P" \<rightharpoonup> "\<exists>x \<in> A. P"
  "\<exists>x \<in> A. P" \<rightleftharpoons> "CONST bex A (\<lambda>x. P)"

  "\<exists>!x \<in> A. P" \<rightleftharpoons> "CONST bex1 A (\<lambda>x. P)"

text\<open>Setup of one point rules.\<close>

simproc_setup defined_bex ("\<exists>x \<in> A. P x \<and> Q x") =
  \<open>fn _ => Quantifier1.rearrange_Bex
    (fn ctxt => unfold_tac ctxt @{thms bex_def})\<close>

simproc_setup defined_ball ("\<forall>x \<in> A. P x \<longrightarrow> Q x") =
  \<open>fn _ => Quantifier1.rearrange_Ball
    (fn ctxt => unfold_tac ctxt @{thms ball_def})\<close>

lemma ballI [intro!]: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> \<forall>x \<in> A. P x"
  by (simp add: ball_def)

lemma ballD [dest?]: "\<lbrakk>\<forall>x \<in> A. P x; x \<in> A\<rbrakk> \<Longrightarrow> P x"
  by (simp add: ball_def)

lemma ballE:
  assumes "\<forall>x \<in> A. P x"
  obtains "\<And>x. x \<in> A \<Longrightarrow> P x"
  using assms unfolding ball_def by auto

lemma ballE' [elim]:
  assumes "\<forall>x \<in> A. P x"
  obtains "x \<notin> A" | "P x"
  using assms by (auto elim: ballE)

(*LP: Trival rewrite rule: \<open>(\<forall>x \<in> A. P) \<longleftrightarrow> P\<close> holds only if A is nonempty!*)
lemma ball_iff_ex_mem [iff]: "(\<forall>x \<in> A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<longrightarrow> P)"
  by (simp add: ball_def)

lemma ball_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<forall>x \<in> A. P x) \<longleftrightarrow> (\<forall>x \<in> A'. P' x)"
  by (simp add: ball_def)

lemma ball_or_iff_ball_or [iff]: "(\<forall>x \<in> A. P x \<or> Q) \<longleftrightarrow> ((\<forall>x \<in> A. P x) \<or> Q)"
  by auto

lemma ball_or_iff_or_ball [iff]: "(\<forall>x \<in> A. P \<or> Q x) \<longleftrightarrow> (P \<or> (\<forall>x \<in> A. Q x))"
  by auto

lemma ball_imp_iff_imp_ball [iff]: "(\<forall>x \<in> A. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x \<in> A. Q x))"
  by auto

lemma ball_empty [iff]: "\<forall>x \<in> {}. P x" by auto

lemma atomize_ball:
  "(\<And>x. x \<in> A \<Longrightarrow> P x) \<equiv> Trueprop (\<forall>x \<in> A. P x)"
  by (simp only: ball_def atomize_all atomize_imp)

declare atomize_ball[symmetric, rulify]
declare atomize_ball[symmetric, defn]

lemma bexI [intro]: "\<lbrakk>P x; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x"
  by (simp add: bex_def, blast)

(*LP: The best argument order when there is only one @{term "x \<in> A"}*)
corollary bexI': "\<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> \<exists>x \<in> A. P x" ..

lemma bexE [elim!]: "\<lbrakk>\<exists>x \<in> A. P x; \<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding bex_def by blast

(*LP: We do not even have @{term "(\<exists>x \<in> A. True) \<longleftrightarrow> True"} unless @{term "A"} is
  nonempty.*)
lemma bex_iff_ex_and [simp]: "(\<exists>x \<in> A. P) \<longleftrightarrow> ((\<exists>x. x \<in> A) \<and> P)"
  unfolding bex_def by simp

lemma bex_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<exists>x \<in> A. P x) \<longleftrightarrow> (\<exists>x \<in> A'. P' x)"
  unfolding bex_def by (simp cong: conj_cong)

lemma bex_and_iff_bex_and [simp]: "(\<exists>x \<in> A. P x \<and> Q) \<longleftrightarrow> ((\<exists>x \<in> A. P x) \<and> Q)"
  by auto

lemma bex_and_iff_or_bex [simp]: "(\<exists>x \<in> A. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x \<in> A. Q x))"
  by auto

lemma not_bex_empty [iff]: "\<not>(\<exists>x \<in> {}. P x)" by auto

lemma ball_imp_iff_bex_imp [simp]: "(\<forall>x \<in> A. P x \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x \<in> A. P x) \<longrightarrow> Q)"
  by auto

lemma not_ball_iff_bex_not [simp]: "(\<not>(\<forall>x \<in> A. P x)) \<longleftrightarrow> (\<exists>x \<in> A. \<not>P x)"
  by auto

lemma not_bex_iff_ball_not [simp]: "(\<not>(\<exists>x \<in> A. P x)) \<longleftrightarrow> (\<forall>x \<in> A. \<not>P x)"
  by auto

lemma bex1I [intro]: "\<lbrakk>P x; x \<in> A; \<And>z. \<lbrakk>P z; z \<in> A\<rbrakk> \<Longrightarrow> z = x\<rbrakk> \<Longrightarrow> \<exists>!x \<in> A. P x"
  by (simp add: bex1_def, blast)

lemma bex1I': "\<lbrakk>x \<in> A; P x; \<And>z. \<lbrakk>P z; z \<in> A\<rbrakk> \<Longrightarrow> z = x\<rbrakk> \<Longrightarrow> \<exists>!x \<in> A. P x"
  by blast

lemma bex1E [elim!]: "\<lbrakk>\<exists>!x \<in> A. P x; \<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (simp add: bex1_def, blast)

lemma bex1_triv [simp]: "(\<exists>!x \<in> A. P) \<longleftrightarrow> ((\<exists>!x. x \<in> A) \<and> P)"
  by (auto simp add: bex1_def)

lemma bex1_iff: "(\<exists>!x \<in> A. P x) \<longleftrightarrow> (\<exists>!x. x \<in> A \<and> P x)"
  by (auto simp add: bex1_def)

lemma bex1_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<exists>!x \<in> A. P x) \<longleftrightarrow> (\<exists>!x \<in> A'. P' x)"
  by (simp add: bex1_def cong: conj_cong)

lemma bex_if_bex1: "\<exists>!x \<in> A. P x \<Longrightarrow> \<exists>x \<in> A. P x"
  by auto

lemma ball_conj_distrib: "(\<forall>x \<in> A. P x \<and> Q x) \<longleftrightarrow> (\<forall>x \<in> A. P x) \<and> (\<forall>x \<in> A. Q x)"
  by auto

lemma antimono_ball_set: "antimono (\<lambda>A. \<forall>x \<in> A. P x)"
  by (intro antimonoI) auto

lemma mono_ball_pred: "mono (\<lambda>P. \<forall>x \<in> A. P x)"
  by (intro monoI) auto

lemma mono_bex_set: "mono (\<lambda>A. \<exists>x \<in> A. P x)"
  by (intro monoI) auto

lemma mono_bex_pred: "mono (\<lambda>P. \<exists>x \<in> A. P x)"
  by (intro monoI) auto


section \<open>Bounded definite description\<close>

definition bthe :: "set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set"
  where "bthe A P \<equiv> The (\<lambda>x. x \<in> A \<and> P x)"


bundle hotg_bounded_the_syntax
begin
syntax "_bthe" :: "[pttrn, set, bool] \<Rightarrow> set" ("(3THE _ \<in> _./ _)" [0, 0, 10] 10)
end
bundle no_hotg_bounded_the_syntax
begin
no_syntax "_bthe" :: "[pttrn, set, bool] \<Rightarrow> set" ("(3THE _ \<in> _./ _)" [0, 0, 10] 10)
end
unbundle hotg_bounded_the_syntax

translations "THE x \<in> A. P" \<rightleftharpoons> "CONST bthe A (\<lambda>x. P)"

lemma bthe_eqI [intro]:
  assumes "P a"
  and "a \<in> A"
  and "\<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> x = a"
  shows "(THE x \<in> A. P x) = a"
  unfolding bthe_def by (auto intro: assms)

lemma
  bthe_memI: "\<exists>!x \<in> A. P x \<Longrightarrow> (THE x \<in> A. P x) \<in> A" and
  btheI: "\<exists>!x \<in> A. P x \<Longrightarrow> P (THE x \<in> A. P x)"
  unfolding bex1_def bthe_def by (auto simp: theI'[of "\<lambda>x. x \<in> A \<and> P x"])


end
