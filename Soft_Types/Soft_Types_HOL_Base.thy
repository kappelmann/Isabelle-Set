\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Basics Of Soft Types\<close>
theory Soft_Types_HOL_Base
  imports
    ML_Unification.ML_Unification_HOL_Setup
    Transport.HOL_Syntax_Bundles_Base
begin

text \<open>This theory introduces a generic notion of soft types based on HOL
predicates. It contains the basic definitions and technical tool setup.\<close>

unbundle no_HOL_ascii_syntax

subsection \<open>Basic type judgments\<close>

text \<open>Soft types are "just" predicates wrapped up in a constructor.\<close>

typedecl 'a type

axiomatization
  type :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type\<close> and
  adj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow> 'a type\<close>  and
  type_of :: \<open>'a \<Rightarrow> 'a type \<Rightarrow> bool\<close>
where
  meaning_of_adj: "type_of x (adj P T) \<equiv> P x \<and> type_of x T" and
  meaning_of_type: "type_of x (type P) \<equiv> P x"

bundle soft_type_base_syntax
begin notation adj (infixr "\<sqdot>" \<comment>\<open>\<sqdot>\<close> 56) and type_of (infix "\<Ztypecolon>" 39) end
bundle no_soft_type_base_syntax
begin no_notation adj (infixr "\<sqdot>" \<comment>\<open>\<sqdot>\<close> 56) and type_of (infix "\<Ztypecolon>" 39) end
unbundle soft_type_base_syntax

definition "of_type T x \<equiv> x \<Ztypecolon> T"

axiomatization where type_ext: "\<And>T T'. of_type T = of_type T' \<Longrightarrow> T = T'"

lemma of_type_eq: "of_type = (\<lambda>T x. x \<Ztypecolon> T)" unfolding of_type_def by simp
lemma of_type_iff [iff]: "of_type T x \<longleftrightarrow> x \<Ztypecolon> T" unfolding of_type_def by simp

named_theorems type_to_HOL_simp "simplification rules going from soft types to HOL concepts"
declare of_type_iff[symmetric, type_to_HOL_simp]

lemma of_type_eq_type_of_uhint [uhint]:
  assumes "x \<equiv> x'"
  and "T \<equiv> T'"
  shows "of_type T x \<equiv> x' \<Ztypecolon> T'"
  using assms by simp

lemma eq_if_of_type_eq_of_type:
  assumes "of_type T = of_type S"
  shows "T = S"
  using assms by (rule type_ext)

corollary eq_iff_of_type_eq_of_type [type_to_HOL_simp]: "T = S \<longleftrightarrow> of_type T = of_type S"
  using eq_if_of_type_eq_of_type by blast

lemma of_type_type_eq_self [type_to_HOL_simp]: "of_type (type P) = P"
  by (intro ext) (simp add: meaning_of_type)

lemma of_type_type_iff_self: "of_type (type P) x \<longleftrightarrow> P x"
  unfolding of_type_type_eq_self by simp

lemma type_of_typeI: "P x \<Longrightarrow> x \<Ztypecolon> type P"
  unfolding type_to_HOL_simp by assumption

lemma type_of_typeD: "x \<Ztypecolon> type P \<Longrightarrow> P x"
  unfolding type_to_HOL_simp by assumption

lemma type_of_typeE:
  assumes "x \<Ztypecolon> type P"
  obtains "P x"
  using assms unfolding type_to_HOL_simp by auto

lemma has_adjI: "\<lbrakk>P x; x \<Ztypecolon> T\<rbrakk> \<Longrightarrow> x \<Ztypecolon> P \<sqdot> T"
  unfolding meaning_of_adj by auto

lemma
  has_adjD1: "x \<Ztypecolon> P \<sqdot> T \<Longrightarrow> P x" and
  has_adjD2: "x \<Ztypecolon> P \<sqdot> T \<Longrightarrow> x \<Ztypecolon> T"
  unfolding meaning_of_adj by auto

lemma has_adjE:
  "\<lbrakk>x \<Ztypecolon> P \<sqdot> T; \<lbrakk>P x; x \<Ztypecolon> T\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding meaning_of_adj by auto


end
