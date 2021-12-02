subsection \<open>Basix Definitions\<close>
theory Fixpoints_Base
imports Sets
begin

definition "prefixpoint X h \<equiv> h X \<subseteq> X"

lemma
  prefixpointI [intro!]: "h X \<subseteq> X \<Longrightarrow> prefixpoint X h" and
  prefixpointD: "prefixpoint X h \<Longrightarrow> h X \<subseteq> X"
  unfolding prefixpoint_def by assumption

lemma prefixpointE [elim]:
  assumes "prefixpoint X h"
  obtains "h X \<subseteq> X"
  using assms by (auto dest: prefixpointD)

definition "postfixpoint X h \<equiv> X \<subseteq> h X"

lemma
  postfixpointI [intro!]: "X \<subseteq> h X \<Longrightarrow> postfixpoint X h" and
  postfixpointD: "postfixpoint X h \<Longrightarrow> X \<subseteq> h X"
  unfolding postfixpoint_def by assumption

lemma postfixpointE [elim]:
  assumes "postfixpoint X h"
  obtains "X \<subseteq> h X"
  using assms by (auto dest: postfixpointD)

definition "fixpoint X h \<equiv> h X = X"

lemma
  fixpointI [intro!]: "h X = X \<Longrightarrow> fixpoint X h" and
  fixpointD: "fixpoint X h \<Longrightarrow> h X = X"
  unfolding fixpoint_def by assumption

lemma fixpointE [elim]:
  assumes "fixpoint X h"
  obtains "h X = X"
  using assms by (auto dest: fixpointD)

lemma fixpoint_iff_prefixpoint_and_postfixpoint:
  "fixpoint X h \<longleftrightarrow> prefixpoint X h \<and> postfixpoint X h"
  by auto


end
