\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Axiom of Choice for @{typ set}\<close>
theory HOTG_Choice
  imports
    HOTG_Functions_Monotone
begin

text \<open>The axiom of choice.\<close>
axiomatization where choice: "\<And>S. \<emptyset> \<notin> S \<Longrightarrow> \<exists>(f :: set \<Rightarrow> set). ((X : S) \<Rightarrow> X) f"

lemma choice_if_empty_not_memE:
  assumes "\<emptyset> \<notin> S"
  obtains f :: "set \<Rightarrow> set" where "((X : S) \<Rightarrow> X) f"
  using assms choice by fastforce

end