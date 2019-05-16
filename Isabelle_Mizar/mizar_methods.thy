theory mizar_methods
imports "../MML/tarski_0"

\<comment>\<open> Proof methods \<close>

begin

section \<open> For logical reasoning \<close>

method purify = (rule ballI exI notI impI)+

section \<open> For abbreviated properties \<close>

method commutativity uses def = (
  rule ballI, rule ballI, rule tarski_0_2[rule_format], simp only: def, mauto; fastforce+
)

method reflexivity uses def = (
  rule ballI, simp only: def, mauto; fastforce+
)

end
