section \<open>Setup for Isabelle/Set MML\<close>

theory MML_setup
imports "../Isabelle_Set/Set_Theory"

begin

subsection \<open>Basic soft types\<close>

abbreviation set :: "set type"
  where "set \<equiv> any"

lemma all_sets_set [intro]: "x : set" using any_typeI .

subsection \<open>Some abbreviations\<close>

abbreviation (input) prefix_asymmetry ("asymmetry _ _")
  where "asymmetry dom R \<equiv> \<forall>x1 : dom. \<forall>x2 : dom. \<not>(R x1 x2 \<and> R x2 x1)"

abbreviation (input) prefix_irreflexive ("irreflexivity _ _")
  where "irreflexivity dom R \<equiv> \<forall>x : dom. \<not>R x x"

abbreviation (input) prefix_reflexive ("reflexivity _ _")
  where "reflexivity dom R \<equiv> \<forall>x : dom. R x x"

abbreviation (input) prefix_symmetry ("symmetry _ _")
  where "symmetry dom R \<equiv> \<forall>x1 : dom. \<forall>x2 : dom. R x1 x2 \<longrightarrow> R x2 x1"

abbreviation (input) prefix_connectedness ("connectedness _ _")
  where "connectedness dom R \<equiv> \<forall>x1 : dom. \<forall>x2 : dom. R x1 x2 \<or> R x2 x1"

abbreviation (input) prefix_involutiveness ("involutiveness _ _")
  where "involutiveness dom f \<equiv> \<forall>x : dom.  f (f x) = x"

abbreviation (input) prefix_projectivity ("projectivity _ _")
  where "projectivity dom f \<equiv> \<forall>x : dom. f (f x) = f x"

abbreviation (input) prefix_idempotence ("idempotence _ _")
  where "idempotence dom B \<equiv> \<forall>x : dom. B x x = x"

abbreviation (input) prefix_commutativity ("commutativity _ _")
  where "commutativity dom B \<equiv> \<forall>x1 : dom. \<forall>x2 : dom. B x1 x2 = B x2 x1"


end
