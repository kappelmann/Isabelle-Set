theory Pure_HOL
imports
  Pure
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

begin

text \<open>Extend the Pure logic itself with the usual connectives.\<close>


section \<open>Constants, quantifiers, and connectives\<close>

abbreviation Equal (infix "=" 2)
  where "(x = y) \<equiv> (x \<equiv> y)"

definition "True \<equiv> (\<And>P :: prop. P = P)"
definition "False \<equiv> (\<And>P :: prop. P = True)"

definition All :: "('a \<Rightarrow> prop) \<Rightarrow> prop" (binder "\<forall>" [0] 0)
  where "(\<forall>x. PROP P x) \<equiv> (\<And>x. PROP P x)"

definition Ex :: "('a \<Rightarrow> prop) \<Rightarrow> prop" (binder "\<exists>" [0] 0)
  where "(\<exists>x. PROP P x) \<equiv> (\<forall>Q :: prop. (\<forall>x. PROP P x \<Longrightarrow> PROP Q) \<Longrightarrow> PROP Q)"

definition And (infix "\<and>" 100)
  where "P \<and> Q \<equiv> (PROP P &&& PROP Q)"

definition Or (infix "\<or>" 99)
  where "P \<or> Q \<equiv> (\<forall>R. \<lbrakk>PROP P \<Longrightarrow> PROP R; PROP Q \<Longrightarrow> PROP R\<rbrakk> \<Longrightarrow> PROP R)"

definition Not ("(\<not> _)" [101] 900)
  where "\<not>P \<equiv> (PROP P \<Longrightarrow> PROP False)"

definition Iff (infix "\<Longleftrightarrow>" 0)
  where "(P \<Longleftrightarrow> Q) \<equiv> (PROP P \<Longrightarrow> PROP Q) \<and> (PROP Q \<Longrightarrow> PROP P)"


section \<open>Methods\<close>

text \<open>We set up the basic logical solver following the Eisbach user manual.\<close>

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/eqsubst.ML"
\<comment> \<open>Import the @{method subst} method, used for substituting definitional equalities.\<close>

named_theorems intros
named_theorems elims
named_theorems dests
named_theorems simps
named_theorems subst
named_theorems refine

method logic declares intros elims dests subst refine = (
  assumption | unfold All_def | fold All_def |
  rule intros | erule elims | drule dests | frule dests |
  simp add: simps | subst subst | subst (asm) subst |
  (erule refine; solves \<open>logic\<close>)
)+

method_setup move =
  \<open>Scan.succeed (METHOD o (ALLGOALS oo Method.insert_tac))\<close> "Move facts into the goal statements"

\<comment>\<open>Strangely, the move method can solve iterated modus ponens by moving the rule and all premises into the goal state, followed by a call to qed.\<close>
method mp = move


section \<open>Basic axioms and rules\<close>

lemmas mp = meta_mp

lemma TrueI [intros]: "PROP True"
  unfolding True_def .

lemmas tautology = TrueI

lemma FalseE [dest, dests]: "PROP False \<Longrightarrow> PROP P"
unfolding False_def proof -
  assume "\<And>P. P = True"
  hence "PROP P = True" by (rule meta_spec)
  thus "PROP P" using tautology by simp
qed

lemmas explosion = FalseE
method explosion = (rule explosion)

lemmas AllE = meta_spec[folded All_def]
lemmas AllE2 = meta_allE[folded All_def]

method instantiate for pred :: "'a \<Rightarrow> prop" and tm :: 'a = (elim AllE[where ?P=pred and ?x=tm])

lemma ExI:
  assumes "PROP P x"
  shows "\<exists>x. PROP P x"
unfolding Ex_def All_def proof -
  fix Q :: "prop"
  assume "\<And>x. PROP P x \<Longrightarrow> PROP Q"
  with assms show "PROP Q" by mp
qed

lemma ExE:
  assumes "\<exists>x. PROP P x" and "\<forall>x. PROP P x \<Longrightarrow> PROP Q"
  shows "PROP Q"
proof -
  have "(\<forall>x. PROP P x \<Longrightarrow> PROP Q) \<Longrightarrow> PROP Q"
    using
      AllE[where ?P="\<lambda>x. ((\<forall>y. PROP P y \<Longrightarrow> PROP x) \<Longrightarrow> PROP x)" and ?x="PROP Q"]
      assms(1)[unfolded Ex_def]
    by mp
  thus "PROP Q" using assms(2) by mp
qed

lemma AndI [intro, intros]:
  assumes "PROP P" and "PROP Q"
  shows "PROP P \<and> PROP Q"
  unfolding And_def by fact+

lemma AndD1 [dest, dests]:
  assumes "PROP P \<and> PROP Q"
  shows "PROP P"
  using assms unfolding And_def by (rule conjunctionD1)

lemma AndD2 [dest, dests]:
  assumes "PROP P \<and> PROP Q"
  shows "PROP Q"
  using assms unfolding And_def by (rule conjunctionD2)

lemma AndE [elim, elims]:
  assumes "PROP P \<and> PROP Q" and "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R"
  shows "PROP R"
proof -
  from \<open>PROP P \<and> PROP Q\<close> have "PROP P" and "PROP Q" by logic
  thus "PROP R" using assms by mp
qed

lemma OrI1:
  assumes "PROP P"
  shows "PROP P \<or> PROP Q"
  unfolding Or_def using assms by move logic

lemma OrI2:
  assumes "PROP Q"
  shows "PROP P \<or> PROP Q"
  unfolding Or_def using assms by move logic

lemma OrE [elim, elims]:
  assumes "PROP P \<or> PROP Q" and "PROP P \<Longrightarrow> PROP R" and "PROP Q \<Longrightarrow> PROP R"
  shows "PROP R"
  apply (rule AllE[where ?P="\<lambda>R. (\<lbrakk>PROP P \<Longrightarrow> PROP R; PROP Q \<Longrightarrow> PROP R\<rbrakk> \<Longrightarrow> PROP R)"])
  by (fold Or_def) fact+

lemma NotI [intro, intros]:
  assumes "PROP P \<Longrightarrow> PROP False"
  shows "\<not>PROP P"
  unfolding Not_def by fact

lemma NotE [refine]:
  assumes "\<not>PROP P" and "PROP P"
  shows "PROP Q"
  using assms unfolding Not_def by mp explosion

lemmas contradiction = NotE
method contradiction = (rule contradiction | rule contradiction[rotated])

lemma IffI [intro, intros]:
  assumes "PROP P \<Longrightarrow> PROP Q" and "PROP Q \<Longrightarrow> PROP P"
  shows "PROP P \<Longleftrightarrow> PROP Q"
  unfolding Iff_def by (rule AndI) fact+

lemma IffD1 [dest, dests]:
  assumes "PROP P \<Longleftrightarrow> PROP Q"
  shows "PROP P \<Longrightarrow> PROP Q"
  using assms unfolding Iff_def by (rule AndD1)

lemma IffD2 [dest, dests]:
  assumes "PROP P \<Longleftrightarrow> PROP Q"
  shows "PROP Q \<Longrightarrow> PROP P"
  using assms unfolding Iff_def by (rule AndD2)

lemmas forward_imp = IffD1
lemmas backward_imp = IffD2

text \<open>Logical equivalence is the equality relation on propositions.\<close>

axiomatization where
  Iff_imp_Equal [intros]: "(PROP P \<Longleftrightarrow> PROP Q) \<Longrightarrow> (PROP P = PROP Q)"

lemma Iff_iff_Equal:
  "(PROP P \<Longleftrightarrow> PROP Q) \<Longleftrightarrow> (PROP P = PROP Q)"
  by logic

lemma Iff_is_Equal [simps]:
  "(PROP P \<Longleftrightarrow> PROP Q) = (PROP P = PROP Q)"
  by logic


section \<open>Classical logic\<close>

axiomatization where LEM: "PROP P \<or> \<not>PROP P"

text \<open>Set up disjunctive case analysis:\<close>

thm OrE[OF LEM, where ?P="PROP Z"]

method cases for cs :: "prop" = (rule OrE[OF LEM[where ?P="PROP cs"]])


lemma double_negE:
  assumes "\<not>\<not>PROP P"
  shows "PROP P"
proof (cases "PROP P")
  show "PROP P \<Longrightarrow> PROP P" .
  show "\<not>PROP P \<Longrightarrow> PROP P" by (explosion, fold Not_def, fact)
qed


lemma de_Morgan_And:
  "\<not>(PROP A \<and> PROP B) = \<not>PROP A \<or> \<not>PROP B"
  apply logic
  apply (cases "PROP A")
  apply (cases "PROP B")
  apply logic
  apply (erule OrI1 OrI2)+
  apply logic
done

lemma de_Morgan_Or:
  "\<not>(PROP A \<or> PROP B) = \<not>PROP A \<and> \<not>PROP B"
apply logic defer
apply logic defer
apply logic
proof -
  assume *: "\<not>(PROP A \<or> PROP B)"
  { assume "PROP A"
    hence "PROP A \<or> PROP B" by (rule OrI1)
    thus "PROP False" using * by contradiction }
  { assume "PROP B"
    hence "PROP A \<or> PROP B" by (rule OrI2)
    thus "PROP False" using * by contradiction }
qed


end
