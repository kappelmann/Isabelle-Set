theory mizar_string
imports "../MML/xboole_0"

\<comment>\<open> Labels for the Isabelle/Mizar formulation of structures \<close>

begin

lemma prefix_in_irreflexivity:
  "irreflexivity object prefix_in"
    using prefix_in_asymmetry by auto

mdef Succ :: "Set \<Rightarrow> Set" ("Succ _" [90] 90) where
  "func Succ X \<rightarrow> set equals X \<union> {X}"
    by mauto

lemma Succ_1: "X \<noteq> Y \<Longrightarrow> Succ X \<noteq> Succ Y"
proof
  assume A1: "X\<noteq>Y" "Succ X = Succ Y"
  have "Y in Succ Y" using Succ tarski_def_1 xboole_0_def_3 by auto
  hence "Y in X \<union> {X}" using Succ A1(2) by auto
  hence A2: "Y in X" using A1(1) tarski_def_1 xboole_0_def_3 by auto
  have "X in Succ X" using Succ tarski_def_1 xboole_0_def_3 by auto
  hence "X in Y \<union> {Y}" using Succ A1(2) by auto
  hence "X in Y" using A1(1) tarski_def_1 xboole_0_def_3 by auto
  thus "False" using A2 prefix_in_asymmetry[of X Y] by auto
qed

lemma Succ_2: "x in Succ Y \<Longrightarrow> x in Succ Succ Y" using Succ tarski_def_1 xboole_0_def_3 by simp
lemma Succ_3: "x in Succ Y \<Longrightarrow> x \<noteq> Succ Y" using prefix_in_irreflexivity by auto
lemma Succ_4: "x in Succ Y \<Longrightarrow> Succ Y \<noteq> x" using prefix_in_irreflexivity by auto
lemma Succ_5: "X in Succ X" using Succ tarski_def_1 xboole_0_def_3 by auto

lemmas string = Succ_1 Succ_2 Succ_3 Succ_4 Succ_5 tarski_def_1 xboole_0_def_3[OF all_set all_set]

definition carrier :: Set
  where "carrier \<equiv> {}"

abbreviation ZeroF :: Set ("ZeroF")
  where "ZeroF \<equiv> Succ carrier"

abbreviation OneF :: Set ("OneF")
  where "OneF \<equiv> Succ ZeroF"

abbreviation multF :: Set ("multF")
  where "multF \<equiv> Succ OneF"

abbreviation addF :: Set ("addF")
  where "addF \<equiv> Succ multF"

abbreviation lmult :: Set ("lmult")
  where "lmult \<equiv> Succ addF"

abbreviation rmult :: Set ("rmult")
  where "rmult \<equiv> Succ lmult"

abbreviation topology :: Set ("topology")
  where "topology \<equiv> Succ rmult"

abbreviation ObjectKind :: Set ("Object-Kind")
  where "Object-Kind \<equiv> Succ topology"

abbreviation ValuesF :: Set ("ValuesF")
  where "ValuesF \<equiv> Succ Object-Kind"

abbreviation InstructionsF :: Set ("InstructionsF")
  where "InstructionsF \<equiv> Succ ValuesF"

abbreviation Execution :: Set ("Execution")
  where "Execution \<equiv> Succ InstructionsF"

abbreviation carrierP :: Set ("carrier`")
  where "carrier` \<equiv> Succ Execution"

abbreviation Source :: Set ("Source")
  where "Source \<equiv> Succ carrier`"

abbreviation Target :: Set ("Target")
  where "Target \<equiv> Succ Source"

abbreviation Comp :: Set ("Comp")
  where "Comp \<equiv> Succ Target"

(*
abbreviation testA :: Set ("testA")
  where "testA \<equiv> Succ Comp"

abbreviation testB :: Set ("testB")
  where "testB \<equiv> Succ testA"
*)


end
