theory ZF_Tests
  imports ZF
begin

consts carrier :: "i \<Rightarrow> i"
consts add :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
consts Int_Add :: i
consts Nat_Add :: i

lemma [TC]: "x \<in> carrier(A) \<Longrightarrow> y \<in> carrier(A) \<Longrightarrow> add(A, x, y) \<in> carrier(A)"
  sorry

lemma [TC]: "x \<in> carrier(Nat_Add) \<Longrightarrow> x \<in> carrier(Int_Add)"
  sorry

schematic_goal
  "x \<in> carrier(Nat_Add) \<Longrightarrow> y \<in> carrier(Int_Add) \<Longrightarrow> add(?A, x, y) \<in> carrier(?A)"
  by typecheck (*greedy instantiation leads to unprovable goal; can be solved
  by re-stating carrier lemma with subtyping judgements*)
  oops

lemma "x \<in> carrier(Nat_Add) \<Longrightarrow> y \<in> carrier(Int_Add) \<Longrightarrow> add(Int_Add, x, y) \<in> carrier(Int_Add)"
  by typecheck

consts nat :: i
consts int :: i
consts pos_int :: i
consts succ :: "i \<Rightarrow> i"

lemma [TC]: "x \<in> nat \<Longrightarrow> x \<in> int"
  sorry

lemma [TC]: "x \<in> nat \<Longrightarrow> succ(x) \<in> nat"
  sorry

lemma "x \<in> nat \<Longrightarrow> succ(x) \<in> int"
  by typecheck

lemma [iff]: "x \<in> pos_int \<longleftrightarrow> x \<in> nat"
  sorry

(*adding the following two instead will make the typechecker loop*)
(* lemma [TC]: "x \<in> pos_int \<Longrightarrow> x \<in> nat"
  sorry

lemma [TC]: "x \<in> nat \<Longrightarrow> x \<in> pos_int"
  sorry *)

lemma [TC]: "x \<in> int \<Longrightarrow> succ(x) \<in> int"
  sorry

lemma "x \<in> int \<Longrightarrow> succ(x) \<in> pos_int"
  by (typecheck | auto)+ (*no progress or unprovable goal*)

end