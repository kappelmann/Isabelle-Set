theory Notation_Cleanup
  imports Main
begin

text \<open> We need to get rid of a lot of HOL-specific syntax, which would conflict
with set-theoretic syntax.
\<close>

bundle no_hol_notation
begin

no_notation
  HOL.disj (infixr "|" 30) and

  Set.empty ("{}") and
  Set.member ("(_/ : _)" [51, 51] 50) and
  Set.member ("(_/ \<in> _)" [51, 51] 50) and
  Set.not_member  ("'(\<notin>')") and
  Set.not_member  ("(_/ \<notin> _)" [51, 51] 50) and
  union (infixl "\<union>" 65) and
  inter (infixl "\<inter>" 70) and
  subset ("(_/ \<subset> _)" [51, 51] 50) and
  subset_eq ("(_/ \<subseteq> _)" [51, 51] 50) and
  Fun.comp (infixl "\<circ>" 55) and
  Fun.comp (infixl "o" 55) and
  Nil ("[]") and
  Cons (infixr "#" 65) and
  times (infixl "*" 70) and
  relcompp (infixr "OO" 75) and
  relcomp(infixr "O" 75) and
  minus (infixl "-" 65) and
  uminus ("- _" [81] 80) and
  plus (infixl "+" 65) and
  Complete_Lattices.Union ("\<Union>") and
  Complete_Lattices.Inter ("\<Inter>")

end

unbundle no_hol_notation


text \<open> Unfortunately, the following cannot be put into a bundle \<close>

no_syntax
  "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
  "_Finset" :: "args \<Rightarrow> 'a set"    ("{(_)}")
  "_list" :: "args => 'a list"    ("[(_)]")
  "_listcompr" :: "'a \<Rightarrow> lc_qual \<Rightarrow> lc_quals \<Rightarrow> 'a list"  ("[_ . __")

  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/\<in>_)./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>(_/\<in>_)./ _)" [0, 0, 10] 10)
  
  "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    ("(1{_./ _})")
  "_Collect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  ("(1{(_/ \<in> _)./ _})")

  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)
  "_INTER1"     :: "pttrns \<Rightarrow> 'b set \<Rightarrow> 'b set"           ("(3\<Inter>_./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 0, 10] 10)


hide_const (open)
  Set.empty finite union dom set inter Func
  Map.empty
  even Nat
  Relation.Field

  (* Code_Target_Nat.Nat *)
  Nat.Nat
  Set.Pow

end