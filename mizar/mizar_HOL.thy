theory mizar_HOL imports
  "HOL-Number_Theory.Number_Theory"
  "HOL-Computational_Algebra.Primes"
  "HOL-Algebra.Group"
  "HOL-Algebra.IntRing"
  "HOL.Int"
(*
  "Bertrands_Postulate.Bertrand"
  "SumSquares.TwoSquares"
  "SumSquares.FourSquares"
  "Fermat3_4.Fermat3"
  "Fermat3_4.Fermat4"
  "HOL-Library.Discrete"
  "HOL-Decision_Procs.Approximation_Bounds"
*)
 "HOL-Eisbach.Eisbach"

begin

setup Pure_Thy.old_appl_syntax_setup

text_raw {*\DefineSnippet{mizar-typedecl}{*}
typedecl Set
typedecl Ty
text_raw {*}%EndSnippet*}

notation
  HOL.eq (infixl "=\<^sub>\<H>" 50)

no_notation
  HOL.eq (infixl "=" 50) and
  HOL.not_equal (infixl "~=" 50) and
  HOL.not_equal (infixl "\<noteq>" 50) and
  HOL.not_equal (infix "\<noteq>" 50) and
  HOL.disj (infixr "|" 30) and

  Set.empty ("{}") and
  Set.member ("(_/ : _)" [51, 51] 50) and
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
  plus (infixl "+" 65)

no_syntax
  "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
  "_Finset" :: "args \<Rightarrow> 'a set"    ("{(_)}")
  "_list" :: "args => 'a list"    ("[(_)]")
  "_listcompr" :: "'a \<Rightarrow> lc_qual \<Rightarrow> lc_quals \<Rightarrow> 'a list"  ("[_ . __")

hide_const
  Set.empty finite union dom set inter Func
  Map.empty
  even Nat
  Relation.Field

  (* Code_Target_Nat.Nat *)
  Nat.Nat

type_synonym o = bool
abbreviation (input) "imp \<equiv> implies"

abbreviation mizeq :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "=" 50)
  where "mizeq \<equiv> HOL.eq"

notation mizeq (infixl "=\<^sub>\<S>" 50)
(*notation
  HOL.eq (infixl "=H" 50)
*)
abbreviation not_eq :: "Set \<Rightarrow> Set \<Rightarrow> o" (infix "<>" 50) where
  "a <> b \<equiv> \<not> HOL.eq(a,b)"
notation not_eq (infixl "\<noteq>" 50)

abbreviation tyeq :: "Ty \<Rightarrow> Ty \<Rightarrow> o" (infixl "=\<^sub>T" 50)
  where "tyeq \<equiv> HOL.eq"

notation (ASCII)
  implies (infixl "implies" 25) and
  iff (infixl "iff" 25) and
  disj (infixl "or" 30) and
  Not ("not _" [40] 40)

syntax (output) "HOL.eq" :: "o \<Rightarrow> o \<Rightarrow> o" (infixl "\<longleftrightarrow>" 25)

ML {*
val basic_ss = HOL_basic_ss;
val main_ss = HOL_ss;
val mk_Trueprop = HOLogic.mk_Trueprop;
val dest_Trueprop = HOLogic.dest_Trueprop;
val eq_const = @{const_name HOL.eq}
*}

end
