(*  Title:      ZF/ZF_Base.thy
    Author:     Lawrence C Paulson and Martin D Coen, CU Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>ASCII syntax\<close>

theory ASCII_Syntax
  imports Ordered_Pair
begin



notation (ASCII)
  cart_prod       (infixr "*" 80) and
  Int             (infixl "Int" 70) and
  Un              (infixl "Un" 65) and
  Subset          (infixl "<=" 50) and
(*  mem             (infixl ":" 50) and *)
  not_mem         (infixl "~:" 50)

syntax (ASCII)
  "_Ball"     :: "[pttrn, i, o] => o"        ("(3ALL _:_./ _)" 10)
  "_Bex"      :: "[pttrn, i, o] => o"        ("(3EX _:_./ _)" 10)
  "_Collect"  :: "[pttrn, i, o] => i"        ("(1{_: _ ./ _})")
  "_Replace"  :: "[pttrn, pttrn, i, o] => i" ("(1{_ ./ _: _, _})")
  "_RepFun"   :: "[i, pttrn, i] => i"        ("(1{_ ./ _: _})" [51,0,51])
  "_UNION"    :: "[pttrn, i, i] => i"        ("(3UN _:_./ _)" 10)
  "_INTER"    :: "[pttrn, i, i] => i"        ("(3INT _:_./ _)" 10)
  "_PROD"     :: "[pttrn, i, i] => i"        ("(3PROD _:_./ _)" 10)
  "_SUM"      :: "[pttrn, i, i] => i"        ("(3SUM _:_./ _)" 10)
  "_lam"      :: "[pttrn, i, i] => i"        ("(3lam _:_./ _)" 10)
  "_Tuple"    :: "[i, is] => i"              ("<(_,/ _)>")
  "_pattern"  :: "patterns => pttrn"         ("<_>")


end
