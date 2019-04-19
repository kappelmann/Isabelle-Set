theory tarski
imports tarski_0

begin

reserve x,y,z,u for object
reserve N,M,X,Y,Z for set

mtheorem tarski_th_1:
  "for x being object holds x is set"
  by (fact tarski_0_1)

mtheorem tarski_th_2:
  "(for x being object holds x in X \<longleftrightarrow> x in Y) \<longrightarrow> X = Y"
  by (fact tarski_0_2)

mdef tarski_def_1 ("{ _ }") where
  mlet "y be object"
  "func { y } \<rightarrow> set means \<lambda>it.
    for x being object holds x in it \<longleftrightarrow> x = y"
proof -
  \<comment>\<open>existence\<close>
  show "ex it be set st for x be object holds x in it iff x = y" using tarski_0_3 by force
  
  \<comment>\<open>uniqueness\<close>
  fix X1 X2 assume "X1 be set" "X2 be set" and
    A1: "for x be object holds x in X1 iff x = y" and
    A2: "for x be object holds x in X2 iff x = y"
  show "X1 = X2"
  proof -
    {
      fix z assume "z be object"
      have "z in X1 iff z = y" using A1 by auto
      hence "z in X1 iff z in X2" using A2 by auto
    }
    thus ?thesis using tarski_0_2 by auto
  qed
qed auto

mdef tarski_def_2 ("{ _ , _ }") where
  mlet "z be object"
  "func { y, z } \<rightarrow> set means \<lambda>it.
    for x being object holds x in it iff x = y \<or> x = z"
proof -
  \<comment>\<open>existence\<close>
  show "ex it be set st for x be object holds x in it iff x = y \<or> x = z" using tarski_0_3 by auto

  \<comment>\<open>uniqueness\<close>
  fix X1 X2 assume "X1 be set" "X2 be set" and
    A1: "for x be object holds x in X1 iff x = y \<or> x = z" and
    A2: "for x be object holds x in X2 iff x = y \<or> x = z"
  show "X1 = X2"
  proof -
    {
      fix x assume "x be object"
      have "x in X1 iff x = y \<or> x = z" using A1 by auto
      hence "x in X1 iff x in X2" using A2 by auto
    }
    thus ?thesis using tarski_0_2 by auto
  qed
qed auto

theorem tarski_def_2_commutativity:
fixes y z assumes "y be object" "z be object"
shows "{y, z} = {z, y}"
  using tarski_def_2[of y z] tarski_def_2[of z y] tarski_0_2[of "{y, z}" "{z, y}"]
  by auto
  (* Notice the above theorem is formulated in terms of a Pure natural deduction rule,
     instead of as a HOL boolean predicate. We did this in order to be able to instantiate
     variables in the proof. *)

mdef tarski_def_3 ("_ c= _") where
  mlet "X be set", "Y be set"
  "pred X c= Y means
    for x being object holds x in X implies x in Y" .

theorem tarski_def_3_reflexivity:
  "for Y be set holds (Y c= Y)"
  using tarski_def_3_def by auto

mdef tarski_def_4 ("union  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func unionTARSKIK3 X \<rightarrow> setHIDDENM2 means

  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex Y be setHIDDENM2 st x inHIDDENR3 Y & Y inHIDDENR3 X)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex Y be setHIDDENM2 st x inHIDDENR3 Y & Y inHIDDENR3 X)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex Y be setHIDDENM2 st x inHIDDENR3 Y & Y inHIDDENR3 X)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex Y be setHIDDENM2 st x inHIDDENR3 Y & Y inHIDDENR3 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem tarski_th_3:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X implies ( ex Y be setHIDDENM2 st Y inHIDDENR3 X &  not ( ex x be objectHIDDENM1 st x inHIDDENR3 X & x inHIDDENR3 Y))"
  using tarski_0_th_5 sorry

abbreviation(input) TARSKIR2(" _ inTARSKIR2  _ " [50,50]50) where
  "x inTARSKIR2 X \<equiv> x inHIDDENR3 X"

mtheorem TARSKIR2_asymmetry:
" for x be setHIDDENM2 holds  for X be setHIDDENM2 holds x inTARSKIR2 X implies  not X inTARSKIR2 x"
sorry

theorem tarski_sch_1:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds Pp2(x,y) & Pp2(x,z) implies y =HIDDENR1 z"
  shows " ex X be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 X iff ( ex y be objectHIDDENM1 st y inHIDDENR3 Af0 & Pp2(y,x))"
sorry

mdef tarski_def_5 ("[TARSKIK4 _ , _ ]" [0,0]356 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"func [TARSKIK4 x,y ] \<rightarrow> objectHIDDENM1 equals

  {TARSKIK2 {TARSKIK2 x,y },{TARSKIK1 x} }"
proof-
  (*coherence*)
    show "{TARSKIK2 {TARSKIK2 x,y },{TARSKIK1 x} } be objectHIDDENM1"
       sorry
qed "sorry"

mdef tarski_def_6 ("'( _ , _ ')are-equipotentTARSKIR3" [0,0]50 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"pred (X,Y)are-equipotentTARSKIR3 means

   ex Z be setHIDDENM2 st (( for x be objectHIDDENM1 holds x inHIDDENR3 X implies ( ex y be objectHIDDENM1 st y inHIDDENR3 Y & [TARSKIK4 x,y ] inHIDDENR3 Z)) & ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies ( ex x be objectHIDDENM1 st x inHIDDENR3 X & [TARSKIK4 x,y ] inHIDDENR3 Z))) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for u be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 Z & [TARSKIK4 z,u ] inHIDDENR3 Z implies (x =HIDDENR1 z iff y =HIDDENR1 u))"..

end
