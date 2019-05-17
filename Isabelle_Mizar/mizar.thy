theory mizar
imports mizar_HOL

begin

no_notation All (binder "\<forall>" 10) and Ex (binder "\<exists>" 10)
notation All (binder "\<forall>\<^sub>L" 10) and Ex (binder "\<exists>\<^sub>L" 10)

abbreviation ty_membership :: "Set \<Rightarrow> Ty \<Rightarrow> o" (infix "be" 45)
  where "x be T \<equiv> x ::: T"

notation (input) ty_membership (infix "is" 45)

abbreviation define_ty :: "Ty \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> Ty"
  where
  "define_ty(parent, cond, property) \<equiv>
    Type (\<lambda>x. x be parent \<and> (cond(x) \<longrightarrow> property(x)))"

definition inhabited :: "Ty \<Rightarrow> o"
  where "inhabited(D) \<longleftrightarrow> (\<exists>\<^sub>Lx. x be D)"

lemma inhabitedI[intro?]: "x be D \<Longrightarrow> inhabited(D)"
  unfolding inhabited_def by auto

consts choice :: "Ty \<Rightarrow> Set" ("the _" 52)

axiomatization where
  define_ty_cond: "x be parent \<and> \<not>cond(x) \<longrightarrow> inhabited(define_ty(parent, cond, property))" and
  choice_ax: "inhabited(M) \<Longrightarrow> (the M) be M"

lemma define_ty_property:
  assumes "T \<equiv> define_ty(parent, cond, property)"
  shows "(x be T \<longrightarrow> x be parent \<and> (cond(x) \<longrightarrow> property(x))) \<and>
    (x be parent \<and> cond(x) \<and> property(x) \<longrightarrow> x be T) \<and>
    (x be parent \<and> \<not>cond(x) \<longrightarrow> inhabited(T))"
  using assms define_ty_cond
  by auto

lemma define_ty_property_true:
  "x be define_ty(ty, \<lambda>_. True, prop) \<longleftrightarrow> x be ty \<and> prop(x)"
  by auto

definition Ball :: "Ty \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> o"
  where [simp]: "inhabited(D) \<Longrightarrow> Ball(D, P) \<longleftrightarrow> (\<forall>\<^sub>Lx. x be D \<longrightarrow> P(x))"

definition Bex :: "Ty \<Rightarrow> (Set \<Rightarrow> o) \<Rightarrow> o"
  where "Bex(D, P) \<longleftrightarrow> \<not>Ball(D, \<lambda>x. \<not>P(x))"

lemma Bex_property[simp]:
  "inhabited(D) \<Longrightarrow> Bex(D, P) \<longleftrightarrow> (\<exists>\<^sub>Lx. x be D \<and> P(x))"
  using Bex_def
  by simp

nonterminal vgs and bg and vs
syntax
  "_BallI" :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("\<forall>_. _" 10)
  "_Ball"  :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3for _ holds _)" [0, 10] 10)
  "_Ball2" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ holds _)" [0, 0, 10] 10)
  "_Ball3" :: "vgs \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o" ("(3for _ st _ _)" [0, 10, 10] 10)
  "_Bex"   :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("(3ex _ st _)" [0, 10] 10)
  "_BexI"  :: "vgs \<Rightarrow> o \<Rightarrow> o"      ("\<exists>_. _" 10)
  "_vgs"   :: "bg \<Rightarrow> vgs \<Rightarrow> vgs"   (infixr "," 15)
  ""       :: "bg \<Rightarrow> vgs"          ("_")
  "_nbg"   :: "vs \<Rightarrow> vgs"          ("_")
  "_bg"    :: "vs \<Rightarrow> Ty \<Rightarrow> bg"     (infix "being" 20)
  "_bg"    :: "vs \<Rightarrow> Ty \<Rightarrow> bg"     (infix "be" 20)
  "_bg"    :: "vs \<Rightarrow> Ty \<Rightarrow> bg"     (infix ":" 20)
  "_vs"    :: "pttrn \<Rightarrow> vs \<Rightarrow> vs"  (infixr "," 25)
  ""       :: "pttrn \<Rightarrow> vs"        ("_")
  "_BallML1" :: "vgs \<Rightarrow> o \<Rightarrow> o"
  "_BallML2" :: "vs \<Rightarrow> o \<Rightarrow> o"
  "_BexML1"  :: "vgs \<Rightarrow> o \<Rightarrow> o"
  "_BexML2"  :: "vs \<Rightarrow> o \<Rightarrow> o"
translations
  "_Ball2 (vs, c, e)" \<rightleftharpoons> "_Ball (vs, CONST imp(c, e))"
  "_Ball3 (vs, c, e)" \<rightleftharpoons> "_Ball (vs, CONST imp(c, e))"
  "_Ball (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Ball (bg, _Ball (vgs, P))"
  "_Ball (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BallML1 (_bg (_vs (v, vs), D), P)"
  "_Ball (_nbg (vs), P)" \<rightharpoonup> "_BallML2 (vs, P)"
  "_Bex (_vgs (bg, vgs), P)" \<rightleftharpoons> "_Bex (bg, _Bex (vgs, P))"
  "_Bex (_bg (_vs (v, vs), D), P)" \<rightleftharpoons> "_BexML1 (_bg (_vs (v, vs), D), P)"
  "_Bex (_nbg (vs), P)" \<rightharpoonup> "_BexML2 (vs, P)"
  "_BallML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Ball(D,(%v. _Ball (_bg(vs, D), P)))"
  "_BexML1 (_bg (_vs (v, vs), D), P)" \<rightharpoonup> "CONST Bex(D,(%v. _Bex (_bg(vs, D), P)))"
  "_BallI (vs, P)" \<rightharpoonup> "_Ball (vs, P)"
  "_BexI (vs, P)" \<rightharpoonup> "_Bex (vs, P)"
  "for x being D holds P" \<rightharpoonup> "CONST mizar.Ball(D,(%x. P))"
  "ex x being D st P" \<rightharpoonup> "CONST mizar.Bex(D,(%x. P))"
  "\<forall>y being D . P" \<rightleftharpoons> "CONST mizar.Ball(D,(\<lambda>y. P))"
  "\<exists>y being D . P" \<rightleftharpoons> "CONST mizar.Bex(D,(\<lambda>y. P))"

lemma ballI [intro!]: 
  "(\<And>x. x be D \<Longrightarrow> P(x)) \<Longrightarrow> inhabited(D) \<Longrightarrow> \<forall>x: D. P(x)"
  by simp

lemma bspec [dest?]:
  "\<forall>x: D. P(x) \<Longrightarrow> inhabited(D) \<Longrightarrow> x be D \<Longrightarrow> P(x)"
  by simp

lemma ballE [elim]:
  "\<forall>x: D. P(x) \<Longrightarrow> inhabited(D) \<Longrightarrow> (x be D \<Longrightarrow> P(x) \<Longrightarrow> Q) \<Longrightarrow> (\<not> x be D \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (unfold Ball_def) blast

lemma bexI [intro]:
  "P(x) \<Longrightarrow> x be D \<Longrightarrow> inhabited(D) \<Longrightarrow> \<exists>x: D. P(x)"
  unfolding Bex_def
  by blast
    
lemma rev_bexI [intro?]:
  "inhabited(D) \<Longrightarrow> x be D \<Longrightarrow> P(x) \<Longrightarrow> \<exists>x: D. P(x)"
  by (unfold Bex_def) blast

lemma bexE [elim!]:
  "\<exists>x: A. P(x) \<Longrightarrow> inhabited(A) \<Longrightarrow> (\<And>x. x be A \<Longrightarrow> P(x) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by auto

lemma atomize_conjL[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (A \<and> B \<Longrightarrow> C)"
  by rule iprover+
lemma atomize_conjL2[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D)"
  by rule iprover+
lemma atomize_conjL3[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E)"
  by rule iprover+
lemma atomize_conjL4[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F)"
  by rule iprover+
lemma atomize_conjL5[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G)"
  by rule iprover+
lemma atomize_conjL6[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H)"
  by rule iprover+
lemma atomize_conjL7[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I) \<equiv>
    (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I)"
  by rule iprover+
lemma atomize_conjL8[atomize_elim]:
  "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I \<Longrightarrow> J) \<equiv>
    (A \<and> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> F \<Longrightarrow> G \<Longrightarrow> H \<Longrightarrow> I \<Longrightarrow> J)"
  by rule iprover+

lemmas [rulify] =
  atomize_conjL[symmetric] atomize_conjL2[symmetric]
  atomize_conjL3[symmetric] atomize_conjL4[symmetric]
  atomize_conjL5[symmetric] atomize_conjL6[symmetric]
  atomize_conjL7[symmetric] atomize_conjL8[symmetric]

lemma iffI2: "A \<longrightarrow> B \<Longrightarrow> B \<longrightarrow> A \<Longrightarrow> A \<longleftrightarrow> B" by iprover
lemma iffI3: "A \<longrightarrow> B \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<longleftrightarrow> B" by iprover
lemma disjCI2: "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by auto
lemma aaI: "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P" by auto

ML \<open>
fun conj_elims th =
  (case dest_Trueprop (Thm.concl_of th) of
    (@{const conj} $ _ $ _) =>
      conj_elims (th RS @{thm conjunct1}) @ conj_elims (th RS @{thm conjunct2})
  | _ => [th])
  handle TERM _ => [th]
\<close>

section \<open> Mizar article "HIDDEN" \<close>

(* object is the root of the type hierarchy *)

definition object :: Ty
  where "object \<equiv> Type (\<lambda>_. True)"

lemma object_root: "x be object"
  unfolding object_def by auto

axiomatization where object_exists: "inhabited(object)"

consts prefix_in :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "in" 50)

declare object_root[simp]

lemma def_ty_property_object:
  "x be D \<Longrightarrow> x is define_ty(object, \<lambda>it. it be D, prop) \<longleftrightarrow> prop(x)"
  by auto

definition set where
  "set \<equiv> object"

(*
lemma hidden_mode: "x be set \<Longrightarrow> x be object" 
  using set_def by simp
*)

abbreviation (input) theProp
  where "theProp(ty, prop) \<equiv> the define_ty(ty, \<lambda>_. True, prop)"

lemma ty_intersection: "(x be t1 \<bar> t2) \<longleftrightarrow> (x be t1 \<and> x be t2)"
  by (auto intro: Int_TypeI Int_TypeD1 Int_TypeD2)

definition NON ("non _" [102] 101)
  where "non A \<equiv> define_ty(object, \<lambda>_. True, \<lambda>x. \<not> x is A)"
  
lemma non_property: "x is non A \<longleftrightarrow> \<not> x is A"
  using define_ty_property_true NON_def by simp

lemmas [simp] = ty_intersection non_property

end
