theory Manual_Type_Checks
  imports "Soft_Types.Soft_Types_HOL"
begin

subsection \<open>Greedy Instantiations and Subtyping\<close>

consts Nat :: "'a type"
consts Int :: "'a type"
consts add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

lemma Int_if_Nat: "x : Nat \<Longrightarrow> x : Int"
  sorry

lemma add_type: "add : A \<Rightarrow> A \<Rightarrow> A"
  sorry

lemma app_type:
  assumes "t : A \<Rightarrow> B"
  and "t : A \<Rightarrow> B \<Longrightarrow> u : A"
  shows "t u : B"
  sorry

(*subtyping in domain and codomain*)
lemma app_type':
  assumes "t : A \<Rightarrow> B'"
  and "t : A \<Rightarrow> B' \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t u : B' \<Longrightarrow> t u : B"
  and "t : A \<Rightarrow> B' \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B"
  sorry

(*subtyping in domain*)
lemma app_type'':
  assumes "t : A \<Rightarrow> B"
  and "t : A \<Rightarrow> B \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t : A \<Rightarrow> B \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B"
  sorry

(*loops if above rules are tagged with intro *)
(* schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : ?T"
  using assms by (-) auto *)

lemma app_dep_type:
  assumes "t : (x : A) \<Rightarrow> B x"
  and "t : (x : A) \<Rightarrow> B x \<Longrightarrow> u : A"
  shows "t u : B u"
  sorry

(*subtyping in domain and codomain*)
lemma app_dep_type':
  assumes "t : (x : A) \<Rightarrow> B' x"
  and "t : (x : A) \<Rightarrow> B' x \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t u : B' u \<Longrightarrow> t u : B u"
  and "t : (x : A) \<Rightarrow> B' x \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B u"
  sorry

(*subtyping in domain*)
lemma app_dep_type'':
  assumes "t : (x : A) \<Rightarrow> B x"
  and "t : (x : A) \<Rightarrow> B x \<Longrightarrow> u : A'"
  (*subtyping*)
  and "t : (x : A) \<Rightarrow> B x \<Longrightarrow> u : A' \<Longrightarrow> u : A"
  shows "t u : B u"
  sorry

lemma
  assumes f_type: "f : (A \<Rightarrow> C) \<Rightarrow> C"
  and c_type: "c : A \<Rightarrow> Bool \<Rightarrow> C"
  shows "f (\<lambda> a. c a True) : C"
  using assms
  apply -
  apply (rule app_type''[where ?t=f])
    apply (rule f_type)
    apply (rule Dep_fun_typeI)
    apply (rule app_type''[where ?t="c a" for a])
      apply (rule app_type''[where ?t="c" for a])
        apply (rule c_type)
        apply assumption
        defer
      apply (rule Any_typeI)
      defer
    defer
  (*subtyping*)
  apply assumption+
  done

(*subtyping in domain and codomain*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : ?T"
  using assms
  apply -
  apply (rule app_type'[where ?t="add n" and ?u="i"])
    apply (rule app_type'[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
      defer
    apply (rule i_type)
    defer
    defer
  (*subtyping*)
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  apply assumption
  apply assumption
  done

(*subtyping in domain*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : ?T"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Int_if_Nat)
  apply assumption
  apply assumption
  done


subsection \<open>Higher-Order Functions\<close>

consts mynat :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

lemma mynat_type: "mynat : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  sorry

(*compound arguments with subtyping in domain*)
schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add (mynat n n) i : ?T"
  using assms
  apply -
  apply (rule app_type''[where ?t="add (mynat n n)" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u="mynat n n"])
      apply (rule add_type)
      apply (rule app_type''[where ?t="mynat n" and ?u="n"])
        apply (rule app_type''[where ?t="mynat" and ?u="n"])
          apply (rule mynat_type)
          apply (rule n_type)
          defer
        apply (rule n_type)
        defer
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply assumption
  apply assumption
  apply (rule app_type''[where ?t="mynat n" and ?u=n])
    apply (rule app_type'[where ?t="mynat" and ?u=n])
      apply (rule mynat_type)
      apply (rule n_type)
      defer
    apply assumption
    defer
  (*subtyping*)
  apply assumption
  defer
  apply (rule app_type'[where ?t="mynat" and ?u=n])
    apply (rule mynat_type)
    apply (rule n_type)
    defer
  apply assumption
  defer
  defer
  (*loops; subtyping goals must be solved by user instead*)
  oops

schematic_goal
  assumes f_type: "f : Nat \<Rightarrow> Int \<Rightarrow> Nat" and g_type: "g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  shows "add f g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  apply (rule app_type''[where ?t="add f" and ?u="g"])
    apply (rule app_type''[where ?t=add and ?u=f])
      apply (rule add_type)
      apply (rule f_type)
      defer
    apply (rule g_type)
    defer
  (*subtyping*)
  apply (rule Dep_fun_typeI)+
  apply (rule app_type'[where ?t="f x" and ?u=y for x y])
    apply (rule app_type''[where ?t="f" and ?u=x for x])
      apply assumption
      apply assumption
      defer
    apply assumption
    defer
    defer
  (*subtyping*)
  apply assumption
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  done

schematic_goal
  assumes f_type: "f : Nat \<Rightarrow> Int \<Rightarrow> Nat" and g_type: "g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  shows "add f g : Nat \<Rightarrow> Nat \<Rightarrow> Int"
  apply (rule Dep_fun_typeI)+
  apply (rule app_type''[where ?t="add f g x" and ?u="y" for x y])
    apply (rule app_type''[where ?t="add f g" and ?u=x for x])
      apply (rule app_type''[where ?t="add f" and ?u=g])
        apply (rule app_type''[where ?t="add" and ?u=f])
          apply (rule add_type)
          apply (rule f_type)
          defer
        apply (rule g_type)
        defer
      apply assumption
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule Dep_fun_typeI)+
  apply (rule app_type'[where ?t="f x" and ?u=y for x y])
    apply (rule app_type''[where ?t="f" and ?u=x for x])
      apply assumption
      apply assumption
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule Int_if_Nat)
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  apply (rule Int_if_Nat)
  apply assumption
  done


subsection \<open>Non-Immediate Subtyping\<close>

schematic_goal
  assumes n_type: "n : A & (B & Nat)" and i_type: "i : Int & B"
  shows "add n i : Int & B"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  (* apply (assumption | (rule Int_typeI | rule Int_if_Nat) | erule Int_typeE)+ *)
  apply (rule Int_typeI)
  apply (erule Int_typeE)+
  apply (rule Int_if_Nat)
  apply assumption
  apply (erule Int_typeE)+
  apply assumption
  apply assumption
  done

schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  shows "add n i : Int \<bar> B"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Union_type_leftI)
  apply (rule Int_if_Nat)
  apply assumption
  apply (rule Union_type_leftI)
  apply assumption
  done

schematic_goal
  assumes n_type: "\<And>x. x : A \<Longrightarrow> n x : B x" and n_type': "\<And>x. x : A \<Longrightarrow> n x : B' x"
  and x_type: "x : A"
  and f_type: "\<And>C. f : (x : A) \<Rightarrow> C x \<Rightarrow> C x"
  shows "f x (n x) : B x & B' x"
  using assms
  apply -
  apply (rule app_dep_type''[where ?t="f x" and ?u="n x"])
    apply (rule app_dep_type''[where ?t=f and ?u=x])
      apply (rule f_type)
      apply (rule x_type)
      defer
    apply (rule n_type)
    defer
  (*subtyping*)
  apply (rule Int_typeI)
  apply assumption
  apply assumption
  apply assumption
  apply assumption
  done


subsection \<open>Type Simplification and Equivalences\<close>

consts Vec :: "'a \<Rightarrow> 'a type"

schematic_goal
  assumes v_type: "v : Vec n" and v'_type: "v' : Vec m"
  and n_eq_m: "n = m"
  shows "add v v' : Vec m"
  using assms
  apply -
  apply (rule app_type''[where ?t="add v" and ?u="v'"])
    apply (rule app_type''[where ?t=add and ?u=v])
      apply (rule add_type)
      apply (rule v_type)
      defer
    apply (rule v'_type)
    defer
  (*subtyping*)
  defer
  apply assumption
  (*left to the user; solvable with integration in simplifier*)
  oops
  (* done *)

consts pos :: "'a \<Rightarrow> bool"

lemma Nat_if_pos_Int:
  assumes "i : Int"
  and "pos i"
  shows "i : Nat"
  sorry

schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  and "pos i"
  shows "add n i : Nat"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply assumption
  apply (rule Nat_if_pos_Int)
  apply assumption
  apply assumption
  done

lemma Int_pos_iff_Nat:
  shows "i : Int & type pos \<longleftrightarrow> i : Nat"
  sorry

schematic_goal
  assumes n_type: "n : Nat" and i_type: "i : Int"
  and "pos i"
  shows "add n i : Int & type pos"
  using assms
  apply -
  apply (rule app_type''[where ?t="add n" and ?u="i"])
    apply (rule app_type''[where ?t=add and ?u=n])
      apply (rule add_type)
      apply (rule n_type)
      defer
    apply (rule i_type)
    defer
  (*subtyping*)
  apply (rule Int_typeI)
  apply (rule Int_if_Nat)
  apply assumption
  defer
  apply (rule Int_typeI)
  apply assumption
  apply (rule has_typeI)
  apply assumption
  apply (rule has_typeI)
  (*left to the user; solvable with integration in simplifier*)
  oops

lemma
  assumes f_type: "f : (x : A) \<Rightarrow> (y : B x) \<Rightarrow> C x y"
  and A_eq_B: "\<And>x. x : A \<Longrightarrow> B x = B' x"
  shows "add f : ((x : A) \<Rightarrow> (y : B' x) \<Rightarrow> C x y) \<Rightarrow> (x : A) \<Rightarrow> (y : B' x) \<Rightarrow> C x y"
  apply (rule app_dep_type'[where ?t="add" and ?u="f"])
    apply (rule add_type)
    apply (rule f_type)
  (*subtyping*)
  apply assumption
  apply (rule Dep_fun_typeI)+
    apply (rule app_dep_type''[where ?t="f x" and ?u=y for x y])
      apply (rule app_dep_type''[where ?t="f" and ?u=x for x])
        apply assumption
        apply assumption
        defer
        defer
      apply assumption
      defer
      defer
    apply assumption
  apply (subst A_eq_B)
  apply assumption
  apply assumption
  done


subsection \<open>Implicit Arguments\<close>

consts List :: "'a type \<Rightarrow> 'a type"
consts nil :: "'a type \<Rightarrow> 'a"
consts cons :: "'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"

lemma nil_type: "nil : (A : Any) \<Rightarrow> List A"
  sorry

lemma cons_type: "cons : (A : Any) \<Rightarrow> A \<Rightarrow> List A \<Rightarrow> List A"
  sorry

schematic_goal
  "?A : ?TA \<Longrightarrow> x : ?TX \<Longrightarrow> ?B : ?TB \<Longrightarrow> cons ?A x (nil ?B) : ?T"
  apply (rule app_dep_type''[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type''[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type''[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply assumption
        defer
      apply assumption
      defer
    apply (rule app_dep_type''[where ?t=nil and ?u=B for B])
      apply (rule nil_type)
      apply assumption
      defer
    defer
  (*subtyping*)
  apply (rule Any_typeI)
  defer
  apply (rule Any_typeI)
  apply assumption
  apply assumption
  done

schematic_goal
  "?A : ?TA \<Longrightarrow> x : ?TX \<Longrightarrow> ?B : ?TB \<Longrightarrow> cons ?A x (nil ?B) : ?T"
  apply (rule app_dep_type[where ?t="cons A x" and ?u="nil B" for A B])
    apply (rule app_dep_type[where ?t="cons A" and ?u="x" for A])
      apply (rule app_dep_type[where ?t="cons" and ?u="A" for A])
        apply (rule cons_type)
        apply (rule Any_typeI)
      apply assumption
    apply (rule app_dep_type[where ?t=nil and ?u=B for B])
      (*Problem: when matching `nil ?B : List ?A = nil ?B : ?C ?B`,
        the higher-order unifier picks `?C=\<lambda>x. ?x` and `?B = List ?A`*)
      apply (rule nil_type)
      apply (rule Any_typeI)
   oops

schematic_goal "?A : ?TA \<Longrightarrow> B : ?TB \<Longrightarrow> nil ?A = B : ?T"
  apply (rule app_dep_type''[where ?t="(=) (nil A)" for A])
    apply (rule app_dep_type''[where ?t="(=)"])
      apply (rule eq_type)
      apply (rule app_dep_type''[where ?t="nil"])
        apply (rule nil_type)
        apply assumption
        defer
      defer
    apply assumption
    defer
  (*subtyping*)
  apply (rule Any_typeI)
  apply assumption
  apply assumption
  done

experiment
  fixes Element :: "'a \<Rightarrow> 'a type"
  and nat :: "'a"
  and zero :: "'a" ("0")
  and succ :: "'a \<Rightarrow> 'a"
  and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vec :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vnil :: "'a \<Rightarrow> 'a"
  and vcons :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and vappend :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes vec_type: "vec: Any \<Rightarrow> Element nat \<Rightarrow> Any"
  and vnil_type: "vnil : (A : Any) \<Rightarrow> Element (vec A 0)"
  and vcons_type: "vcons: (A : Any) \<Rightarrow> (n : Element nat) \<Rightarrow>
    Element A \<Rightarrow> Element (vec A n) \<Rightarrow> Element (vec A (succ n))"
  and add_type: "add: Element nat \<Rightarrow> Element nat \<Rightarrow> Element nat"
  and succ_type: "succ: Element nat \<Rightarrow> Element nat"
  and zero_type: "0: Element nat"
  and vappend_type: "vappend: (A : Any) \<Rightarrow> (n : Element nat) \<Rightarrow> (m : Element nat) \<Rightarrow>
    Element (vec A n) \<Rightarrow> Element (vec A m) \<Rightarrow> Element (vec A (add n m))"
  and add_succ_eq_succ_add: "add (succ n) m = succ (add n m)"
begin

text \<open>The base 'a of the vector and the dimensions are completely inferred:\<close>

schematic_goal
  "?A1 : ?TA1 \<Longrightarrow> ?A2 : ?TA2 \<Longrightarrow> ?A3 : ?TA3 \<Longrightarrow> ?A4 : ?TA4 \<Longrightarrow>
  ?n1 : ?Tn1 \<Longrightarrow> ?n2 : ?Tn2 \<Longrightarrow> ?n3 : ?Tn3 \<Longrightarrow> ?n4 : ?Tn4 \<Longrightarrow>
  ?m1 : ?Tm1 \<Longrightarrow> ?m2 : ?Tm2 \<Longrightarrow> ys : ?Tys \<Longrightarrow> x : ?Tx \<Longrightarrow> xs : ?Txs \<Longrightarrow>
  vappend ?A1 ?n1 ?m1 (vcons ?A2 ?n2 x xs) ys = vcons ?A3 ?n3 x (vappend ?A4 ?n4 ?m2 xs ys) : ?T"
  apply (rule app_dep_type''[where ?t="(=) (vappend A1 n1 m1 (vcons A2 n2 x xs) ys)" for A1 n1 m1 A2 n2])
    apply (rule app_dep_type''[where ?t="(=)"])
      apply (rule eq_type)
      apply (rule app_dep_type''[where ?t="vappend A1 n1 m1 (vcons A2 n2 x xs)" for A1 n1 m1 A2 n2])
        apply (rule app_dep_type''[where ?t="vappend A1 n1 m1" for A1 n1 m1])
          apply (rule app_dep_type''[where ?t="vappend A1 n1" for A1 n1])
            apply (rule app_dep_type''[where ?t="vappend A1" for A1])
              apply (rule app_dep_type''[where ?t="vappend"])
                apply (rule vappend_type)
                apply (assumption)
                defer
              (*unify constraints for matching meta variables*)
              apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 8 1\<close>, assumption)
            defer
          apply (rule app_dep_type''[where ?t="vcons A2 n2 x" for A2 n2])
            apply (rule app_dep_type''[where ?t="vcons A2 n2" for A2 n2])
              apply (rule app_dep_type''[where ?t="vcons A2" for A2])
                apply (rule app_dep_type''[where ?t="vcons"])
                  apply (rule vcons_type)
                  apply (tactic \<open>rotate_tac 1 1\<close>, assumption)
                  defer
                apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
                defer
              apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
            defer
          defer
        apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
        defer
      defer
    apply (rule app_dep_type''[where ?t="vcons A3 n3 x" for A3 n3])
      apply (rule app_dep_type''[where ?t="vcons A3 n3" for A3 n3])
        apply (rule app_dep_type''[where ?t="vcons A3" for A3])
          apply (rule app_dep_type''[where ?t="vcons"])
            apply (rule vcons_type)
            apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
            defer
          apply (tactic \<open>rotate_tac 6 1\<close>, assumption)
          defer
        apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
        defer
      apply (rule app_dep_type''[where ?t="vappend A4 n4 m2 xs" for A4 n4 m2])
        apply (rule app_dep_type''[where ?t="vappend A4 n4 m2" for A4 n4 m2])
          apply (rule app_dep_type''[where ?t="vappend A4 n4" for A4 n4])
            apply (rule app_dep_type''[where ?t="vappend A4" for A4])
              apply (rule app_dep_type''[where ?t="vappend"])
                apply (rule vappend_type)
                apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
                defer
              apply (tactic \<open>rotate_tac 7 1\<close>, assumption)
              defer
            apply (tactic \<open>rotate_tac 9 1\<close>, assumption)
            defer
          apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
          defer
        apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
        defer
      defer
    defer
  (*subtyping*)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 8 1\<close>, assumption)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 15 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 14 1\<close>, assumption)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 6 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 11 1\<close>, assumption)
  apply (rule Any_typeI)
  apply (tactic \<open>rotate_tac 7 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 9 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 12 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 10 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 15 1\<close>, assumption)
  apply (tactic \<open>rotate_tac 14 1\<close>)
  apply (simp only: add_succ_eq_succ_add)
  done
  (*assumptions can be cleaned by merging assumptions for meta variables
    and discharging remaining assumptions by type-checker.*)

schematic_goal "g : ?Tg \<Longrightarrow> ?y1 : ?Ty1 \<Longrightarrow> ?y2 : ?Ty2 \<Longrightarrow> x : ?Tx \<Longrightarrow> xs : ?Txs
  \<Longrightarrow> g (vcons ?y1 ?y2 x xs) : ?T"
  apply (rule app_type[where ?t=g])
    apply assumption
    apply (rule app_dep_type[where ?t="vcons y1 y2 x" for y1 y2])
      apply (rule app_dep_type[where ?t="vcons y1 y2" for y1 y2])
        apply (rule app_dep_type[where ?t="vcons y1" for y1])
          apply (rule app_dep_type[where ?t="vcons"])
            apply (rule vcons_type)
            apply (rule Any_typeI)
          apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
        apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
      apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
   done

end

experiment
  fixes Id
  and refl
  and J
  assumes Id_type: "Id : (A : U) \<Rightarrow> A \<Rightarrow> A \<Rightarrow> U"
  and refl_type: "refl: (A : U) \<Rightarrow> (x: A) \<Rightarrow> Id A x x"
  and J_type: "J: (A : U) \<Rightarrow> (C: (x: A) \<Rightarrow> (y: A) \<Rightarrow>
    (p: Id A x y) \<Rightarrow> U) \<Rightarrow> ((x: A) \<Rightarrow> C x x (refl A x)) \<Rightarrow> (a: A) \<Rightarrow> (b: A)
    \<Rightarrow> (p: Id A a b) \<Rightarrow> C a b p"
begin

text \<open>The proof term for reflexivity of equality:\<close>

schematic_goal
  "?A1 : ?TA1 \<Longrightarrow> ?C1 : ?TC1 \<Longrightarrow> ?A2 : ?TA2 \<Longrightarrow> a : ?Ta \<Longrightarrow> b : ?Tb \<Longrightarrow>
    p : ?Tp \<Longrightarrow> J ?A1 ?C1 (refl ?A2) a b p : ?T"
  apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x) a b" for A1 C1 A2])
    apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x) a" for A1 C1 A2])
      apply (rule app_dep_type[where ?t="J A1 C1 (\<lambda>x. refl A2 x)" for A1 C1 A2])
        apply (rule app_dep_type[where ?t="J A1 C1" for A1 C1])
          apply (rule app_dep_type[where ?t="J A1" for A1])
            apply (rule app_dep_type[where ?t="J"])
              apply (rule J_type)
              apply assumption
            apply (tactic \<open>rotate_tac 1 1\<close>, assumption)
          apply (rule Dep_fun_typeI)
          apply (rule app_dep_type[where ?t="refl A2" for A2])
            apply (rule app_dep_type[where ?t="refl"])
              apply (rule refl_type)
              apply (tactic \<open>rotate_tac 2 1\<close>, assumption)
            apply (tactic \<open>rotate_tac 7 1\<close>, assumption)
          apply (tactic \<open>rotate_tac 3 1\<close>, assumption)
        apply (tactic \<open>rotate_tac 4 1\<close>, assumption)
      apply (tactic \<open>rotate_tac 5 1\<close>, assumption)
  done

end


(*
Notes:
1. Priority of rules
2. Priority of assumptions
3. Specification of unification algorithm for rules?
4. Postponing zero-priority rules (e.g. subtype conditions, additional assumptions)
*)

end