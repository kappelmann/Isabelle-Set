theory Spines_Tests
  imports Manual_Type_Checks
begin

definition "spine_app f t \<equiv> t"
notation spine_app (infixr ";" 99)

definition "pannot P1 P2 \<equiv> P2 \<longrightarrow> P1"
notation pannot (infix ":p" 50)

(* declare[[show_types]] *)
lemma spine_app_type:
  assumes "f : F"
  and "(t : T) :p (f : F)"
  shows "f;t : T"
  using assms unfolding spine_app_def pannot_def by simp

lemma spine_app_pannot_type:
  assumes "x : A"
  and "(t : T) :p (f x : B x)"
  shows "(x;t : T) :p (f : (x : A) \<Rightarrow> B x)"
  using assms unfolding spine_app_def pannot_def by simp

lemma pannot_solve:
  shows "(t : T) :p (t : T)"
  unfolding pannot_def by simp

definition "type_spine t P T \<equiv> P \<longrightarrow> t : T"
notation type_spine ("_ :s _ >> _" [50,50,50] 50)

lemma spine_app_type':
  assumes "f : F"
  and "t :s (f : F) >> T"
  shows "f;t : T"
  using assms unfolding spine_app_def type_spine_def by simp

lemma spine_app_type_spine_type:
  assumes "x : A"
  and "t :s (f x : B x) >> T"
  shows "x;t :s (f : Dep_fun_type A B) >> T"
  using assms unfolding spine_app_def type_spine_def by simp

lemma type_spine_solve:
  shows "t :s (t : T) >> T"
  unfolding type_spine_def by simp

lemma spine_app_Dep_Fun_type':
  assumes "\<And>x. x : A \<Longrightarrow> f x; t x : B x"
  shows "f;t : (x : A) \<Rightarrow> B x"
  using assms unfolding spine_app_def type_spine_def Dep_fun_typeI by simp


experiment
begin

lemma
  assumes n_type: "n : Nat" and i_type: "i : Nat"
  shows "(add :: 'a \<Rightarrow> 'a \<Rightarrow> 'a);n;i;((add :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) n i) : Nat"
  apply (rule spine_app_type)
    apply (rule add_type)
    apply (rule spine_app_pannot_type)
      apply (rule n_type)
      apply (rule spine_app_pannot_type)
        apply (rule i_type)
        apply (rule pannot_solve)
  done

lemma
  assumes n_type: "n : Nat" and i_type: "i : Nat"
  shows "(add :: 'a \<Rightarrow> 'a \<Rightarrow> 'a);n;i;((add :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) n i) : Nat"
  apply (rule spine_app_type')
    apply (rule add_type)
    apply (rule spine_app_type_spine_type)
      apply (rule n_type)
      apply (rule spine_app_type_spine_type)
        apply (rule i_type)
        apply (rule type_spine_solve)
  done

lemma
  nat_rec_type':
    "nat_rec : A 0 \<Rightarrow> ((n : Element nat) \<Rightarrow> A n \<Rightarrow> A (succ n)) \<Rightarrow> (n : Element nat) \<Rightarrow> A n"
  and zero_type': "0 : Element nat"
  sorry

schematic_goal "?T1 : ?TT1 \<Longrightarrow> ?T2 : ?TT2 \<Longrightarrow> ?n : ?Tn \<Longrightarrow>
  (nat_rec :: 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a);
  ((vnil :: 'a \<Rightarrow> _);?T1;
   (vnil :: 'a \<Rightarrow> _) ?T1);
  ((\<lambda>(n :: 'a) (v :: 'a).
    (vcons;(?T2;n;v;?T2 n v);(?n;n;v;?n n v);n;v));
   (\<lambda>(n :: 'a) (v :: 'a).
    vcons (?T2 n v) (?n n v) n v));
  0;
  (nat_rec :: 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a)
    (vnil ?T1)
    (\<lambda>n v. vcons (?T2 n v) (?n n v) n v) 0 : Element (vec nat 0)"
  apply (rule spine_app_type')
    apply (rule nat_rec_type')
    apply (rule spine_app_type_spine_type)
      apply (rule spine_app_type')
        apply (rule vnil_type)
        apply (rule spine_app_type_spine_type)
          apply (rule Any_typeI)
          apply (rule type_spine_solve)
      apply (rule spine_app_type_spine_type)
        apply (rule spine_app_Dep_Fun_type')
        apply (rule spine_app_Dep_Fun_type')
        apply (rule spine_app_type')
          apply (rule spine_app_type')

        (* apply (rule Dep_fun_typeI)
        apply (rule Dep_fun_typeI) *)
      (* apply (rule spine_app_type')
      apply (rule spine_app_type_spine_type) *)




end

end