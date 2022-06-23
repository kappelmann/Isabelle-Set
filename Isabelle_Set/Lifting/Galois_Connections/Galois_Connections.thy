section \<open>Galois Connections\<close>
theory Galois_Connections
  imports LBinary_Relations
begin

text\<open>A \<^emph>\<open>Galois connection\<close> between two relations @{term "L"} and @{term "R"}
consists of two monotone functions @{term "l"} and @{term "r"} such that
@{term "L x (r y) \<longleftrightarrow> R (l x) y"}. We call this the \<^emph>\<open>Galois property\<close>.
@{term "l"} is called the \<^emph>\<open>left adjoint\<close> and @{term "r"} the \<^emph>\<open>right adjoint\<close>.
We call @{term "L"} the \<^emph>\<open>left relation\<close> and @{term "R"} the \<^emph>\<open>right relation\<close>.\<close>

consts galois_property_on :: "'a \<Rightarrow> 'b \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
  ('e \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'e) \<Rightarrow> ('f \<Rightarrow> 'd) \<Rightarrow> bool"

overloading
  galois_property_on_pred \<equiv> "galois_property_on ::
    ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool"
begin
  definition "galois_property_on_pred Pl Pr L R l r \<equiv>
    \<forall>x y. Pl x \<longrightarrow> Pr y \<longrightarrow> L x (r y) \<longleftrightarrow> R (l x) y"
end

lemma galois_property_onI:
  assumes "\<And>x y. Pl x \<Longrightarrow> Pr y \<Longrightarrow> L x (r y) \<longleftrightarrow> R (l x) y"
  shows "galois_property_on Pl Pr L R l r"
  unfolding galois_property_on_pred_def using assms by simp

lemma galois_property_on_left_rel_right_iff_right_rel_left:
  assumes "galois_property_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  shows "L x (r y) \<longleftrightarrow> R (l x) y"
  using assms unfolding galois_property_on_pred_def by simp

lemma galois_property_on_right_rel_left_if_left_rel_right:
  assumes "galois_property_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  and "L x (r y)"
  shows "R (l x) y"
  using assms galois_property_on_left_rel_right_iff_right_rel_left by fastforce

lemma galois_property_on_left_rel_right_if_right_rel_left:
  assumes "galois_property_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  and "R (l x) y"
  shows "L x (r y)"
  using assms galois_property_on_left_rel_right_iff_right_rel_left by fastforce

lemma galois_property_on_dual:
  fixes Pl :: "'a \<Rightarrow> bool" and Pr :: "'b \<Rightarrow> bool"
  and L :: "'a \<Rightarrow> _" and R :: "_ \<Rightarrow> 'b \<Rightarrow> _"
  assumes "galois_property_on Pl Pr L R l r"
  shows "galois_property_on Pr Pl (rel_inv R) (rel_inv L) r l"
  using assms by (intro galois_property_onI) (auto
    dest: galois_property_on_left_rel_right_iff_right_rel_left
    simp: rel_inv_iff_rel)

lemma galois_property_on_compI:
  assumes galois1: "galois_property_on Pl1 Pr1 L1 R1 l1 r1"
  and galois2: "galois_property_on Pl2 Pr2 L2 R2 l2 r2"
  and has_fun_type_l1: "has_fun_type Pl1 Pl2 l1"
  and has_fun_type_r2: "has_fun_type Pr2 Pr1 r2"
  and agree: "\<And>x y. R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  shows "galois_property_on Pl1 Pr2 L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
proof (rule galois_property_onI)
  fix x y assume "Pl1 x" "Pr2 y"
  with has_fun_type_r2 has_fun_type_l1 have "Pl2 (l1 x)" "Pr1 (r2 y)"
    by (blast dest: has_fun_typeD)+
  have "L1 x ((r1 \<circ> r2) y) \<longleftrightarrow> L1 x (r1 (r2 y))" by simp
  also from galois1 \<open>Pl1 x\<close> \<open>Pr1 (r2 y)\<close> have "... \<longleftrightarrow> R1 (l1 x) (r2 y)"
    by (rule galois_property_on_left_rel_right_iff_right_rel_left)
  also from agree have "... \<longleftrightarrow> L2 (l1 x) (r2 y)" by simp
  also from galois2 \<open>Pl2 (l1 x)\<close> \<open>Pr2 y\<close> have "... \<longleftrightarrow> R2 (l2 (l1 x)) y"
    by (simp only: galois_property_on_left_rel_right_iff_right_rel_left)
  also have "... \<longleftrightarrow> R2 ((l2 \<circ> l1) x) y" by simp
  finally show "L1 x ((r1 \<circ> r2) y) \<longleftrightarrow> R2 ((l2 \<circ> l1) x) y" .
qed

definition "galois_property (L :: 'a \<Rightarrow> _) (R :: _ \<Rightarrow> 'b \<Rightarrow> _) l r \<equiv>
  galois_property_on (\<lambda>x :: 'a. True) (\<lambda>x :: 'b. True) L R l r"

lemma galois_property_eq_galois_property_on:
  "galois_property (L :: 'a \<Rightarrow> _) (R :: _ \<Rightarrow> 'b \<Rightarrow> _) l r
    = galois_property_on (\<lambda>x :: 'a. True) (\<lambda>x :: 'b. True) L R l r"
  unfolding galois_property_def ..

lemma galois_propertyI:
  assumes "\<And>x y. L x (r y) \<longleftrightarrow> R (l x) y"
  shows "galois_property L R l r"
  unfolding galois_property_eq_galois_property_on using assms
  by (intro galois_property_onI)

lemma galois_property_left_rel_right_iff_right_rel_left:
  assumes "galois_property L R l r"
  shows "L x (r y) \<longleftrightarrow> R (l x) y"
  using assms unfolding galois_property_eq_galois_property_on
  by (rule galois_property_on_left_rel_right_iff_right_rel_left) simp_all

lemma galois_property_right_rel_left_if_left_rel_right:
  assumes "galois_property L R l r"
  and "L x (r y)"
  shows "R (l x) y"
  using assms galois_property_left_rel_right_iff_right_rel_left by fastforce

lemma galois_property_left_rel_right_if_right_rel_left:
  assumes "galois_property L R l r"
  and "R (l x) y"
  shows "L x (r y)"
  using assms galois_property_left_rel_right_iff_right_rel_left by fastforce

lemma galois_property_dual:
  assumes "galois_property L R l r"
  shows "galois_property (rel_inv R) (rel_inv L) r l"
  using assms unfolding galois_property_eq_galois_property_on
  by (intro galois_property_on_dual)

lemma galois_property_compI:
  assumes galois1: "galois_property L1 R1 l1 r1"
  and galois2: "galois_property L2 R2 l2 r2"
  and agree: "\<And>x y. R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  shows "galois_property L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms unfolding galois_property_eq_galois_property_on
  by (intro galois_property_on_compI has_fun_typeI)

definition "galois_connection_on
  (Pl :: 'a \<Rightarrow> bool) (Pr :: 'b \<Rightarrow> bool) (L :: 'a \<Rightarrow> _) (R :: _ \<Rightarrow> 'b \<Rightarrow> _) l r \<equiv>
  monotone L R l \<and> monotone R L r \<and> galois_property_on Pl Pr L R l r"

lemma galois_connection_onI:
  assumes "monotone L R l" "monotone R L r"
  and "galois_property_on Pl Pr L R l r"
  shows "galois_connection_on Pl Pr L R l r"
  unfolding galois_connection_on_def using assms by blast

lemma galois_connection_on_monotone_left:
  assumes "galois_connection_on Pl Pr L R l r"
  shows "monotone L R l"
  using assms unfolding galois_connection_on_def by blast

lemma galois_connection_on_monotone_right:
  assumes "galois_connection_on Pl Pr L R l r"
  shows "monotone R L r"
  using assms unfolding galois_connection_on_def by blast

lemma galois_property_on_if_galois_connection_on:
  assumes "galois_connection_on Pl Pr L R l r"
  shows "galois_property_on Pl Pr L R l r"
  using assms unfolding galois_connection_on_def by blast

lemma galois_connection_on_left_rel_right_iff_right_rel_left:
  assumes "galois_connection_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  shows "L x (r y) \<longleftrightarrow> R (l x) y"
  by (fact galois_property_on_left_rel_right_iff_right_rel_left
    [OF galois_property_on_if_galois_connection_on, OF assms])

lemma galois_connection_on_right_rel_left_left_if_left_rel:
  assumes "galois_connection_on Pl Pr L R l r"
  and "L x x'"
  shows "R (l x) (l x')"
  using assms by (force intro: dep_monotoneD dest: galois_connection_on_monotone_left)

lemma galois_connection_on_left_rel_right_right_if_right_rel:
  assumes "galois_connection_on Pl Pr L R l r"
  and "R y y'"
  shows "L (r y) (r y')"
  using assms by (force intro: dep_monotoneD dest: galois_connection_on_monotone_right)

lemma galois_connection_on_right_rel_left_if_left_rel_right:
  assumes "galois_connection_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  and "L x (r y)"
  shows "R (l x) y"
  using assms galois_connection_on_left_rel_right_iff_right_rel_left by fastforce

lemma galois_connection_on_left_rel_right_if_right_rel_left:
  assumes "galois_connection_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  and "R (l x) y"
  shows "L x (r y)"
  using assms galois_connection_on_left_rel_right_iff_right_rel_left by fastforce

lemma galois_connection_on_left_rel_right_left_if_left_rel:
  assumes galois: "galois_connection_on Pl Pr L R l r"
  and PlPr: "Pl x" "Pr (l x')"
  and Lxx': "L x x'"
  shows "L x (r (l x'))"
proof -
  from galois Lxx' have "R (l x) (l x')"
    by (rule galois_connection_on_right_rel_left_left_if_left_rel)
  with galois PlPr show "L x (r (l x'))"
    by (rule galois_connection_on_left_rel_right_if_right_rel_left)
qed

lemma galois_connection_on_right_rel_left_right_if_right_rel:
  assumes galois: "galois_connection_on Pl Pr L R l r"
  and PlPr: "Pl (r y)" "Pr y'"
  and Ryy': "R y y'"
  shows "R (l (r y)) y'"
proof -
  from galois Ryy' have "L (r y) (r y')"
    by (rule galois_connection_on_left_rel_right_right_if_right_rel)
  with galois PlPr show "R (l (r y)) y'"
    by (rule galois_connection_on_right_rel_left_if_left_rel_right)
qed

lemma galois_connection_on_dual:
  assumes "galois_connection_on Pl Pr L R l r"
  shows "galois_connection_on Pr Pl (rel_inv R) (rel_inv L) r l"
  using assms by (intro galois_connection_onI) (auto
    intro: monotone_rel_inv_if_monotone galois_connection_on_monotone_left
      galois_connection_on_monotone_right galois_property_on_dual
    simp only: rel_inv_iff_rel galois_property_on_if_galois_connection_on)

lemma galois_property_on_galois_connection_on_compI:
  assumes "galois_property_on Pl1 Pr1 L1 R1 l1 r1"
  and "galois_property_on Pl2 Pr2 L2 R2 l2 r2"
  and "has_fun_type Pl1 Pl2 l1"
  and "has_fun_type Pr2 Pr1 r2"
  and "\<And>x y. R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and "monotone L1 R2 (l2 \<circ> l1)"
  and "monotone R2 L1 (r1 \<circ> r2)"
  shows "galois_connection_on Pl1 Pr2 L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  by (intro galois_connection_onI galois_property_on_compI) fact+

lemma galois_connection_on_compI:
  assumes galois1: "galois_connection_on Pl1 Pr1 L1 R1 l1 r1"
  and galois2: "galois_connection_on Pl2 Pr2 L2 R2 l2 r2"
  and "has_fun_type Pl1 Pl2 l1"
  and "has_fun_type Pr2 Pr1 r2"
  and "\<And>x y. R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and R1_l1_finer: "\<And>x x'. R1 (l1 x) (l1 x') \<Longrightarrow> L2 (l1 x) (l1 x')"
  and L2_r2_finer: "\<And>z z'. L2 (r2 z) (r2 z') \<Longrightarrow> R1 (r2 z) (r2 z')"
  shows "galois_connection_on Pl1 Pr2 L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
proof (rule galois_property_on_galois_connection_on_compI[where ?Pr1.0=Pr1 and ?Pl2.0=Pl2])
  from galois1 galois2 R1_l1_finer show "monotone L1 R2 (l2 \<circ> l1)"
    by (intro monotone_compI galois_connection_on_monotone_left)
  from galois1 galois2 L2_r2_finer show "monotone R2 L1 (r1 \<circ> r2)"
    by (intro monotone_compI galois_connection_on_monotone_right)
qed (intro galois_property_on_if_galois_connection_on | fact)+

lemma galois_connection_on_compI':
  assumes "galois_connection_on Pl1 Pr1 L1 R1 l1 r1"
  and "galois_connection_on Pr1 Pr2 R1 R2 l2 r2"
  and "has_fun_type Pl1 Pr1 l1"
  and "has_fun_type Pr2 Pr1 r2"
  shows "galois_connection_on Pl1 Pr2 L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms by (rule galois_connection_on_compI) simp_all

lemma galois_connection_on_Dep_Fun_RelI:
  assumes galois1: "galois_connection_on Pl1 Pr1 L1 R1 l1 r1"
  (* and galois2: "\<And>x y. L1 x (r1 y) \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 x y) (R2 x y) (l2 y x) (r2 x y)" *)
  and galois2: "\<And>x y. L1 x y \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 x y) (R2 x y) (l2 (l1 y) x) (r2 x (l1 y))"
  (* and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) (abs2 y x) (rep2 x y)" *)
  (* note swapped order of arguments for abs2 *)
  (* and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  and rep2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_abs (T2 x y) \<Rrightarrow> Eq_rep (T2 x y)) (rep2 x y) (rep2 x' y')"
  and abs2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_rep (T2 x y) \<Rrightarrow> Eq_abs (T2 x y)) (abs2 y x) (abs2 y' x')" *)
    (* shows "True" *)
  shows "galois_connection_on P P'
    ([x1 x2 \<Colon> L1] \<Rrightarrow> L2 x1 x2) ([y1 y2 \<Colon> R1] \<Rrightarrow> R2 (r1 y1) (r1 y2))
    (dep_map_fun r1 l2) (dep_map_fun l1 r2)"
    (is "galois_connection_on ?Pl ?Pr ?L ?R ?l ?r")
proof (rule galois_connection_onI)
  show "monotone ?L ?R ?l"
  proof (intro dep_monotoneI Dep_Fun_RelI)
    fix f1 f2 y1 y2
    assume "R1 y1 y2"
    with galois1 have "L1 (r1 y1) (r1 y2)"
      by (rule galois_connection_on_left_rel_right_right_if_right_rel)
    moreover assume "?L f1 f2"
    ultimately have "L2 (r1 y1) (r1 y2) (f1 (r1 y1)) (f2 (r1 y2))"
      by (blast dest: Dep_Fun_RelD)
    (* ultimately have "L2 (r1 y1) (r1 y2) (f1 (r1 y1)) (f2 (r1 y2))"
      by (blast dest: Dep_Fun_RelD) *)
    with galois2 have
      "R2 (r1 y1) (r1 y2) (l2 (l1 (r1 y2)) (r1 y1) (f1 (r1 y1))) (l2 (l1 (r1 y2)) (r1 y1) (f2 (r1 y2)))"
      (* sorry *)
      by (rule galois_connection_on_right_rel_left_left_if_left_rel) fact
    have
      "R2 (r1 y1) (r1 y2) (l2 y1           (r1 y1) (f1 (r1 y1))) (l2 y2           (r1 y2) (f2 (r1 y2)))"
        sorry
      (* by (rule galois_connection_on_right_rel_left_left_if_left_rel) *)
    then show "R2 (r1 y1) (r1 y2) (?l f1 y1) (?l f2 y2)" unfolding dep_map_fun_def .
    (* show "R2 y1 y2 (?l f1 y1) (?l f2 y2)" *)
    (* f g h x \<equiv> l2 x (r1 x) (f (r1 x)) *)
  qed
qed



definition "galois_connection L R l r \<equiv>
  galois_connection_on (\<lambda>x. True) (\<lambda>x. True) L R l r"

lemma galois_connection_eq_galois_connection_on:
  "galois_connection L R l r = galois_connection_on (\<lambda>x. True) (\<lambda>x. True) L R l r"
  unfolding galois_connection_def ..

lemma galois_connectionI:
  assumes "monotone L R l" "monotone R L r"
  and "galois_property L R l r"
  shows "galois_connection L R l r"
  using assms
  unfolding galois_connection_eq_galois_connection_on galois_property_eq_galois_property_on
  by (intro galois_connection_onI)

lemma galois_connection_monotone_left:
  assumes "galois_connection L R l r"
  shows "monotone L R l"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (rule galois_connection_on_monotone_left)

lemma galois_connection_monotone_right:
  assumes "galois_connection L R l r"
  shows "monotone R L r"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (rule galois_connection_on_monotone_right)

lemma galois_property_if_galois_connection_on:
  assumes "galois_connection L R l r"
  shows "galois_property L R l r"
  using assms
  unfolding galois_connection_eq_galois_connection_on galois_property_eq_galois_property_on
  by (intro galois_property_on_if_galois_connection_on)

lemma galois_connection_left_rel_right_iff_right_rel_left:
  assumes "galois_connection L R l r"
  shows "L x (r y) \<longleftrightarrow> R (l x) y"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (rule galois_connection_on_left_rel_right_iff_right_rel_left) simp_all

lemma galois_connection_right_rel_left_left_if_left_rel:
  assumes "galois_connection L R l r"
  and "L x x'"
  shows "R (l x) (l x')"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (rule galois_connection_on_right_rel_left_left_if_left_rel)

lemma galois_connection_left_rel_right_right_if_right_rel:
  assumes "galois_connection_on Pl Pr L R l r"
  and "R y y'"
  shows "L (r y) (r y')"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (rule galois_connection_on_left_rel_right_right_if_right_rel)

lemma galois_connection_right_rel_left_if_left_rel_right:
  assumes "galois_connection L R l r"
  and "L x (r y)"
  shows "R (l x) y"
  using assms galois_connection_left_rel_right_iff_right_rel_left by fastforce

lemma galois_connection_left_rel_right_if_right_rel_left:
  assumes "galois_connection L R l r"
  and "R (l x) y"
  shows "L x (r y)"
  using assms galois_connection_left_rel_right_iff_right_rel_left by fastforce

lemma galois_connection_left_rel_right_left_if_left_rel:
  assumes galois: "galois_connection L R l r"
  and Lxx': "L x x'"
  shows "L x (r (l x'))"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (blast intro: galois_connection_on_left_rel_right_left_if_left_rel)

lemma galois_connection_right_rel_left_right_if_right_rel:
  assumes galois: "galois_connection L R l r"
  and Ryy': "R y y'"
  shows "R (l (r y)) y'"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (blast intro: galois_connection_on_right_rel_left_right_if_right_rel)

lemma galois_connection_dual:
  assumes "galois_connection L R l r"
  shows "galois_connection (rel_inv R) (rel_inv L) r l"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (rule galois_connection_on_dual)

lemma galois_property_galois_connection_compI:
  assumes "galois_property L1 R1 l1 r1"
  and "galois_property L2 R2 l2 r2"
  and "\<And>x y. R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and "monotone L1 R2 (l2 \<circ> l1)"
  and "monotone R2 L1 (r1 \<circ> r2)"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms
  unfolding galois_connection_eq_galois_connection_on galois_property_eq_galois_property_on
  by (intro galois_property_on_galois_connection_on_compI has_fun_typeI)

lemma galois_connection_compI:
  assumes galois1: "galois_connection L1 R1 l1 r1"
  and galois2: "galois_connection L2 R2 l2 r2"
  and "\<And>x y. R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and R1_l1_finer: "\<And>x x'. R1 (l1 x) (l1 x') \<Longrightarrow> L2 (l1 x) (l1 x')"
  and L2_r2_finer: "\<And>z z'. L2 (r2 z) (r2 z') \<Longrightarrow> R1 (r2 z) (r2 z')"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (intro galois_connection_on_compI has_fun_typeI)

lemma galois_connection_compI':
  assumes "galois_connection L1 R1 l1 r1"
  and "galois_connection R1 R2 l2 r2"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms unfolding galois_connection_eq_galois_connection_on
  by (intro galois_connection_on_compI' has_fun_typeI)


subsection \<open>Instantiations\<close>

lemma galois_property_eq_id: "galois_property (=) (=) id id"
  by (rule galois_propertyI) simp

lemma galois_connection_eq_id: "galois_connection (=) (=) id id"
  by (intro galois_connectionI galois_property_eq_id monotone_self_id)


end