subsection \<open>Lifting With Galois Connections\<close>
theory Lifting_Galois_Connections
  imports
    Galois_Connections
    Lifting_Relations_New
begin

consts Galois_Rel_on :: "'a \<Rightarrow> 'b \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'd) \<Rightarrow> 'c \<Rightarrow> 'e \<Rightarrow> bool"

overloading
  Galois_Rel_on_pred \<equiv> "Galois_Rel_on ::
    ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
  definition Galois_Rel_on_pred ::
    "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
    where "Galois_Rel_on_pred Pl Pr L r x y \<equiv> Pl x \<and> Pr y \<and> L x (r y)"
end

lemma Galois_Rel_onI:
  assumes "Pl x" "Pr y"
  and "L x (r y)"
  shows "(Galois_Rel_on Pl Pr L r) x y"
  unfolding Galois_Rel_on_pred_def using assms by blast

context
  fixes Pl :: "'a \<Rightarrow> bool" and Pr :: "'b \<Rightarrow> bool"
  and L :: "'a \<Rightarrow> 'c \<Rightarrow> bool" and r :: "'b \<Rightarrow> 'c"
begin

lemma Galois_Rel_onE:
  assumes "(Galois_Rel_on Pl Pr L r) x y"
  obtains "Pl x" "Pr y" "L x (r y)"
  using assms unfolding Galois_Rel_on_pred_def by blast

lemma Galois_Rel_on_Pl:
  assumes "(Galois_Rel_on Pl Pr L r) x y"
  shows "Pl x"
  using assms by (elim Galois_Rel_onE)

lemma Galois_Rel_on_Pr:
  assumes "(Galois_Rel_on Pl Pr L r) x y"
  shows "Pr y"
  using assms by (elim Galois_Rel_onE)

lemma Galois_Rel_on_left_rel_right:
  assumes "(Galois_Rel_on Pl Pr L r) x y"
  shows "L x (r y)"
  using assms by (elim Galois_Rel_onE)

corollary Galois_Rel_on_iff_left_rel_right:
  "(Galois_Rel_on Pl Pr L r) x y \<longleftrightarrow> Pl x \<and> Pr y \<and> L x (r y)"
  by (blast elim: Galois_Rel_onE intro: Galois_Rel_onI)

lemma galois_property_on_right_rel_left_if_Galois_Rel_on:
  assumes "galois_property_on Pl Pr L R l r"
  and "(Galois_Rel_on Pl Pr L r) x y"
  shows "R (l x) y"
  using assms
  by (blast intro: galois_property_on_right_rel_left_if_left_rel_right elim: Galois_Rel_onE)

lemma galois_property_on_Galois_Rel_onE:
  assumes "galois_property_on Pl Pr L R l r"
  and "(Galois_Rel_on Pl Pr L r) x y"
  obtains "Pl x" "Pr y" "L x (r y)" "R (l x) y"
  using assms
  by (blast dest: galois_property_on_right_rel_left_if_Galois_Rel_on elim: Galois_Rel_onE)

lemma galois_property_on_Galois_Rel_on_if_right_rel_left:
  assumes "galois_property_on Pl Pr L R l r"
  and "Pl x" "Pr y"
  and "R (l x) y"
  shows "(Galois_Rel_on Pl Pr L r) x y"
  using assms
  by (intro Galois_Rel_onI) (blast intro: Galois_Rel_onI galois_property_on_left_rel_right_if_right_rel_left)+

corollary galois_property_on_Galois_Rel_on_iff_right_rel_left:
  assumes "galois_property_on Pl Pr L R l r"
  shows "(Galois_Rel_on Pl Pr L r) x y \<longleftrightarrow> Pl x \<and> Pr y \<and> R (l x) y"
  using assms
  by (blast intro: galois_property_on_Galois_Rel_on_if_right_rel_left
    elim: galois_property_on_Galois_Rel_onE)

end

lemma galois_property_on_rel_inv_Galois_Rel_on_on_rel_inv_eq:
  fixes Pl :: "'a \<Rightarrow> bool" and Pr :: "'b \<Rightarrow> bool"
  and L :: "'a \<Rightarrow> 'c \<Rightarrow> bool" and r :: "'b \<Rightarrow> 'c"
  assumes "galois_property_on Pl Pr L R l r"
  shows "rel_inv (Galois_Rel_on Pr Pl (rel_inv R) l) = Galois_Rel_on Pl Pr L r"
proof (intro ext)
  fix x y
  have "rel_inv (Galois_Rel_on Pr Pl (rel_inv R) l) x y \<longleftrightarrow> (Galois_Rel_on Pr Pl (rel_inv R) l) y x"
    by (simp only: rel_inv_iff_rel)
  also have "... \<longleftrightarrow> Pr y \<and> Pl x \<and> (rel_inv R) y (l x)" by (fact Galois_Rel_on_iff_left_rel_right)
  also have "... \<longleftrightarrow> Pr y \<and> Pl x \<and> R (l x) y" by (simp only: rel_inv_iff_rel)
  also from assms have "... \<longleftrightarrow> Pl x \<and> Pr y \<and> L x (r y)"
    by (fastforce iff: galois_property_on_left_rel_right_iff_right_rel_left)
  also have "... \<longleftrightarrow> (Galois_Rel_on Pl Pr L r) x y" by (fact Galois_Rel_on_iff_left_rel_right[symmetric])
  finally show "rel_inv (Galois_Rel_on Pr Pl (rel_inv R) l) x y \<longleftrightarrow> Galois_Rel_on Pl Pr L r x y" .
qed

lemma galois_connection_on_Galois_Rel_on_left_if_left_rel:
  assumes "galois_connection_on Pl Pr L R l r"
  and "Pl x" "Pr (l x')"
  and "L x x'"
  shows "(Galois_Rel_on Pl Pr L r) x (l x')"
  using assms
  by (blast intro: Galois_Rel_onI galois_connection_on_left_rel_right_left_if_left_rel)

lemma galois_connection_on_Galois_Rel_on_right_if_right_rel:
  assumes "galois_connection_on Pl Pr L R l r"
  and "Pl (r y)" "Pr y'"
  and "R y y'"
  shows "(Galois_Rel_on Pl Pr L r) (r y) y'"
  using assms
  by (blast intro: Galois_Rel_onI galois_connection_on_left_rel_right_right_if_right_rel)

lemma galois_connection_on_Dep_Fun_RelI:
  assumes galois1: "galois_connection_on Pl1 Pr1 L1 R1 l1 r1"
  and galois2: "\<And>x y. (Galois_Rel_on Pl1 Pr1 L1 r1) x y \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 x y) (R2 x y) (l2 y x) (r2 x y)"
  (* and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) (abs2 y x) (rep2 x y)" *)
  (* note swapped order of arguments for abs2 *)
  (* and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  and rep2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_abs (T2 x y) \<Rrightarrow> Eq_rep (T2 x y)) (rep2 x y) (rep2 x' y')"
  and abs2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_rep (T2 x y) \<Rrightarrow> Eq_abs (T2 x y)) (abs2 y x) (abs2 y' x')" *)
    (* shows "True" *)
  shows "galois_connection_on P P'
    ([x1 x2 \<Colon> L1] \<Rrightarrow> L2 x1 (l1 x2)) ([y1 y2 \<Colon> R1] \<Rrightarrow> R2 (r1 y1) y2)
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
    ultimately have "L2 (r1 y1) (l1 (r1 y2)) (f1 (r1 y1)) (f2 (r1 y2))"
      by (blast dest: Dep_Fun_RelD)
    have "Pl1 (r1 y1)" "Pr1 y2" sorry
    from galois1 this \<open>R1 y1 y2\<close> have "R1 (l1 (r1 y1)) y2"
      by (rule galois_connection_on_right_rel_left_right_if_right_rel)
    with galois1 have "(Galois_Rel_on Pl1 Pr2 L1 r1) (r1 y1) y2"
      sorry
      (* by (rule galois_property_on_Galois_Rel_on_if_right_rel_left) *)
    (* ultimately have "L2 (r1 y1) y2 (f1 (r1 y1)) (f2 (r1 y2))"
      by (blast dest: Dep_Fun_RelD) *)
    (* (Galois_Rel L1 r1) (r1 y1)*)
(* "(Galois_Rel L1 r1) (r1 y1) (l1 (r1 y2)) \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 (r1 y1) (l1 (r1 y2))) (R2 (r1 y1) (l1 (r1 y2)))
      (l2 (l1 (r1 y2)) (r1 y1)) (r2 (r1 y1) (l1 (r1 y2)))" *)
(* "(Galois_Rel L1 r1) (r1 y1) y2 \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 (r1 y1) y2) (R2 (r1 y1) y2) (l2 y2 (r1 y1)) (r2 (r1 y1) y2)" *)
(* "(Galois_Rel L1 r1) (r1 y1) y1 \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 (r1 y1) y1) (R2 (r1 y1) y1) (l2 y1 (r1 y1)) (r2 (r1 y1) y1)" *)
(* "(Galois_Rel L1 r1) (r1 y1) y2 \<Longrightarrow>
    galois_connection_on Pl2 Pr2 (L2 (r1 y1) y2 (R2 (r1 y1) y2 (l2 y2 (r1 y1)) (r2 (r1 y1) y2" *)
    with galois2 have
      "R2 (r1 y1) (l1 (r1 y2)) (l2 (l1 (r1 y2)) (r1 y1) (f1 (r1 y1))) (l2 (l1 (r1 y2)) (r1 y1) (f2 (r1 y2)))"
      sorry
    have
      "R2 (r1 y1) y2           (l2 y1           (r1 y1) (f1 (r1 y1))) (l2 y2           (r1 y2) (f2 (r1 y2)))"
        sorry
      (* by (rule galois_connection_on_right_rel_left_left_if_left_rel) *)
    then show "R2 (r1 y1) y2 (?l f1 y1) (?l f2 y2)" unfolding dep_map_fun_def .
    (* show "R2 y1 y2 (?l f1 y1) (?l f2 y2)" *)
    (* f g h x \<equiv> l2 x (r1 x) (f (r1 x)) *)
  qed
qed


lemma galois_property:
  fixes Pl :: "'a \<Rightarrow> bool" and Pr :: "'b \<Rightarrow> bool" and l :: "'a \<Rightarrow> 'b"
  assumes bij: "bijection_on Pl Pr l r"
  shows "galois_property (Eq_Rel\<restriction>Pl) (Eq_Rel\<restriction>Pr) l r"
proof (rule galois_propertyI)
  fix x y
  have "(Eq_Rel\<restriction>Pl) x (r y) \<longleftrightarrow> Pl x \<and> x = r y"
    by (intro iffI) (blast intro: restrictI Eq_RelI elim: restrictE Eq_RelE)+
  also have "... \<longleftrightarrow> Pr (l x) \<and> l x = y"
  proof (intro iffI conjI)
    presume "Pl x"
    with bij show "Pr (l x)" by (elim bijection_on_prop_right)
    presume "x = r y"
    (* x = r l x
    l r y = y
      x = r l r y
    l x = l r l x *)
    (* l x = y *)

    then have "l x = l (r y)" by (rule arg_cong)
    (* Pl x \<and> x = r y *)
  qed
 (* (auto intro: bijection_on_prop_right app_app_eq_self_if_bijection_on'[symmetric]) *)
  (* thm app_app_eq_self_if_bijection_on'[symmetric] *)
    (* (auto intro: bijection_on_prop_right bijection_on_prop_left *)
      (* simp: app_app_eq_self_if_bijection_on app_app_eq_self_if_bijection_on) *)
    (* by (intro iffI) (blast intro: restrictI Eq_RelI elim: restrictE Eq_RelE)+ *)
  (* finally show "(Eq_Rel\<restriction>Pl) x (r y) \<longleftrightarrow> (Eq_Rel\<restriction>Pr) (l x) y" . *)
qed

(* lemma lifting_triple_Eq_Rel_id: "lifting_triple (Eq_Rel A) id id"
  using bijection_id
  by (subst Eq_Rel_eq_Iso_Rel) (intro lifting_triple_Iso_Rel_if_bijection) *)


end