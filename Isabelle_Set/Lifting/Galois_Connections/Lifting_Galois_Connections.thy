subsection \<open>Lifting With Galois Connections\<close>
theory Lifting_Galois_Connections
  imports
    Galois_Connections
    Lifting_Relations_New
    Lifting_Triples
begin

definition "Galois_Rel L r x y \<equiv> L x (r y)"

lemma Galois_Rel_if_left_rel_right:
  assumes "L x (r y)"
  shows "(Galois_Rel L r) x y"
  unfolding Galois_Rel_def using assms .

lemma Galois_Rel_on_left_rel_right:
  assumes "(Galois_Rel L r) x y"
  shows "L x (r y)"
  using assms unfolding Galois_Rel_def by blast

corollary Galois_Rel_iff_left_rel_right: "(Galois_Rel L r) x y \<longleftrightarrow> L x (r y)"
  using Galois_Rel_if_left_rel_right Galois_Rel_on_left_rel_right by (intro iffI)

lemma galois_property_right_rel_left_if_Galois_Rel:
  assumes "galois_property L R l r"
  and "(Galois_Rel L r) x y"
  shows "R (l x) y"
  using assms
  by (blast intro: galois_property_right_rel_left_if_left_rel_right
    dest: Galois_Rel_on_left_rel_right)

lemma galois_property_Galois_Rel_if_right_rel_left:
  assumes "galois_property L R l r"
  and "R (l x) y"
  shows "(Galois_Rel L r) x y"
  using assms
  by (intro Galois_Rel_if_left_rel_right) (rule galois_property_left_rel_right_if_right_rel_left)

corollary galois_property_Galois_Rel_iff_right_rel_left:
  assumes "galois_property L R l r"
  shows "(Galois_Rel L r) x y \<longleftrightarrow> R (l x) y"
  using assms galois_property_right_rel_left_if_Galois_Rel
    galois_property_Galois_Rel_if_right_rel_left
  by (intro iffI)

lemma galois_property_rel_inv_Galois_Rel_rel_inv_eq:
  assumes "galois_property L R l r"
  shows "rel_inv (Galois_Rel (rel_inv R) l) = Galois_Rel L r"
proof (intro ext)
  fix x y
  have "rel_inv (Galois_Rel (rel_inv R) l) x y \<longleftrightarrow> (Galois_Rel (rel_inv R) l) y x"
    by (simp only: rel_inv_iff_rel)
  also have "... \<longleftrightarrow> (rel_inv R) y (l x)" by (fact Galois_Rel_iff_left_rel_right)
  also have "... \<longleftrightarrow> R (l x) y" by (simp only: rel_inv_iff_rel)
  also from assms have "... \<longleftrightarrow> L x (r y)"
    by (rule galois_property_left_rel_right_iff_right_rel_left[symmetric])
  also have "... \<longleftrightarrow> (Galois_Rel L r) x y" by (fact Galois_Rel_iff_left_rel_right[symmetric])
  finally show "rel_inv (Galois_Rel (rel_inv R) l) x y \<longleftrightarrow> Galois_Rel L r x y" .
qed

lemma galois_connection_Galois_Rel_left_if_left_rel:
  assumes "galois_connection L R l r"
  and "L x x'"
  shows "(Galois_Rel L r) x (l x')"
  using assms by (intro Galois_Rel_if_left_rel_right)
    (rule galois_connection_left_rel_right_left_if_left_rel)

lemma galois_connection_Galois_Rel_right_if_right_rel:
  assumes galois: "galois_connection L R l r"
  and "R y y'"
  shows "(Galois_Rel L r) (r y) y'"
  using assms
  by (intro Galois_Rel_if_left_rel_right)
    (rule galois_connection_left_rel_right_right_if_right_rel)

lemma galois_connection_on_Dep_Fun_RelI:
  assumes galois1: "galois_connection L1 R1 l1 r1"
  and galois2: "\<And>x y. (Galois_Rel L1 r1) x y \<Longrightarrow>
    galois_connection (L2 x y) (R2 x y) (l2 y x) (r2 x y)"
  (* and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) (abs2 y x) (rep2 x y)" *)
  (* note swapped order of arguments for abs2 *)
  (* and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  and rep2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_abs (T2 x y) \<Rrightarrow> Eq_rep (T2 x y)) (rep2 x y) (rep2 x' y')"
  and abs2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_rep (T2 x y) \<Rrightarrow> Eq_abs (T2 x y)) (abs2 y x) (abs2 y' x')" *)
    (* shows "True" *)
  shows "galois_connection
    ([x1 x2 \<Colon> L1] \<Rrightarrow> L2 x1 (l1 x2)) ([y1 y2 \<Colon> R1] \<Rrightarrow> R2 (r1 y1) y2)
    (dep_map_fun r1 l2) (dep_map_fun l1 r2)"
    (is "galois_connection ?L ?R ?l ?r")
proof (rule galois_connectionI)
  show "monotone ?L ?R ?l"
  proof (intro dep_monotoneI Dep_Fun_RelI)
    fix f1 f2 y1 y2
    assume "R1 y1 y2"
    with galois1 have "L1 (r1 y1) (r1 y2)"
      by (fact galois_connection_left_rel_right_right_if_right_rel)
    moreover assume "?L f1 f2"
    ultimately have "L2 (r1 y1) (l1 (r1 y2)) (f1 (r1 y1)) (f2 (r1 y2))"
      by (blast dest: Dep_Fun_RelD)
    (*L2 covar at pos 2*)
    then have "L2 (r1 y1) y2 (f1 (r1 y1)) (f2 (r1 y2))" sorry
    from galois1 \<open>R1 y1 y2\<close> have "(Galois_Rel L1 r1) (r1 y1) y2"
      by (rule galois_connection_Galois_Rel_right_if_right_rel)
    then have "galois_connection (L2 (r1 y1) y2) (R2 (r1 y1) y2) (l2 y2 (r1 y1)) (r2 (r1 y1) y2)"
      by (rule galois2)
    from this \<open>L2 (r1 y1) y2 _ _\<close> have
      "R2 (r1 y1) y2 (l2 y2 (r1 y1) (f1 (r1 y1))) (l2 y2 (r1 y1) (f2 (r1 y2)))"
      by (rule galois_connection_right_rel_left_left_if_left_rel)
    (*l2 contravar at pos 1; covar at pos 2*)
    then have
      "R2 (r1 y1) y2 (l2 y1 (r1 y1) (f1 (r1 y1))) (l2 y2 (r1 y2) (f2 (r1 y2)))"
      sorry
    then show "R2 (r1 y1) y2 (?l f1 y1) (?l f2 y2)" unfolding dep_map_fun_def .
  qed
  show "monotone ?R ?L ?r"
  proof (intro dep_monotoneI Dep_Fun_RelI)
    fix f1 f2 x1 x2
    assume "L1 x1 x2"
    with galois1 have "R1 (l1 x1) (l1 x2)"
      by (fact galois_connection_right_rel_left_left_if_left_rel)
    moreover assume "?R f1 f2"
    ultimately have "R2 (r1 (l1 x1)) (l1 x2) (f1 (l1 x1)) (f2 (l1 x2))"
      by (blast dest: Dep_Fun_RelD)
    (*R2 contravar at pos 1*)
    then have "R2 x1 (l1 x2) (f1 (l1 x1)) (f2 (l1 x2))" sorry
    from galois1 \<open>L1 x1 x2\<close> have "(Galois_Rel L1 r1) x1 (l1 x2)"
      by (rule galois_connection_Galois_Rel_left_if_left_rel)
    then have "galois_connection (L2 x1 (l1 x2)) (R2 x1 (l1 x2)) (l2 (l1 x2) x1) (r2 x1 (l1 x2))"
      by (rule galois2)
    from this \<open>R2 x1 (l1 x2) _ _\<close> have
      "L2 x1 (l1 x2) (r2 x1 (l1 x2) (f1 (l1 x1))) (r2 x1 (l1 x2) (f2 (l1 x2)))"
      by (rule galois_connection_left_rel_right_right_if_right_rel)
    (*r2 contravar at pos 2; covar at pos 1*)
    then have
      "L2 x1 (l1 x2) (r2 x1 (l1 x1) (f1 (l1 x1))) (r2 x2 (l1 x2) (f2 (l1 x2)))"
      sorry
    then show "L2 x1 (l1 x2) (?r f1 x1) (?r f2 x2)" unfolding dep_map_fun_def .
  qed
  show "galois_property ?L ?R ?l ?r"
  proof (intro galois_propertyI iffI Dep_Fun_RelI)
    fix f g y1 y2
    assume "?L f (?r g)"
    then have "\<And>x1 x2. L1 x1 x2 \<Longrightarrow> L2 x1 (l1 x2) (f x1) ((?r g) x2)"
      by (blast elim: Dep_Fun_RelE)
    then have L_Dep_Fun_Rel: "\<And>x1 x2. L1 x1 x2 \<Longrightarrow> L2 x1 (l1 x2) (f x1) (r2 x2 (l1 x2) (g (l1 x2)))"
      by (simp only: dep_map_fun_eq)
    assume "R1 y1 y2"
    with galois1 have "(Galois_Rel L1 r1) (r1 y1) y2"
      by (rule galois_connection_Galois_Rel_right_if_right_rel)
    then have galois3:
      "galois_connection (L2 (r1 y1) y2) (R2 (r1 y1) y2) (l2 y2 (r1 y1)) (r2 (r1 y1) y2)"
      by (rule galois2)
    from galois1 \<open>R1 y1 y2\<close> have "L1 (r1 y1) (r1 y2)"
      by (rule galois_connection_left_rel_right_right_if_right_rel)
    then have "L2 (r1 y1) (l1 (r1 y2)) (f (r1 y1)) (r2 (r1 y2) (l1 (r1 y2)) (g (l1 (r1 y2))))"
      by (rule L_Dep_Fun_Rel)
    (*L2 covar at pos 2*)
    then have "L2 (r1 y1) y2 (f (r1 y1)) (r2 (r1 y2) (l1 (r1 y2)) (g (l1 (r1 y2))))"
      sorry
    with galois3 have
      "R2 (r1 y1) y2 (l2 y2 (r1 y1) (f (r1 y1))) (l2 y2 (r1 y1) (r2 (r1 y2) (l1 (r1 y2)) (g (l1 (r1 y2)))))"
      by (rule galois_connection_right_rel_left_left_if_left_rel)
    (*l2 contravar at pos 1*)
    have "R2 (r1 y1) y2 (l2 y1 (r1 y1) (f (r1 y1))) (g y2)" sorry
    then show "R2 (r1 y1) y2 (?l f y1) (g y2)"
      by (simp only: dep_map_fun_eq)
    (* also have "... \<longleftrightarrow> (\<forall>x1 x2. L1 x1 x2 \<longrightarrow> L2 x1 (l1 x2) (f x1) (r2 x2 (l1 x2) (g (l1 x2))))"
      by (simp only: dep_map_fun_eq) *)
    (* have "... \<longleftrightarrow> (\<forall>x1 x2. L1 x1 x2 \<longrightarrow> R2 x1 (l1 x2) (l2 ? ? (f x1)) (l2 ? ? (?r g) x2))" *)
    (* have "True \<longleftrightarrow> (\<forall>y1 y2. R1 y1 y2 \<longrightarrow> R2 (r1 y1) y2 (l2 y1 (r1 y1) (f (r1 y1))) (g y2))"
      sorry
    also have "... \<longleftrightarrow> (\<forall>y1 y2. R1 y1 y2 \<longrightarrow> R2 (r1 y1) y2 ((?l f) y1) (g y2))"
      by (simp only: dep_map_fun_eq)
    show "?L f (?r g) \<longleftrightarrow> ?R (?l f) g"
      sorry *)

(*
(l2 y2 (r1 y1) (r2 (r1 y2) (l1 (r1 y2)) (g (l1 (r1 y2))))

(g y2)

(L1 => L2) f f'
(R1 => R2) g' g

L1 x1 x2 => L2 (f x1) (r2 g l1 x2)

L1 (l1 r1 y2) y2 ==> L2 (g l1 r1 y2) (g y2)

f x ==> r1 (f l1 x) ==> g x

R1 y1 y2
==>
L1 (r1 y1) (r1 y2)                R2 (g' y1) (g y2)
==>
L2 (f r1 y1) (r2 g (l1 r1 y2))    L2 (f r1 y1) (f' r1 y2)
<==>
R2 (l2 f r1 y1) (g (l1 r1 y2))    R2 (g (l1 r1 y2))
==>
R2 (l2 f r1 y1) (g y2)


(* <==>
(Galois_Rel L2 r2) (f r1 y1) (g (l1 r1 y2)) *)

(R1 \<Rightarrow> R2) g g <===> R1 y1 y2 ==> R2 (g y1) (g y2)
(* L1 (r1 y1) (x2) *)
(R2 \<Rightarrow> L2) r2 r2 <====> R2 y1'y2' ==> L2 (r2 y1') (r2 y2')


(* (Galois_Rel L2 r2) (f r1 y1) (g y2)
<==>
L2 (f r1 y1) (r2 g y2)
<==> *)
R2 (l2 f r1 y1) (g y2)
*)
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


lemma lifting_triple_monotone_Eq_rep_Eq_abs_abs:
  assumes "lifting_triple R abs rep"
  shows "monotone (Eq_rep R) (Eq_abs R) abs"
  using assms
  by (intro dep_monotoneI lifting_triple_Eq_abs_abs_abs_if_Eq_rep)

lemma lifting_triple_monotone_Eq_abs_Eq_rep_rep:
  assumes "lifting_triple R abs rep"
  shows "monotone (Eq_abs R) (Eq_rep R) rep"
  using assms
  by (intro dep_monotoneI lifting_triple_Eq_rep_rep_rep_if_Eq_abs)

lemma lifting_triple_Eq_abs_abs_if_Eq_rep_rep:
  assumes lift_trip: "lifting_triple R abs rep"
  and in_codom: "in_codom (Eq_abs R) y"
  and Eq_rep: "Eq_rep R x (rep y)"
  shows "Eq_abs R (abs x) y"
proof -
  from lift_trip have "transitive (Eq_abs R)"
    by (intro transitive_Eq_abs_if_z_property z_property_if_lifting_triple)
  from lift_trip Eq_rep have Eq_abs_abs_abs_rep: "(Eq_abs R) (abs x) (abs (rep y))"
    by (intro lifting_triple_Eq_abs_abs_abs_if_Eq_rep)
  from in_codom have "in_codom R y" by (rule in_codom_if_in_codom_Eq_abs)
  with lift_trip have "(Eq_abs R) (abs (rep y)) y"
    by (rule lifting_triple_Eq_abs_abs_rep_self_if_in_codom)
  with \<open>transitive (Eq_abs R)\<close> Eq_abs_abs_abs_rep show "(Eq_abs R) (abs x) y"
    by (rule transitiveD)
qed

lemma lifting_triple_Eq_rep_rep_if_Eq_abs_abs:
  assumes lift_trip: "lifting_triple R abs rep"
  and in_dom: "in_dom (Eq_rep R) x"
  and Eq_abs: "Eq_abs R (abs x) y"
  shows "Eq_rep R x (rep y)"
proof -
  from lift_trip have "transitive (Eq_rep R)"
    by (intro transitive_Eq_rep_if_z_property z_property_if_lifting_triple)
  from in_dom have "in_dom R x" by (rule in_dom_if_in_dom_Eq_rep)
  with lift_trip have Eq_rep_rep_abs: "(Eq_rep R) x (rep (abs x))"
    by (rule lifting_triple_Eq_rep_rep_abs_self_if_in_dom)
  from lift_trip Eq_abs have "(Eq_rep R) (rep (abs x)) (rep y)"
    by (intro lifting_triple_Eq_rep_rep_rep_if_Eq_abs)
  with \<open>transitive (Eq_rep R)\<close> Eq_rep_rep_abs show "(Eq_rep R) x (rep y)"
    by (blast intro: transitiveD)
qed

lemma galois_property_if_lifting_triple:
  assumes "lifting_triple R abs rep"
  shows "galois_property (Eq_rep R) (Eq_abs R) abs rep"
  using assms
  by (intro galois_propertyI)
    (blast intro: lifting_triple_Eq_abs_abs_if_Eq_rep_rep lifting_triple_Eq_rep_rep_if_Eq_abs_abs)

lemma galois_connection_if_lifting_triple:
  assumes "lifting_triple R abs rep"
  shows "galois_connection (Eq_rep R) (Eq_abs R) abs rep"
  using assms
  by (intro galois_connectionI lifting_triple_monotone_Eq_rep_Eq_abs_abs
    lifting_triple_monotone_Eq_abs_Eq_rep_rep galois_property_if_lifting_triple)



end