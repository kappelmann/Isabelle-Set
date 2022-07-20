subsection \<open>Composition of Galois Property\<close>
theory Galois_Property_Compositions
  imports
    Galois_Equivalences
    Galois_Relations
begin

lemma galois_property_compI:
  assumes galois1: "galois_property L1 R1 l1 r1"
  and galois2: "galois_property L2 R2 l2 r2"
  and has_fun_type_l1: "has_fun_type (in_dom L1) (in_dom L2) l1"
  and has_fun_type_r2: "has_fun_type (in_codom R2) (in_codom R1) r2"
  and agree: "\<And>x y. in_dom L1 x \<Longrightarrow> in_codom R2 y \<Longrightarrow> R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  shows "galois_property L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
proof (rule galois_propertyI)
  fix x y assume "in_dom L1 x" "in_codom R2 y"
  with has_fun_type_r2 has_fun_type_l1 have "in_dom L2 (l1 x)" "in_codom R1 (r2 y)"
    by (blast dest: has_fun_typeD)+
  have "L1 x ((r1 \<circ> r2) y) \<longleftrightarrow> L1 x (r1 (r2 y))" by simp
  also from galois1 \<open>in_dom L1 x\<close> \<open>in_codom R1 (r2 y)\<close> have "... \<longleftrightarrow> R1 (l1 x) (r2 y)"
    by (rule galois_property_left_rel_right_iff_right_rel_left)
  also from \<open>in_dom L1 x\<close> \<open>in_codom R2 y\<close> have "... \<longleftrightarrow> L2 (l1 x) (r2 y)"
    by (rule agree)
  also from galois2 \<open>in_dom L2 (l1 x)\<close> \<open>in_codom R2 y\<close> have "... \<longleftrightarrow> R2 (l2 (l1 x)) y"
    by (rule galois_property_left_rel_right_iff_right_rel_left)
  also have "... \<longleftrightarrow> R2 ((l2 \<circ> l1) x) y" by simp
  finally show "L1 x ((r1 \<circ> r2) y) \<longleftrightarrow> R2 ((l2 \<circ> l1) x) y" .
qed

(*Lemmas *)

lemma galois_connection_right_rel_left_right_if_reflexive_on:
  assumes "galois_connection L R l r"
  and "reflexive_on P R"
  and "P y"
  shows "R (l (r y)) y"
  using assms by (blast intro: galois_connection_right_rel_left_right_if_right_rel
    dest: reflexive_onD)

context
  fixes L1 R1 l1 r1 L2 R2 l2 r2 L R l r
  assumes galois1: "galois_connection L1 R1 l1 r1"
  and galois2: "galois_connection L2 R2 l2 r2"
  defines "l \<equiv> l2 \<circ> l1" and "r \<equiv> r1 \<circ> r2"
  and "L \<equiv> Galois_Comp_Left L1 R1 l1 r1 L2" and "R \<equiv> Galois_Comp_Right R1 L2 R2 r2"
begin

lemma galois_property_Galois_CompI:
  assumes galois_equiv_left2: "galois_equivalence_left L2 l2 r2"
  and preorder_R1: "preorder_on (in_field R1) R1"
  and R1_L2_comm: "(R1 \<circ>\<circ> L2) = (L2 \<circ>\<circ> R1)"
  shows "galois_property L R l r"
proof (rule galois_propertyI)
  from preorder_R1 have
    trans_R1: \<open>transitive R1\<close> and refl_R1: \<open>reflexive_on (in_field R1) R1\<close>
    by (blast elim: preorder_onE intro: transitive_if_transitive_on_in_field)+

  fix x z assume "in_dom L x"

  assume "in_codom R z"
  then obtain wr wr' where
    "R1 wr wr'" "L2 wr' (r2 z)" "in_codom R2 z"
    unfolding R_def by (blast elim: in_codomE Galois_Comp_RightE GaloisE)

  show "L x (r z) \<longleftrightarrow> R (l x) z"
  proof
    assume "L x (r z)"
    then obtain yl yl' where
      "(Galois L1 R1 r1) x yl" "L2 yl yl'" "(Galois_Inv_Right L1 R1 l1) yl' (r z)"
      unfolding L_def by (elim Galois_Comp_LeftE)
    from \<open>(Galois_Inv_Right L1 R1 l1) yl' (r z)\<close> have "R1 yl' (l1 (r z))"
      (* "in_dom L1 (r z)" *)
      by (blast elim: Galois_Inv_RightE)+
    moreover have "R1 (l1 (r z)) (r2 z)"
    proof -
      have "in_field R1 (r2 z)"
      proof (rule in_field_if_in_codom)
        from \<open>R1 wr wr'\<close> \<open>L2 wr' (r2 z)\<close> have "(R1 \<circ>\<circ> L2) wr (r2 z)"
          by (elim rel_compI)
        with R1_L2_comm have "(L2 \<circ>\<circ> R1) wr (r2 z)" by simp
        then show "in_codom R1 (r2 z)" by
          (blast dest: in_codomI intro: in_codom_if_in_codom_rel_comp)
      qed
      with galois1 refl_R1 show "R1 (l1 (r z)) (r2 z)"
        unfolding r_def
        by (auto intro: galois_connection_right_rel_left_right_if_reflexive_on)
    qed
    ultimately have "R1 yl' (r2 z)" using trans_R1 by (elim transitiveD)
    with \<open>L2 yl yl'\<close> have "(L2 \<circ>\<circ> R1) yl (r2 z)" by (rule rel_compI)
    with R1_L2_comm have "(R1 \<circ>\<circ> L2) yl (r2 z)" by simp
    then obtain w where "R1 yl w" "L2 w (r2 z)" by (elim rel_compE)
    show "R (l x) z" unfolding R_def
    proof (rule Galois_Comp_RightI)
      from \<open>in_codom R2 z\<close> \<open>L2 w (r2 z)\<close> show "Galois L2 R2 r2 w z" by (rule GaloisI)
      from galois1 \<open>(Galois L1 R1 r1) x yl\<close> have "R1 (l1 x) yl"
        by (blast dest: galois_property_if_galois_connection elim: galois_property_GaloisE)
      with trans_R1 \<open>R1 yl w\<close> show "R1 (l1 x) w" by (elim transitiveD)
      show "Galois_Inv_Left L2 R2 r2 (l x) (l1 x)"
      proof (rule Galois_Inv_LeftI)
        from \<open>R1 (l1 x) w\<close> \<open>L2 w (r2 z)\<close> have "(R1 \<circ>\<circ> L2) (l1 x) (r2 z)"
          by (rule rel_compI)
        with R1_L2_comm have "(L2 \<circ>\<circ> R1) (l1 x) (r2 z)" by simp
        then have "in_dom L2 (l1 x)" by
          (blast dest: in_domI intro: in_dom_if_in_dom_rel_comp)
        with galois_equiv_left2 show "L2 (r2 (l x)) (l1 x)"
          unfolding l_def by (auto dest: galois_equivalence_leftD)
        with galois2 show "in_codom R2 (l x)"
          unfolding l_def by (auto dest!: galois_connection_monotone_left
            intro: monotone_in_codom_if_in_codom in_codomI)
      qed
    qed
  qed
  (* "(Galois_Inv_Left L2 R2 r2) z' y2" "R1 y2 y2'" "(Galois L2 R2 r2) y2' z" *)
  then have "in_dom L1 x" "in_codom R1 (r2 y)" unfolding L_def R_def
    by (fastforce elim: in_dom_rel_interE in_codom_rel_interE intro: in_domI in_codomI)+
  (* then obtain x' y' where "L x x'" "R y' y" by (blast elim: in_domE in_codomE)
  then have "L1 x x'" "L2 (l1 x) (l1 x')" "R2 y' y" "R1 (r2 y') (r2 y)"
    unfolding L_def R_def by (fastforce elim: rel_interE)+ *)
  have "L x (r y) \<longleftrightarrow> L1 x (r y) \<and> L2 (l1 x) (l1 (r y))"
    unfolding L_def by (fastforce elim: rel_interE intro: rel_interI)
  have "R2 (l x) y \<and> R1 (r2 (l x)) (r2 y) \<longleftrightarrow> R (l x) y"
    unfolding R_def by (fastforce elim: rel_interE intro: rel_interI)
  also from galois1 \<open>in_dom L1 x\<close> \<open>in_codom R1 (r2 y)\<close>
    have "... \<longleftrightarrow> R1 (l1 x) (r2 y)"
    by (rule galois_property_left_rel_right_iff_right_rel_left)
  also from \<open>in_dom L1 x\<close> \<open>in_codom R2 y\<close> have "... \<longleftrightarrow> L2 (l1 x) (r2 y)"
    by (rule agree)
  also from galois2 \<open>in_dom L2 (l1 x)\<close> \<open>in_codom R2 y\<close> have "... \<longleftrightarrow> R2 (l2 (l1 x)) y"
    by (rule galois_property_left_rel_right_iff_right_rel_left)
  also have "... \<longleftrightarrow> R2 ((l2 \<circ> l1) x) y" by simp
  finally show "L1 x ((r1 \<circ> r2) y) \<longleftrightarrow> R2 ((l2 \<circ> l1) x) y" .
  show "L x (r y) \<longleftrightarrow> R (l x) y" sorry
qed

end