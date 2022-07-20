section \<open>Galois Connections\<close>
theory Galois_Connections
  imports
    Galois_Connections_Base
    Galois_Compositions
begin

(* lemma TODO:
  assumes galois1: "galois_connection L1 R1 l1 r1"
  and galois2: "galois_connection L2 R2 l2 r2"
  (* and "\<And>x y. in_dom L1 x \<Longrightarrow> in_codom R2 y \<Longrightarrow> R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)" *)
  (* and R1_l1_finer: "\<And>x x'. R1 (l1 x) (l1 x') \<Longrightarrow> L2 (l1 x) (l1 x')"
  and L2_r2_finer: "\<And>z z'. L2 (r2 z) (r2 z') \<Longrightarrow> R1 (r2 z) (r2 z')" *)
  defines "l \<equiv> l2 \<circ> l1" and "r \<equiv> r1 \<circ> r2"
  defines "L \<equiv> L1 \<sqinter> (rel_map l1 L2)" and "R \<equiv> R2 \<sqinter> (rel_map r2 R1)"
  (* defines "L \<equiv> L1 \<sqinter> (rel_map (r \<circ> l) L1)" and "R \<equiv> R2 \<sqinter> (rel_map (l \<circ> r) R2)" *)
  shows "galois_connection L R l r"
proof (rule galois_connectionI)
  show "monotone L R l" unfolding L_def
  proof (rule dep_monotoneI)
    fix x x'
    assume "(L1 \<sqinter> rel_map l1 L2) x x'"
    then have "L1 x x'" "L2 (l1 x) (l1 x')" by (fastforce elim: rel_interE)+
    then have "R2 (l x) (l x')" sorry
    moreover have "rel_map r2 R1 (l x) (l x')" sorry
    ultimately show "R (l x) (l x')" unfolding R_def l_def by (rule rel_interI)
    (* assume "(L1 \<sqinter> rel_map (r \<circ> l) L1) x x'"
    then have "L1 x x'" "L1 (r (l x)) (r (l x'))" by (fastforce elim: rel_interE)+
    have "R2 (l2 (l1 x)) (l2 (l1 x'))" sorry
    show "(R2 \<sqinter> rel_map (l \<circ> r) R2) (l x) (l x')" sorry *)
  qed
  show "galois_property L R l r"
  proof (rule galois_propertyI)
    fix x y
    assume "in_dom L x" "in_codom R y"
    then have "in_dom L1 x" "in_codom R1 (r2 y)"
      unfolding L_def R_def
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
  (* from galois1 galois2 L2_r2_finer show "monotone R2 L1 (r1 \<circ> r2)"
    by (intro monotone_compI galois_connection_monotone_right)
  from galois1 show "has_fun_type (in_dom L1) (in_dom L2) l1"
    by (intro has_fun_typeI)
    (blast elim: in_domE dest: galois_connection_right_rel_left_left_if_left_rel
      intro: in_domI R1_l1_finer)
  from galois2 show "has_fun_type (in_codom R2) (in_codom R1) r2"
    by (intro has_fun_typeI)
    (blast elim: in_codomE dest: galois_connection_left_rel_right_right_if_right_rel
      intro: in_codomI L2_r2_finer) *)
qed
(intro galois_property_if_galois_connection | fact)+ *)

end