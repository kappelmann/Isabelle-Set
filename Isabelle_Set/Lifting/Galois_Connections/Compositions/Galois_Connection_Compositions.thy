subsubsection \<open>Composition of Galois Connections\<close>
theory Galois_Connection_Compositions
  imports
    Galois_Property_Compositions
begin

lemma galois_property_galois_connection_compI:
  assumes "galois_property L1 R1 l1 r1"
  and "galois_property L2 R2 l2 r2"
  and "has_fun_type (in_dom L1) (in_dom L2) l1"
  and "has_fun_type (in_codom R2) (in_codom R1) r2"
  and "\<And>x y. in_dom L1 x \<Longrightarrow> in_codom R2 y \<Longrightarrow> R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and "monotone L1 R2 (l2 \<circ> l1)"
  and "monotone R2 L1 (r1 \<circ> r2)"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  by (intro galois_connectionI galois_property_compI) fact+

lemma galois_connection_compI:
  assumes galois1: "galois_connection L1 R1 l1 r1"
  and galois2: "galois_connection L2 R2 l2 r2"
  and "\<And>x y. in_dom L1 x \<Longrightarrow> in_codom R2 y \<Longrightarrow> R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and R1_l1_finer: "\<And>x x'. R1 (l1 x) (l1 x') \<Longrightarrow> L2 (l1 x) (l1 x')"
  and L2_r2_finer: "\<And>y y'. L2 (r2 y) (r2 y') \<Longrightarrow> R1 (r2 y) (r2 y')"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
proof (rule galois_property_galois_connection_compI)
  from galois1 galois2 R1_l1_finer show "monotone L1 R2 (l2 \<circ> l1)"
    by (intro monotone_compI galois_connection_monotone_left)
  from galois1 galois2 L2_r2_finer show "monotone R2 L1 (r1 \<circ> r2)"
    by (intro monotone_compI galois_connection_monotone_right)
  from galois1 show "has_fun_type (in_dom L1) (in_dom L2) l1"
    by (intro has_fun_typeI)
    (blast elim: in_domE dest: galois_connection_right_rel_left_left_if_left_rel
      intro: in_domI R1_l1_finer)
  from galois2 show "has_fun_type (in_codom R2) (in_codom R1) r2"
    by (intro has_fun_typeI)
    (blast elim: in_codomE dest: galois_connection_left_rel_right_right_if_right_rel
      intro: in_codomI L2_r2_finer)
qed (intro galois_property_if_galois_connection | fact)+

lemma galois_connection_compI':
  assumes "galois_connection L1 R1 l1 r1"
  and "galois_connection R1 R2 l2 r2"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms by (rule galois_connection_compI) simp_all


end