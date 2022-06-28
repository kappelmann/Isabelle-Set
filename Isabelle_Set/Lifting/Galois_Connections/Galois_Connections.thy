section \<open>Galois Connections\<close>
theory Galois_Connections
  imports LBinary_Relations
begin

text\<open>A \<^emph>\<open>Galois connection\<close> between two relations @{term "L"} and @{term "R"}
consists of two monotone functions @{term "l"} and @{term "r"} such that
@{term "L x (r y) \<longleftrightarrow> R (l x) y"}. We call this the \<^emph>\<open>Galois property\<close>.
@{term "l"} is called the \<^emph>\<open>left adjoint\<close> and @{term "r"} the \<^emph>\<open>right adjoint\<close>.
We call @{term "L"} the \<^emph>\<open>left relation\<close> and @{term "R"} the \<^emph>\<open>right relation\<close>.\<close>

definition "galois_property L R l r \<equiv>
  \<forall>x y. in_dom L x \<longrightarrow> in_codom R y \<longrightarrow> L x (r y) \<longleftrightarrow> R (l x) y"

lemma galois_propertyI:
  assumes "\<And>x y. in_dom L x \<Longrightarrow> in_codom R y \<Longrightarrow> L x (r y) \<longleftrightarrow> R (l x) y"
  shows "galois_property L R l r"
  unfolding galois_property_def using assms by blast

lemma galois_property_left_rel_right_iff_right_rel_left:
  assumes "galois_property L R l r"
  and "in_dom L x" "in_codom R y"
  shows "L x (r y) \<longleftrightarrow> R (l x) y"
  using assms unfolding galois_property_def by blast

lemma galois_property_right_rel_left_if_left_rel_right:
  assumes "galois_property L R l r"
  and "in_codom R y"
  and "L x (r y)"
  shows "R (l x) y"
proof -
  from \<open>L x (r y)\<close> have "in_dom L x" by (rule in_domI)
  with assms show ?thesis
    using galois_property_left_rel_right_iff_right_rel_left by fastforce
qed

lemma galois_property_left_rel_right_if_right_rel_left:
  assumes "galois_property L R l r"
  and "in_dom L x"
  and "R (l x) y"
  shows "L x (r y)"
proof -
  from \<open>R (l x) y\<close> have "in_codom R y" by (rule in_codomI)
  with assms show ?thesis
    using galois_property_left_rel_right_iff_right_rel_left by fastforce
qed

lemma galois_property_dual:
  assumes "galois_property L R l r"
  shows "galois_property (rel_inv R) (rel_inv L) r l"
  using assms
  by (intro galois_propertyI)
    (simp only: rel_inv_iff_rel in_codom_rel_inv_iff_in_dom in_dom_rel_inv_iff_in_codom
      galois_property_left_rel_right_iff_right_rel_left)

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

definition "galois_connection L R l r \<equiv>
  monotone L R l \<and> monotone R L r \<and> galois_property L R l r"

lemma galois_connectionI:
  assumes "monotone L R l" "monotone R L r"
  and "galois_property L R l r"
  shows "galois_connection L R l r"
  unfolding galois_connection_def using assms by blast

lemma galois_connectionE:
  assumes "galois_connection L R l r"
  obtains "monotone L R l" "monotone R L r" "galois_property L R l r"
  using assms unfolding galois_connection_def by blast

lemma galois_connection_monotone_left:
  assumes "galois_connection L R l r"
  shows "monotone L R l"
  using assms by (elim galois_connectionE)

lemma galois_connection_monotone_right:
  assumes "galois_connection L R l r"
  shows "monotone R L r"
  using assms by (elim galois_connectionE)

lemma galois_property_if_galois_connection:
  assumes "galois_connection L R l r"
  shows "galois_property L R l r"
  using assms by (elim galois_connectionE)

lemma galois_connection_left_rel_right_iff_right_rel_left:
  assumes "galois_connection L R l r"
  and "in_dom L x" "in_codom R y"
  shows "L x (r y) \<longleftrightarrow> R (l x) y"
  by (fact galois_property_left_rel_right_iff_right_rel_left
    [OF galois_property_if_galois_connection, OF assms])

lemma galois_connection_right_rel_left_left_if_left_rel:
  assumes "galois_connection L R l r"
  and "L x x'"
  shows "R (l x) (l x')"
  using assms by (force intro: dep_monotoneD dest: galois_connection_monotone_left)

lemma galois_connection_left_rel_right_right_if_right_rel:
  assumes "galois_connection L R l r"
  and "R y y'"
  shows "L (r y) (r y')"
  using assms by (force intro: dep_monotoneD dest: galois_connection_monotone_right)

lemma galois_connection_right_rel_left_if_left_rel_right:
  assumes "galois_connection L R l r"
  and "in_codom R y"
  and "L x (r y)"
  shows "R (l x) y"
  using assms
  by (blast dest: galois_property_if_galois_connection
    intro: galois_property_right_rel_left_if_left_rel_right)

lemma galois_connection_left_rel_right_if_right_rel_left:
  assumes "galois_connection L R l r"
  and "in_dom L x"
  and "R (l x) y"
  shows "L x (r y)"
  using assms
  by (blast dest: galois_property_if_galois_connection
    intro: galois_property_left_rel_right_if_right_rel_left)

lemma galois_connection_left_rel_right_left_if_left_rel:
  assumes galois: "galois_connection L R l r"
  and "L x x'"
  shows "L x (r (l x'))"
proof -
  from galois \<open>L x x'\<close> have "R (l x) (l x')"
    by (rule galois_connection_right_rel_left_left_if_left_rel)
  moreover from \<open>L x x'\<close> have "in_dom L x" by (rule in_domI)
  ultimately show "L x (r (l x'))" using galois
    by (blast intro: galois_connection_left_rel_right_if_right_rel_left)
qed

lemma galois_connection_right_rel_left_right_if_right_rel:
  assumes galois: "galois_connection L R l r"
  and "R y y'"
  shows "R (l (r y)) y'"
proof -
  from galois \<open>R y y'\<close> have "L (r y) (r y')"
    by (rule galois_connection_left_rel_right_right_if_right_rel)
  moreover from \<open>R y y'\<close> have "in_codom R y'" by (rule in_codomI)
  ultimately show "R (l (r y)) y'" using galois
    by (blast intro: galois_connection_right_rel_left_if_left_rel_right)
qed

lemma galois_connection_dual:
  assumes "galois_connection L R l r"
  shows "galois_connection (rel_inv R) (rel_inv L) r l"
  using assms by (intro galois_connectionI) (auto
    intro: monotone_rel_inv_if_monotone galois_connection_monotone_left
      galois_connection_monotone_right galois_property_dual
    simp only: rel_inv_iff_rel galois_property_if_galois_connection)

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
  and "has_fun_type (in_dom L1) (in_dom L2) l1"
  and "has_fun_type (in_codom R2) (in_codom R1) r2"
  and "\<And>x y. in_dom L1 x \<Longrightarrow> in_codom R2 y \<Longrightarrow> R1 (l1 x) (r2 y) \<longleftrightarrow> L2 (l1 x) (r2 y)"
  and R1_l1_finer: "\<And>x x'. R1 (l1 x) (l1 x') \<Longrightarrow> L2 (l1 x) (l1 x')"
  and L2_r2_finer: "\<And>z z'. L2 (r2 z) (r2 z') \<Longrightarrow> R1 (r2 z) (r2 z')"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
proof (rule galois_property_galois_connection_compI)
  from galois1 galois2 R1_l1_finer show "monotone L1 R2 (l2 \<circ> l1)"
    by (intro monotone_compI galois_connection_monotone_left)
  from galois1 galois2 L2_r2_finer show "monotone R2 L1 (r1 \<circ> r2)"
    by (intro monotone_compI galois_connection_monotone_right)
qed (intro galois_property_if_galois_connection | fact)+

lemma galois_connection_compI':
  assumes "galois_connection L1 R1 l1 r1"
  and "galois_connection R1 R2 l2 r2"
  and "has_fun_type (in_dom L1) (in_dom R1) l1"
  and "has_fun_type (in_codom R2) (in_codom R1) r2"
  shows "galois_connection L1 R2 (l2 \<circ> l1) (r1 \<circ> r2)"
  using assms by (rule galois_connection_compI) simp_all


subsection \<open>Instantiations\<close>

lemma galois_property_eq_id: "galois_property (=) (=) id id"
  by (rule galois_propertyI) simp

lemma galois_connection_eq_id: "galois_connection (=) (=) id id"
  by (intro galois_connectionI galois_property_eq_id monotone_self_id)


end