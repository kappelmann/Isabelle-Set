\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generalised Addition\<close>
theory SAddition
  imports
    Less_Than
begin
paragraph \<open>Summary\<close>
text \<open>Translation of general set addition from \<^cite>\<open>kirby_set_arithemtics\<close>
and \<^cite>\<open>ZFC_in_HOL_AFP\<close>. Note that general set addition is associative but not commutative.\<close>

text \<open>Define the generalized addition operation for sets.\<close>
definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"

bundle hotg_add_syntax begin notation add (infixl "+" 65) end
bundle no_hotg_add_syntax begin no_notation add (infixl "+" 65) end
unbundle hotg_add_syntax

lemma add_eq_bin_union_repl_add: "X + Y = X \<union> {X + y | y \<in> Y}"
  unfolding add_def by (simp add: transrec_eq)

text \<open>The lift operation is the recursive operation in the definition of addition.\<close>

definition "lift X \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma lift_eq_repl_add: "lift X Y = {X + y | y \<in> Y}"
  using lift_eq_image_add by simp

lemma add_eq_bin_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (subst add_eq_bin_union_repl_add) simp

corollary lift_subset_add: "lift X Y \<subseteq> X + Y"
  using add_eq_bin_union_lift by auto

lemma lift_bin_union_eq_lift_bin_union_lift: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

lemma lift_union_eq_idx_union_lift: "lift X (\<Union>Y) = (\<Union>y \<in> Y. lift X y)"
  by (auto simp: lift_eq_image_add)

lemma idx_union_add_eq_add_idx_union:
  "Y \<noteq> {} \<Longrightarrow> (\<Union>y \<in> Y. X + f y) = X + (\<Union>y \<in> Y. f y)"
  by (simp add: lift_union_eq_idx_union_lift add_eq_bin_union_lift)

lemma lift_zero_eq_zero [simp]: "lift X 0 = 0"
  by (auto simp: lift_eq_image_add)

text \<open>Demonstrate that adding zero to any set results in the set itself, illustrating the identity property of addition.\<close>
lemma add_zero_eq_self [simp]: "X + 0 = X"
  unfolding add_eq_bin_union_lift by simp

text \<open>Show that lifting a set by one (the singleton set) results in the set itself, encapsulating the set within a singleton set.\<close>
lemma lift_one_eq_singleton_self [simp]: "lift X 1 = {X}"
  unfolding lift_def by simp

text \<open>Define the successor of a set in terms of addition, effectively incrementing the set by adding the singleton set.\<close>
definition "succ X \<equiv> X + 1"

text \<open>Confirm that the successor of a set is equivalent to adding one to the set, aligning with the definition of set increment.\<close>
lemma succ_eq_add_one: "succ X = X + 1"
  unfolding succ_def by simp

text \<open>Illustrate that inserting a set into itself is equivalent to the operation of adding one to the set, reflecting a form of self-increment.\<close>
lemma insert_self_eq_add_one: "insert X X = X + 1"
  by (auto simp: add_eq_bin_union_lift succ_eq_add_one)

text \<open>Establish that the successor operation is equivalent to inserting the set into itself, reinforcing the concept of incrementing a set.\<close>
lemma succ_eq_insert: "succ X  = insert X X"
  by (simp add:succ_def  insert_self_eq_add_one[of X])

text \<open>Demonstrate that lifting an insertion operation over sets results in the insertion of the addition of the set to one of the elements and the lifting of the other element, merging the concepts of addition and set insertion.\<close>
lemma lift_insert_eq_insert_add_lift: "lift X (insert Y Z) = insert (X + Y) (lift X Z)"
  unfolding lift_def by (simp add: repl_insert_eq)

text \<open>Show that adding a set to an inserted pair of sets is equivalent to individually adding the set to each element and then inserting, illustrating distributivity of addition over set insertion.\<close>
lemma add_insert_eq_insert_add: "X + insert Y Z = insert (X + Y) (X + Z)"
  by (auto simp: lift_insert_eq_insert_add_lift add_eq_bin_union_lift)


paragraph\<open>Proposition 3.3\<close>

text \<open>Show that adding zero to any set results in the set itself, illustrating the identity property of addition in this set theory context.\<close>
lemma zero_add_eq_self [simp]: "0 + X = X"
proof (induction X)
  case (mem X)
  text \<open>First, represent the addition of zero to a set as lifting zero over the set.\<close>
  have "0 + X = lift 0 X" by (simp add: add_eq_bin_union_lift)
  text \<open>Then, demonstrate that lifting zero over any set simplifies to the set itself, exploiting the identity property of zero in addition.\<close>
  also from mem have "... = X" by (simp add: lift_eq_image_add)
  text \<open>Conclude that adding zero to any set yields the set itself.\<close>
  finally show ?case .
qed

text \<open>Corroborate that lifting a set by zero results in the set itself, directly following from the definition of lift and the identity property of zero.\<close>
corollary lift_zero_eq_self [simp]: "lift 0 X = X"
  by (simp add: lift_eq_image_add)

text \<open>Establish that if the addition of two sets results in zero, then both sets must necessarily be zero, reflecting the cancellation property in this context.\<close>
corollary add_eq_zeroE:
  assumes "X + Y = 0"
  obtains "X = 0" "Y = 0"
  using assms by (auto simp: add_eq_bin_union_lift)

text \<open>Prove that the addition of two sets results in zero if and only if both sets are zero, reinforcing the notion of zero as an additive identity.\<close>
corollary add_eq_zero_iff_and_eq_zero [iff]: "X + Y = 0 \<longleftrightarrow> X = 0 \<and> Y = 0"
  using add_eq_zeroE by auto


text \<open>Next, we prove that addition is associative:\<close>

lemma add_assoc: "(X + Y) + Z = X + (Y + Z)"
text \<open>We prove the associativity of addition by induction on Z.\<close>
proof (induction Z)
  case (mem Z)
  text \<open>First, we express (X + Y) + Z in terms of set union and lifting.\<close>
  from add_eq_bin_union_lift have "(X + Y) + Z = (X + Y) \<union> (lift (X + Y) Z)" by simp
  text \<open>Next, we use the definition of lifting to unfold the addition within the set comprehension.\<close>
  also from lift_eq_repl_add have "... = (X + Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  text \<open>We then distribute the addition over the union, separating X and Y's contributions.\<close>
  also from add_eq_bin_union_lift have "... = X \<union> (lift X Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  text \<open>By applying our induction hypothesis, we simplify the inner additions, aligning them with our goal's structure.\<close>
  also from mem have "... = X \<union> (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
  text \<open>Finally, we show that this structure matches X + (Y + Z), concluding our proof of associativity.\<close>
  also have "... = X \<union> lift X (Y + Z)"
  proof-
    text \<open>Apply the definition of lift to the addition of Y and Z, showcasing how addition distributes over union within the lifting process.\<close>
    from add_eq_bin_union_lift have "lift X (Y + Z) = lift X (Y \<union> lift Y Z)" by simp
    text \<open>Leverage the property that lifting distributes over set union to decompose the lifting of the union into a union of lifts.\<close>
    also from lift_bin_union_eq_lift_bin_union_lift have "... = (lift X Y) \<union> lift X (lift Y Z)" by simp
    text \<open>Reframe the lift of the lift as an addition within a set comprehension, aligning with the definition of lift.\<close>
    also from lift_eq_repl_add have "... = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
    text \<open>Conclude that the lift of X over (Y + Z) is equivalent to the union of X lifted over Y and X added to each element resulting from Y added to z, for each z in Z.\<close>
    finally have "lift X (Y + Z) = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" .
    then show ?thesis by auto
  qed
  text \<open>Complete the proof by showing that the original expression simplifies to the associative form of addition, X + (Y + Z).\<close>
  also from add_eq_bin_union_lift have "... = X + (Y + Z)" by simp
  finally show ?case .
qed
text \<open>Demonstrating that the lift operation composed with itself can be simplified to a single lift operation that adds the two sets together first.\<close>
lemma lift_lift_eq_lift_add: "lift X (lift Y Z) = lift (X + Y) Z"
  by (simp add: lift_eq_image_add add_assoc)

text \<open>Shows that adding a successor to a set is equivalent to adding the set to the successor of another set, which aligns with the intuitive understanding of successor and addition in set theory.\<close>
lemma add_succ_eq_succ_add: "X + succ Y = succ (X + Y)"
  by (auto simp: succ_eq_add_one add_assoc)

text \<open>If an element belongs to a set, then adding that element to another set results in a set that is part of the lift of the second set over the first. This lemma links the concepts of addition and lift in set theory.\<close>
lemma add_mem_lift_if_mem_right:
  assumes "X \<in> Y"
  shows "Z + X \<in> lift Z Y"
  using assms by (auto simp: lift_eq_repl_add)

text \<open>Expanding the previous lemma, if an element is part of a set, then adding this element to another set results in an element of the addition of the two sets. It strengthens the connection between element membership and set addition.\<close>
corollary add_mem_add_if_mem_right:
  assumes "X \<in> Y"
  shows "Z + X \<in> Z + Y"
  using assms add_mem_lift_if_mem_right lift_subset_add by blast

text \<open>This lemma asserts that adding any set to another cannot result in a set that is a proper subset of the original set. It underscores a foundational property of set addition, ensuring that addition does not diminish the "size" of sets in terms of their membership hierarchy.\<close>
lemma not_add_lt_left [iff]: "\<not>(X + Y < X)"
proof
  text \<open>Assume, for the sake of contradiction, that adding Y to X results in a set that is a proper subset of X.\<close>
  assume "X + Y < X"
  then show "False"
  proof (induction Y rule: mem_induction)
    text \<open>We proceed by induction on the structure of Y.\<close>
    case (mem Y)
    then show ?case
    proof (cases "Y = {}")
      text \<open>If Y is empty, the base case trivially holds, as adding the empty set to any set X does not change X.\<close>
      case False
      text \<open>If Y is not empty, there exists an element y in Y.\<close>
      then obtain y where "y \<in> Y" by blast
      text \<open>By the properties of set addition, adding this element y to X results in an element of X + Y.\<close>
      with add_mem_add_if_mem_right have "X + y \<in> X + Y" by auto
      text \<open>However, by our assumption, this addition makes X + y a proper subset of X, which contradicts the definition of set addition.\<close>
      with mem.prems have "X + y < X" by (auto intro: lt_if_lt_if_mem)
      text \<open>This contradiction with the induction hypothesis on Y, asserting that no element of Y when added to X can result in a proper subset of X, leads us to conclude the assumption is false.\<close>
      with \<open>y \<in> Y\<close> mem.IH show ?thesis by auto
    qed simp
  qed
qed

text \<open>Adding Y to X does not result in a subset of X.\<close>
lemma not_add_mem_left [iff]: "X + Y \<notin> X"
  using subset_mem_trans_closure_self lt_iff_mem_trans_closure by auto

text \<open>X + Y is a subset of X iff Y is empty.\<close>
corollary add_subset_left_iff_right_eq_zero [iff]: "X + Y \<subseteq> X \<longleftrightarrow> Y = 0"
  by (subst add_eq_bin_union_repl_add) auto

text \<open>Lifting Y by X is a subset of X iff Y is empty.\<close>
corollary lift_subset_left_iff_right_eq_zero [iff]: "lift X Y \<subseteq> X \<longleftrightarrow> Y = 0"
  by (auto simp: lift_eq_repl_add)

text \<open>The transitive closure of X and its lift by Y are disjoint.\<close>
lemma mem_trans_closure_bin_inter_lift_eq_empty [simp]: "mem_trans_closure X \<inter> lift X Y = {}"
  by (auto simp: lift_eq_image_add simp flip: lt_iff_mem_trans_closure)

text \<open>X and its lift by Y are disjoint.\<close>
lemma bin_inter_lift_self_eq_empty [simp]: "X \<inter> lift X Y = {}"
  using mem_trans_closure_bin_inter_lift_eq_empty subset_mem_trans_closure_self by blast

text \<open>A set and its lift are disjoint.\<close>
corollary lift_bin_inter_self_eq_empty [simp]: "lift X Y \<inter> X = {}"
  using bin_inter_lift_self_eq_empty by blast

text \<open>Equal unions with lifts imply equal lifts.\<close>
lemma lift_eq_lift_if_bin_union_lift_eq_bin_union_lift:
  assumes "X \<union> lift X Y = X \<union> lift X Z"
  shows "lift X Y = lift X Z"
  using assms bin_inter_lift_self_eq_empty by blast


paragraph\<open>Proposition 3.4\<close>

text \<open>Injectivity of lift on the right implies sets are equal if their lifts are equal.\<close>
lemma lift_injective_right: "injective (lift X)"
proof (rule injectiveI)
  fix Y Z assume "lift X Y = lift X Z"
  then show "Y = Z"
  proof (induction Y arbitrary: Z rule: mem_induction)
    case (mem Y)
    {
      fix U V u assume uvassms: "U \<in> {Y, Z}" "V \<in> {Y, Z}" "U \<noteq> V" "u \<in> U"
      with mem have "X + u \<in> lift X V" by (auto simp: lift_eq_repl_add)
      then obtain v where "v \<in> V" "X + u = X + v" using lift_eq_repl_add by auto
      then have "X \<union> lift X u  = X \<union> lift X v" by (simp add: add_eq_bin_union_lift)
      with bin_inter_lift_self_eq_empty have "lift X u = lift X v" by blast
      with uvassms \<open>v \<in> V\<close> mem.IH have "u \<in> V" by auto
    }
    then show ?case by blast
  qed
qed

corollary lift_eq_lift_if_eq_right: "lift X Y = lift X Z \<Longrightarrow> Y = Z"
  using lift_injective_right by (blast dest: injectiveD)

corollary lift_eq_lift_iff_eq_right [iff]: "lift X Y = lift X Z \<longleftrightarrow> Y = Z"
  using lift_eq_lift_if_eq_right by auto

text \<open>Injectivity of addition on the right.\<close>
lemma add_injective_right: "injective ((+) X)"
  using lift_injective_right lift_eq_image_add by auto

corollary add_eq_add_if_eq_right: "X + Y = X + Z \<Longrightarrow> Y = Z"
  using add_injective_right by (blast dest: injectiveD)

corollary add_eq_add_iff_eq_right [iff]: "X + Y = X + Z \<longleftrightarrow> Y = Z"
  using add_eq_add_if_eq_right by auto

text \<open>A set is a member of the addition if and only if it is a member of the right addend.\<close>
lemma mem_if_add_mem_add_right:
  assumes "X + Y \<in> X + Z"
  shows "Y \<in> Z"
proof -
  have "X + Z = X \<union> lift X Z" by (simp only: add_eq_bin_union_lift)
  with assms have "X + Y \<in> lift X Z" by auto
  also have "... = {X + z| z \<in> Z}" by (simp add: lift_eq_image_add)
  finally have "X + Y \<in> {X + z| z \<in> Z}" .
  then show "Y \<in> Z" by blast
qed

corollary add_mem_add_iff_mem_right [iff]: "X + Y \<in> X + Z \<longleftrightarrow> Y \<in> Z"
  using mem_if_add_mem_add_right add_mem_add_if_mem_right by blast

text \<open>Monotonicity of lift and addition functions.\<close>
lemma mono_lift: "mono (lift X)"
  by (auto simp: lift_eq_repl_add)

text \<open>Subset relations between lifted and added sets.\<close>
lemma subset_if_lift_subset_lift: "lift X Y \<subseteq> lift X Z \<Longrightarrow> Y \<subseteq> Z"
  by (auto simp: lift_eq_repl_add)

corollary lift_subset_lift_iff_subset: "lift X Y \<subseteq> lift X Z \<longleftrightarrow> Y \<subseteq> Z"
  using subset_if_lift_subset_lift mono_lift[of X] by (auto del: subsetI)

lemma mono_add: "mono ((+) X)"
proof (rule monoI[of "(+) X", simplified])
  fix Y Z assume "Y \<subseteq> Z"
  then have "lift X Y \<subseteq> lift X Z" by (simp only: lift_subset_lift_iff_subset)
  then show "X + Y \<subseteq> X + Z" by (auto simp: add_eq_bin_union_lift)
qed

lemma subset_if_add_subset_add:
  assumes "X + Y \<subseteq> X + Z"
  shows "Y \<subseteq> Z"
proof-
  have "X + Z = X \<union> lift X Z" by (simp only: add_eq_bin_union_lift)
  with assms have "lift X Y \<subseteq> X \<union> lift X Z" by (auto simp: add_eq_bin_union_lift)
  moreover have "lift X Y \<inter> X = {}" by (fact lift_bin_inter_self_eq_empty)
  ultimately have "lift X Y \<subseteq> lift X Z" by blast
  with lift_subset_lift_iff_subset show ?thesis by simp
qed

corollary add_subset_add_iff_subset [iff]: "X + Y \<subseteq> X + Z \<longleftrightarrow> Y \<subseteq> Z"
  using subset_if_add_subset_add mono_add[of X] by (auto del: subsetI)

text \<open>Transitive closure of addition is the union of the closures of its operands.\<close>
lemma mem_trans_closure_add_eq_mem_trans_closure_bin_union:
  "mem_trans_closure (X + Y) = mem_trans_closure X \<union> lift X (mem_trans_closure Y)"
proof (induction Y)
  case (mem Y)
  have "mem_trans_closure (X + Y) = (X + Y) \<union> (\<Union>z \<in> X + Y. mem_trans_closure z)"
    by (subst mem_trans_closure_eq_bin_union_idx_union) simp
  also have "... = mem_trans_closure X \<union> lift X Y \<union> (\<Union>y \<in> Y. mem_trans_closure (X + y))"
    (is "_ = ?unions \<union> _")
    by (auto simp: lift_eq_repl_add idx_union_bin_union_dom_eq_bin_union_idx_union
      add_eq_bin_union_lift[of X Y] mem_trans_closure_eq_bin_union_idx_union[of X])
  also have "... = ?unions \<union> (\<Union>y \<in> Y. mem_trans_closure X \<union> lift X (mem_trans_closure y))"
    using mem.IH by simp
  also have "... = ?unions \<union> (\<Union>y \<in> Y. lift X (mem_trans_closure y))" by auto
  also have "... = mem_trans_closure X \<union> lift X (Y \<union> (\<Union>y \<in> Y. mem_trans_closure y))"
    by (simp add: lift_bin_union_eq_lift_bin_union_lift
      lift_union_eq_idx_union_lift bin_union_assoc mem_trans_closure_eq_bin_union_idx_union[of X])
  also have "... = mem_trans_closure X \<union> lift X (mem_trans_closure Y)"
    by (simp flip: mem_trans_closure_eq_bin_union_idx_union)
  finally show ?case .
qed

text \<open>Inequalities and their implications in the context of addition.\<close>
corollary lt_add_if_lt_left:
  assumes "X < Y"
  shows "X < Y + Z"
  using assms mem_trans_closure_add_eq_mem_trans_closure_bin_union
  by (auto simp: lt_iff_mem_trans_closure)

corollary add_lt_add_if_lt_right:
  assumes "X < Y"
  shows "Z + X < Z + Y"
  using assms mem_trans_closure_add_eq_mem_trans_closure_bin_union
  by (auto simp: lt_iff_mem_trans_closure lift_eq_image_add)

corollary lt_add_if_eq_add_if_lt:
  assumes "x < X"
  and "Y = Z + x"
  shows "Y < Z + X"
  using assms add_lt_add_if_lt_right by simp

text \<open>Conditions under which addition leads to strict inequalities.\<close>
corollary lt_addE:
  assumes "X < Y + Z"
  obtains (lt_left) "X < Y" | (lt_eq) z where "z < Z" "X = Y + z"
  using assms mem_trans_closure_add_eq_mem_trans_closure_bin_union
  by (auto simp: lt_iff_mem_trans_closure lift_eq_image_add)

corollary lt_add_iff_lt_or_lt_eq: "X < Y + Z \<longleftrightarrow> X < Y \<or> (\<exists>z. z < Z \<and> X = Y + z)"
  by (blast intro: lt_add_if_lt_left add_lt_add_if_lt_right elim: lt_addE)

text \<open>Adding a non-empty set to another strictly increases its "size" in terms of membership.\<close>
lemma lt_add_self_if_ne_zero [simp]:
  assumes "Y \<noteq> 0"
  shows "X < X + Y"
  using assms by (intro lt_add_if_eq_add_if_lt) auto

text \<open>A set is always less than or equal to itself added with another set.\<close>
corollary le_self_add [iff]: "X \<le> X + Y"
  using lt_add_self_if_ne_zero le_iff_lt_or_eq by (cases "Y = 0") auto


end
