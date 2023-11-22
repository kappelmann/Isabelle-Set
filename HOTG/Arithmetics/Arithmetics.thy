theory Arithmetics
  imports
    Functions_Restrict
    Mem_Trans
    Union_Intersection
    Transport.HOL_Syntax_Bundles_Groups
    Transport.HOL_Syntax_Bundles_Orders
    Foundation
    Axioms
begin

paragraph \<open>Summary\<close>
text \<open>Translation of generalised arithmetics from
\<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.\<close>

unbundle no_HOL_ascii_syntax
unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

(*TODO Kevin: rename to binary_relation_restrict*)
unbundle no_restrict_syntax

unbundle no_HOL_groups_syntax

abbreviation "zero_set \<equiv> {}"
abbreviation "one_set \<equiv> {zero_set}"

bundle hotg_set_zero_syntax begin notation zero_set ("0") end
bundle no_hotg_set_zero_syntax begin no_notation zero_set ("0") end

bundle hotg_set_one_syntax begin notation one_set ("1") end
bundle no_hotg_set_one_syntax begin no_notation one_set ("1") end

unbundle
  hotg_set_zero_syntax
  hotg_set_one_syntax


overloading
  fun_restrict_set \<equiv> "fun_restrict :: (set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'a"
begin
  definition "fun_restrict_set f X x \<equiv> if x \<in> X then f x else undefined"
end

lemma fun_restrict_set_eq_fun_restrict [simp]: "(f :: set \<Rightarrow> 'a)\<restriction>\<^bsub>X\<^esub> = f\<restriction>\<^bsub>mem_of X\<^esub>"
  unfolding fun_restrict_set_def by auto

axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f ((transrec f)\<restriction>\<^bsub>X\<^esub>) X"

definition "image f A \<equiv> {f x | x \<in> A}"

lemma image_eq_repl [simp]: "image f A = {f x | x \<in> A}"
  unfolding image_def by simp

lemma repl_fun_restrict_mem_eq_repl [simp]: "{f\<restriction>\<^bsub>A\<^esub> x | x \<in> A} = {f x | x \<in> A}"
  by simp


paragraph \<open>Transitive Closure\<close>

definition "mem_trans_closure \<equiv> transrec (\<lambda>f x. x \<union> \<Union>(image f x))"

lemma mem_trans_closure_eq_bin_union_repl:
  "mem_trans_closure X = X \<union> \<Union>{mem_trans_closure x | x \<in> X}"
  by (simp add: mem_trans_closure_def transrec_eq[where ?X=X])

lemma subset_mem_trans_closure: "X \<subseteq> mem_trans_closure X"
  by (auto simp:mem_trans_closure_eq_bin_union_repl[where ?X= X])

corollary mem_mem_trans_closure_if_mem: "X \<in> Y \<Longrightarrow> X \<in> mem_trans_closure Y"
  using subset_mem_trans_closure by blast

lemma mem_trans_closure_empty_eq_empty [simp]: "mem_trans_closure {} = {}"
  by (simp add: mem_trans_closure_eq_bin_union_repl[where ?X="{}"])

(*TODO Kevin: rename mem_trans to mem_trans_closed*)
lemma mem_trans_mem_trans_closure: "mem_trans (mem_trans_closure X)"
proof (induction X rule: mem_induction)
  case (mem X)
  show ?case
  proof (rule mem_transI')
    fix x y assume "x \<in> mem_trans_closure X" "y \<in> x"
    then have "x \<in> X \<union> \<Union>{mem_trans_closure x | x \<in> X}" (is "_ \<in> _ \<union> ?tmem")
      by (simp flip: mem_trans_closure_eq_bin_union_repl)
    then consider (memX) "x \<in> X" | (memtmem) "x \<in> ?tmem" by blast
    then show "y \<in> mem_trans_closure X"
    proof cases
      case memX
      moreover have "y \<in> mem_trans_closure x" using \<open>y \<in> x\<close> subset_mem_trans_closure by blast
      ultimately show ?thesis by (subst mem_trans_closure_eq_bin_union_repl) blast
    next
      case memtmem
      then obtain z where "x \<in> mem_trans_closure z" "z \<in> X" by auto
      with \<open>y \<in> x\<close> mem.IH \<open>z \<in> X\<close> show ?thesis by (subst mem_trans_closure_eq_bin_union_repl) blast
    qed
  qed
qed

paragraph \<open>Less-Than Order\<close>

definition "lt X Y \<equiv> X \<in> mem_trans_closure Y"

bundle hotg_lt_syntax begin notation lt (infix "<" 60) end
bundle no_hotg_lt_syntax begin no_notation lt (infix "<" 60) end
unbundle hotg_lt_syntax

lemma lt_iff_mem_trans_closure: "X < Y \<longleftrightarrow> X \<in> mem_trans_closure Y"
  unfolding lt_def by simp

lemma lt_if_lt_if_mem [trans]:
  assumes "y \<in> Y"
  and "Y < X"
  shows "y < X"
  using assms mem_trans_mem_trans_closure unfolding lt_iff_mem_trans_closure by auto

find_theorems name:"not_mem_if_eq"

lemma not_mem_trans_closure [iff]: "X \<notin> mem_trans_closure X"
proof
  assume "X \<in> mem_trans_closure X"
  hence "X \<in> X \<union> \<Union>{mem_trans_closure x | x \<in> X}" 
    by (simp add:mem_trans_closure_eq_bin_union_repl[where ?X =X])
  then consider (self) "X \<in> X" | (union) "X \<in> \<Union>{mem_trans_closure x | x \<in> X}" by blast
  then show False
  proof cases
    case union
      then show ?thesis
      proof (induction X rule: mem_induction)
        case (mem X)
        then obtain y where "y \<in> X" and "X \<in> mem_trans_closure y" by blast
        then have "X < y" by (simp add:lt_iff_mem_trans_closure)
        then have "y < y" using  \<open>y \<in> X\<close> by (auto simp:lt_if_lt_if_mem)
        then have inTC:"y \<in> mem_trans_closure y" by (simp add: lt_iff_mem_trans_closure)
        also have uni:"mem_trans_closure y = y \<union> \<Union>{mem_trans_closure yy | yy \<in> y}"
          by (simp add:mem_trans_closure_eq_bin_union_repl[where ?X =y])
        also have notself:"y \<notin> y" by (auto simp:not_mem_if_eq)
        with uni inTC have "y \<in> X \<Longrightarrow>  y \<in> \<Union>{mem_trans_closure yy | yy \<in> y}" by auto
        with mem show False sorry
      qed
  qed (auto simp:not_mem_if_eq)
qed

lemma not_lt_self [iff]: "\<not>(X < X)"
  using lt_iff_mem_trans_closure by auto


paragraph\<open>Addition\<close>

definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"

bundle hotg_add_syntax begin notation add (infixl "+" 65) end
bundle no_hotg_add_syntax begin no_notation add (infixl "+" 65) end
unbundle hotg_add_syntax

lemma add_eq_bin_union_image_add: "X + Y = X \<union> image ((+) X) Y"
  unfolding add_def by (simp add: transrec_eq)

lemma add_eq_bin_union_repl_add: "X + Y = X \<union> {X + y | y \<in> Y}"
  unfolding add_def by (simp add: transrec_eq)

lemma mem_addE:
  assumes "x \<in> (Y + Z)"
  obtains "x \<in> Y" | z where "z \<in> Z" "x = Y + z"
  using assms by (auto simp: add_eq_bin_union_image_add[of Y Z])

definition "lift X \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma lift_eq_repl_add: "lift X Y = {X + y | y \<in> Y}"
  using lift_eq_image_add by simp

lemma add_eq_bin_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (subst add_eq_bin_union_image_add) simp

lemma lift_bin_union_eq_lift_bin_union_lift: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

lemma lift_union_eq_union_repl_lift: "lift X (\<Union>Y) = \<Union>{lift X y | y \<in> Y}"
  by (auto simp: lift_eq_image_add)

lemma idx_union_add_eq_add_idx_union:
  "Y \<noteq> {} \<Longrightarrow> (\<Union>y \<in> Y. X + f y) = X + (\<Union>y \<in> Y. f y)"
  by (simp add: lift_union_eq_union_repl_lift add_eq_bin_union_lift)

lemma lift_zero_eq_zero [simp]: "lift X {} = {}"
  by (auto simp: lift_eq_image_add)

lemma add_zero_eq_self [simp]: "X + {} = X"
  unfolding add_eq_bin_union_lift by simp

lemma lift_one_eq_singleton_self [simp]: "lift X 1 = {X}"
  unfolding lift_def by simp

definition "succ X \<equiv> X + 1"

lemma succ_eq_add_one: "succ X = X + 1"
  unfolding succ_def by simp

lemma insert_self_eq_add_one: "insert X X = X + 1"
  by (auto simp: add_eq_bin_union_lift succ_eq_add_one)

lemma lift_singleton_eq_singleton_add: "lift X {Z} = {X + Z}"
  unfolding lift_def by simp

lemma lift_singleton_eq_singleton_bin_union_lift: "lift X {Z} = {X \<union> lift X Z}"
  by (simp only: lift_singleton_eq_singleton_add add_eq_bin_union_lift)

lemma lift_bin_union_singleton_eq_lift_bin_union:
  "lift X (insert Y Z) = lift X Z \<union> {X \<union> lift X Y}"
  by (simp flip: lift_singleton_eq_singleton_bin_union_lift lift_bin_union_eq_lift_bin_union_lift)

lemma add_insert_eq_insert_add: "X + insert Y Z = insert (X + Y) (X + Z)"
  by (auto simp: lift_bin_union_singleton_eq_lift_bin_union add_eq_bin_union_lift)


paragraph\<open>Proposition 3.3\<close>

lemma zero_add_eq_self [simp]: "{} + X = X"
proof (induct X rule: mem_induction)
  case (mem X)
  have "{} + X = lift {} X" by (simp add: add_eq_bin_union_lift)
  also from mem have "... = X" by (simp add: lift_eq_image_add)
  finally show ?case .
qed

corollary lift_zero_eq_self [simp]: "lift {} X = X"
  by (simp add: lift_eq_image_add)

corollary add_eq_zeroE [elim]:
  assumes "X + Y = 0"
  obtains "X = 0" "Y = 0"
  using assms by (auto simp: add_eq_bin_union_lift)

corollary add_eq_zero_iff_and_eq_zero [iff]: "X + Y = 0 \<longleftrightarrow> X = 0 \<and> Y = 0" by auto

lemma add_assoc: "(X + Y) + Z = X + (Y + Z)"
proof(induct Z rule: mem_induction)
  case (mem Z)
  from add_eq_bin_union_lift have "(X + Y) + Z = (X + Y) \<union> (lift (X + Y) Z)" by simp
  also from lift_eq_repl_add have "... = (X + Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from add_eq_bin_union_lift have "... = X \<union> (lift X Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from mem have "... = X \<union> (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
  also have "... = X \<union> lift X (Y + Z)"
  proof-
    have "lift X (Y + Z) = lift X (Y \<union> lift Y Z)"
      by (simp add: add_eq_bin_union_lift)
    also have "... = (lift X Y) \<union> lift X (lift Y Z)"
      by (simp add: lift_bin_union_eq_lift_bin_union_lift)
    also have "... = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}"
      by (simp add: lift_eq_repl_add)
    finally have "lift X (Y + Z) = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" .
    then show ?thesis by auto
  qed
    also from add_eq_bin_union_lift have "... = X + (Y + Z)" by simp
    finally show ?case .
qed

lemma lift_lift_eq_lift_add: "lift X (lift Y Z) = lift (X + Y) Z"
  by (simp add: lift_eq_image_add add_assoc)

lemma add_succ_eq_succ_add: "X + succ Y = succ (X + Y)"
  by (auto simp: succ_eq_add_one add_assoc)

lemma add_mem_add_if_mem:
  assumes "Y \<in> Z"
  shows "X + Y \<in> X + Z"
proof-
  from assms have "X + Y \<in> {X + z| z \<in> Z}" by auto
  then show ?thesis by (auto simp: lift_eq_repl_add[of X Z] add_eq_bin_union_lift)
qed

lemma not_add_lt_left [iff]: "\<not>(X + Y < X)"
proof
  assume "X + Y < X"
  then show "False"
  proof (induction Y rule: mem_induction)
    case (mem Y)
    then show ?case
    proof (cases "Y = {}")
      case False
      then obtain y where sub: "y \<in> Y" by blast
      with add_mem_add_if_mem mem have sub_in: "X + y \<in> X + Y" by auto
      with mem have bla: "X + y < X" by (auto intro: lt_if_lt_if_mem)
      with sub mem.IH show ?thesis by auto
    qed simp
  qed
qed

lemma not_add_mem_left [iff]: "\<not>(X + Y \<in> X)"
  using subset_mem_trans_closure lt_iff_mem_trans_closure by auto

lemma mem_trans_closure_bin_inter_lift_eq_empty [simp]: "mem_trans_closure X \<inter> lift X Y = {}"
  by (auto simp: lift_eq_image_add simp flip: lt_iff_mem_trans_closure)

lemma bin_inter_lift_self_eq_empty [simp]: "X \<inter> lift X Y = {}"
  using mem_trans_closure_bin_inter_lift_eq_empty subset_mem_trans_closure by blast

lemma bin_inter_lift_self_eq_empty_assoc [simp]: "lift X Y \<inter> X = {}"
  using mem_trans_closure_bin_inter_lift_eq_empty subset_mem_trans_closure by blast

lemma lift_eq_lift_if_bin_union_lift_eq_bin_union_lift:
  assumes "X \<union> lift X Y = X \<union> lift X Z"
  shows "lift X Y = lift X Z"
  using assms bin_inter_lift_self_eq_empty by blast

paragraph\<open>Proposition 3.4\<close>

lemma lift_right_inective:
  assumes "lift X Y = lift X Z"
  shows "Y = Z"
using assms
proof(induction Y arbitrary: Z rule: mem_induction)
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

lemma add_right_inective: "X + Y = X + Z \<Longrightarrow> Y = Z"
  by (subst (asm) add_eq_bin_union_lift)+
  (fast dest: lift_eq_lift_if_bin_union_lift_eq_bin_union_lift lift_right_inective)

lemma add_mem_add_iff_mem: "X + Y \<in> X + Z \<longleftrightarrow> Y \<in> Z"
proof (rule iffI)
  assume left:"X + Y \<in> X + Z"
  thus "Y \<in> Z"
  proof-
    have "X + Y \<in> X + Z"  by (simp add:left)
    also have "... = X \<union> lift X Z"
      by (auto simp: add_eq_bin_union_lift)
    finally have "X + Y \<in> X \<union> lift X Z" .
    have not_add_lt_left: "\<not> X + Y \<in> X" by auto
    with \<open>X + Y \<in> X \<union> lift X Z\<close> have "X + Y \<in> lift X Z" by auto
    have "lift X Z = {X + z| z \<in> Z}" by (simp add:lift_eq_image_add)
    then have "X + Y \<in> {X + z| z \<in> Z}" using \<open>X + Y \<in> lift X Z\<close> by simp
    then obtain z where sub: "z \<in> Z" "X + Y = X + z" by blast
    then have "Y = z" by (auto simp: add_right_inective)
    then have "Y \<in> Z" using sub by simp
    then show ?thesis .
  qed
next
  assume "Y \<in> Z"
  thus "X + Y \<in> X + Z"
    by (simp add: add_mem_add_if_mem)
qed

lemma kkk:
  assumes "A \<subseteq> B \<union> C" "A \<inter> B = {}"
  shows "A \<subseteq> C"
proof
  fix a
  assume "a \<in> A"
  with assms(1) have "a \<in> B \<union> C" by blast
  then show "a \<in> C" 
  proof
    assume "a \<in> B"
    with assms(2) and \<open>a \<in> A\<close> have "a \<in> {}" by blast
    then show "a \<in> C" by simp
  qed auto
qed

lemma  sss: "lift X Y \<subseteq> lift X Z \<longleftrightarrow> Y \<subseteq> Z"
proof(rule iffI)
  assume left:"lift X Y \<subseteq> lift X Z"
  then have "{X + y|y \<in> Y} \<subseteq> {X + z|z \<in> Z}" 
    by (auto simp: lift_eq_repl_add)
  then show "Y \<subseteq> Z" sorry
(*
  proof
    fix y assume "y \<in> Y"
    then have "X + y \<in> {X + z|z \<in> Z}" 
      using \<open>{X + y|y \<in> Y} \<subseteq> {X + z|z \<in> Z}\<close> by auto
    then obtain z where "X + y = X + z" and "z \<in> Z" by auto
    then have "y = z" by (auto simp:add_right_inective)
    then have "y \<in> Y \<Longrightarrow> y \<in> Z " using \<open>z \<in> Z\<close> by simp
    then show "Y \<subseteq> Z"  
  qed
*)
qed (auto simp: lift_eq_image_add)

corollary add_less_cancel_left [iff]:
  "X + Y \<subseteq> X + Z \<longleftrightarrow> Y \<subseteq> Z"
proof(rule iffI)
 assume left:"X + Y \<subseteq> X + Z"
  thus "Y \<subseteq> Z" 
  proof-
    have "X + Y \<subseteq> X + Z"  by (simp add:left)
    also have "... = X \<union> lift X Z"
      by (auto simp: add_eq_bin_union_lift)
    finally have "X + Y \<subseteq> X \<union> lift X Z" .
    then have sub:"(lift X Y) \<subseteq> X \<union> (lift X Z)" 
      by (auto simp: add_eq_bin_union_lift)
    have "lift X Y \<inter> X = {}" by simp
    with sub have "lift X Y \<subseteq> lift X Z"  by (auto simp:kkk)
      then show ?thesis by (simp add:sss)
    qed
next
  assume "Y \<subseteq> Z"
  thus "X + Y \<subseteq> X + Z" 
  proof-
    have "lift X Y \<subseteq> lift X Z" using \<open>Y \<subseteq> Z\<close> by (simp add:sss)
    then show ?thesis 
      by (auto simp: add_eq_bin_union_lift)
  qed
qed



paragraph\<open>Multiplication\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

lemma mul_eq_union_repl_lift_mul: "X * Y = \<Union>{lift (X * y) X | y \<in> Y}"
  by (auto simp:mul_def transrec_eq)

lemma elts_multE:
  assumes "z \<in> (X * Y)"
  obtains u v where "u \<in> x" "v \<in> y" "z = x * v + u"
  sorry

lemma mul_zero_eq_zero: "x * {} = {}"
  unfolding mul_def by (auto simp: transrec_eq)

lemma mul_one_same: "x * 1 = x"
  unfolding mul_def by (auto simp: transrec_eq)

lemma mul_set_one_eq_lift: "X * {1} = lift X X"
proof-
  have 1:"\<And>Y.  X * Y = \<Union>{lift (X * y) X | y \<in> Y }"
    by (simp add:mul_def transrec_eq)
  have "X * {1} = \<Union>{lift (X * y) X | y \<in> {1}}"
    by (simp add: mul_eq_union_repl_lift_mul[where ?Y="{1}"])
  also have "... = \<Union>{lift (X * 1) X }" by auto
  also have "... = \<Union>{lift X X}"
    by (simp add: mul_one_same)
  also have "... = lift X X" by auto
  finally have "X * {1} = lift X X" .
    then show ?thesis by simp
  qed

lemma mul_two_eq_add: "X * {1, {}} = X + X"
proof-
  have "X * {1, {}} = \<Union>{lift (X * y) X | y \<in> {1, {}} }"
    by (simp add: mul_eq_union_repl_lift_mul[where ?Y="{1,0}"])
  also have "... = (lift (X*1) X) \<union> (lift (X*{}) X)" by auto
  also have "... = lift X X \<union> lift {} X" by (simp add: mul_one_same mul_zero_eq_zero)
  also have "... = X \<union> lift X X" by auto
  also have "... = X + X" by (simp add: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma mul_insert_eq_bin_union_mul_lift: 
  "X * (insert Y Z) = (X * Y) \<union> lift (X * Z) X"
  sorry

lemma  mul_mem_add_one_eq_mul_add:
  "X * (Y + 1) = X * Y + X"
proof -
  have "insert Y Y = Y + 1"
    by (simp add: insert_self_eq_add_one[where ?X = Y])
  also have "X * (insert Y Y) = (X * Y) \<union> lift (X * Y) X"
    by (simp add: mul_insert_eq_bin_union_mul_lift)
  then have " X * (insert Y Y) = (X * Y) + X"
    by (simp add: add_eq_bin_union_lift)
  then show "X * (Y + 1) = (X * Y) + X"
    using \<open>insert Y Y = Y + 1\<close> by simp
qed

end
