\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Linghan Fang"\<close>
section \<open>Transfinite Recursion\<close>
theory HOTG_Transfinite_Recursion
  imports
    HOTG_Less_Than 
    HOTG_Ordinals_Base
    HOTG_Functions_Restrict
    Transport.Functions_Restrict
    Transport.Binary_Relations_Transitive
begin

unbundle no_HOL_order_syntax

paragraph \<open>Summary\<close>
text \<open>We take the axiomatization of transfinite recursion from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L1151\<close>.\<close>

definition "wellfounded r \<longleftrightarrow> (\<forall>P x. P x \<longrightarrow> (\<exists>m. P m \<and> (\<forall>y. r y m \<longrightarrow> \<not> P y)))"

lemma wellfoundedI:
  assumes "\<And>P x. P x \<Longrightarrow> (\<exists>m. P m \<and> (\<forall>y. r y m \<longrightarrow> \<not> P y))"
  shows "wellfounded r"
  using assms unfolding wellfounded_def by blast

lemma wellfoundedE:
  assumes "wellfounded r" "P x"
  obtains m where "P m" "\<And>y. r y m \<Longrightarrow> \<not> P y"
  using assms unfolding wellfounded_def by blast

lemma wellfounded_induct:
  assumes wf: "wellfounded r" 
  assumes step: "\<And>x. (\<And>y. r y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
proof (rule ccontr)
  assume "\<not> P x"
  then obtain m where "\<not> P m" "\<And>y. r y m \<longrightarrow> P y" 
    using wf wellfoundedE[where P="\<lambda>x. \<not> P x"] by auto
  then show "False" using step by auto
qed

locale wellfounded_rel =
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes wellfounded: "wellfounded (\<prec>)"
begin

lemma r_induct [case_names step]:
  assumes "\<And>x. (\<And>y. y \<prec> x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wellfounded_induct[OF wellfounded] assms by blast

definition "ord_restrict f x = (\<lambda>y. if y \<prec> x then f y else undefined)"

lemma ord_restrict_eq_if: "ord_restrict f x y = (if y \<prec> x then f y else undefined)"
  unfolding ord_restrict_def by auto

lemma ord_restrict_eq:
  assumes "y \<prec> x"
  shows "ord_restrict f x y = f y"
  using assms unfolding ord_restrict_def by auto

lemma ord_restrict_eq_if_not:
  assumes "\<not> y \<prec> x"
  shows "ord_restrict f x y = undefined"
  using assms unfolding ord_restrict_def by auto

lemma ord_restrict_eq_ord_restrict:
  assumes "\<forall>y. y \<prec> x \<longrightarrow> f y = g y"
  shows "ord_restrict f x = ord_restrict g x"
  using assms unfolding ord_restrict_def by auto

end

locale wellfounded_trans_rel = wellfounded_rel +
  assumes trans: "transitive (\<prec>)"
begin

definition "is_recfun X R f \<longleftrightarrow> (\<forall>x. f x = (if x \<prec> X then R (ord_restrict f x) x else undefined))"

definition "the_recfun X R = (THE f. is_recfun X R f)"

definition "wftrec R X = R (ord_restrict (the_recfun X R) X) X"

lemma is_recfunE:
  assumes "is_recfun X R f"
  shows "\<And>x. x \<prec> X \<Longrightarrow> f x = R (ord_restrict f x) x" "\<And>x. \<not> x \<prec> X \<Longrightarrow> f x = undefined"
  using assms unfolding is_recfun_def by auto

lemma recfuns_agree_over_intersection:
  assumes "is_recfun X R f" "is_recfun Y R g" "Z \<prec> X" "Z \<prec> Y"
  shows "f Z = g Z"
  using \<open>Z \<prec> X\<close> \<open>Z \<prec> Y\<close>
proof (induction Z rule: r_induct)
  case (step Z)
  have "f z = g z" if "z \<prec> Z" for z using step.IH that trans step.prems by blast
  then have "ord_restrict f Z = ord_restrict g Z" using ord_restrict_eq_ord_restrict by auto
  moreover have "f Z = R (ord_restrict f Z) Z" "g Z = R (ord_restrict g Z) Z" 
    using assms step.prems is_recfunE by auto
  ultimately show ?case by auto
qed

corollary recfun_unique:
  assumes "is_recfun X R f" "is_recfun X R g"
  shows "f = g"
  using assms recfuns_agree_over_intersection[OF assms] unfolding is_recfun_def by auto

corollary is_recfun_the_recfun_if_is_recfun:
  assumes "is_recfun X R f"
  shows "is_recfun X R (the_recfun X R)"
proof -
  have "\<exists>!g. is_recfun X R g" using assms recfun_unique by auto
  from theI'[OF this] show ?thesis unfolding the_recfun_def by auto
qed

corollary recfun_restrict_eq_recfun_restrict_if_mem:
  assumes recfuns: "is_recfun x R f" "is_recfun X R g" and "x \<prec> X"
  shows "ord_restrict f x = ord_restrict g x"
proof -
  have "f y = g y" if "y \<prec> x" for y
    using recfuns_agree_over_intersection[OF recfuns] \<open>y \<prec> x\<close> \<open>x \<prec> X\<close> trans by blast
  then show ?thesis using ord_restrict_eq_ord_restrict by auto
qed

lemma recfun_exists: "\<exists>f. is_recfun X R f"
proof (induction X rule: r_induct)
  case (step X)
  have is_recfun: "is_recfun x R (the_recfun x R)" if "x \<prec> X" for x
    using is_recfun_the_recfun_if_is_recfun step.IH that by blast
  define f where "f x = (if x \<prec> X then R (ord_restrict (the_recfun x R) x) x else undefined)" for x
  have "ord_restrict f x = ord_restrict (the_recfun x R) x" if "x \<prec> X" for x
  proof -
    have "f y = (the_recfun x R) y" if "y \<prec> x" for y
    proof -
      have "is_recfun y R (the_recfun y R)" "is_recfun x R (the_recfun x R)" 
        using is_recfun \<open>x \<prec> X\<close> \<open>y \<prec> x\<close> trans by auto
      from recfun_restrict_eq_recfun_restrict_if_mem[OF this]
      have "ord_restrict (the_recfun y R) y = ord_restrict (the_recfun x R) y"
        using \<open>y \<prec> x\<close> by auto
      moreover have "f y = R (ord_restrict (the_recfun y R) y) y" 
        using f_def \<open>y \<prec> x\<close> \<open>x \<prec> X\<close> trans by auto
      moreover have "R (ord_restrict (the_recfun x R) y) y = (the_recfun x R) y" 
        using is_recfunE(1) \<open>y \<prec> x\<close> is_recfun \<open>x \<prec> X\<close> by force
      ultimately show ?thesis by auto
    qed
    then show ?thesis using ord_restrict_eq_ord_restrict by auto
  qed
  then have "is_recfun X R f" using is_recfun_def f_def by force
  then show ?case by auto
qed

corollary is_recfun_the_recfun: "is_recfun X R (the_recfun X R)"
  using is_recfun_the_recfun_if_is_recfun recfun_exists by blast

theorem wftrec_eq: "wftrec R X = R (ord_restrict (wftrec R) X) X"
proof -
  have "(the_recfun X R) x = wftrec R x" if "x \<prec> X" for x
  proof -
    have "(the_recfun X R) x = R (ord_restrict (the_recfun X R) x) x"
      using is_recfunE(1) is_recfun_the_recfun \<open>x \<prec> X\<close> by blast
    moreover have "ord_restrict (the_recfun x R ) x = ord_restrict (the_recfun X R) x"
      using recfun_restrict_eq_recfun_restrict_if_mem[OF is_recfun_the_recfun is_recfun_the_recfun] 
      using \<open>x \<prec> X\<close> by auto
    ultimately show ?thesis unfolding wftrec_def by auto
  qed
  then have "ord_restrict (the_recfun X R) X = ord_restrict (wftrec R) X"
    using ord_restrict_eq_ord_restrict by auto
  then show ?thesis using wftrec_def[of R X] by auto
qed

end

lemma wellfounded_lt: "wellfounded (<)"
  by (auto intro!: wellfoundedI elim: lt_minimal_set_witnessE)

context 
begin

interpretation wellfounded_trans_rel "(<)"
  using wellfounded_lt transitive_lt by unfold_locales auto

definition transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" where
"transrec R = wftrec (\<lambda>f X. R (fun_restrict f X) X)"

corollary transrec_eq: "transrec R X = R (fun_restrict (transrec R) X) X"
proof -
  have fun_restrict_ord_restrict: "fun_restrict (ord_restrict f X) X = fun_restrict f X" for f
    unfolding fun_restrict_set_eq_fun_restrict_pred fun_restrict_eq_if ord_restrict_eq_if
    using lt_if_mem by auto
  have "transrec R X = R (fun_restrict (ord_restrict (transrec R) X) X) X"
    using wftrec_eq[of "\<lambda>f X. R (fun_restrict f X) X"] transrec_def[of R, symmetric] by auto
  then show ?thesis unfolding fun_restrict_ord_restrict by simp
qed

end

(*
  We use transrec to define the transitive closure of a general relation (\<prec>). The fact that the 
  transitive closure of a wellfounded relation is itsself wellfounded can be used to remove the
  transitivity assumption of wftrec. See wfrec
*)

(* Composition of a relation with itsself. The parameter n should be thought of as a natural number. *)
definition "rel_pow r = transrec (\<lambda>r_pow n x y. r x y \<or> (\<exists>m u. m \<in> n \<and> r_pow m x u \<and> r u y))"

lemma rel_pow_iff: "rel_pow r n x y \<longleftrightarrow> r x y \<or> (\<exists>m u. m \<in> n \<and> rel_pow r m x u \<and> r u y)"
  using transrec_eq[of "\<lambda>r_pow n x y. r x y \<or> (\<exists>m u. m \<in> n \<and> r_pow m x u \<and> r u y)" n] 
  unfolding rel_pow_def[symmetric] by auto

lemma rel_powE:
  assumes "rel_pow r n x y"
  obtains (rel) "r x y" | (trans) m u where "m \<in> n" "rel_pow r m x u" "r u y"
  using assms unfolding rel_pow_iff[of r n x y] by blast

definition "trans_closure r x y \<longleftrightarrow> (\<exists>n. rel_pow r n x y)"

lemma transitive_trans_closure: "transitive (trans_closure r)"
proof -
  have "trans_closure r x z" if "trans_closure r x y" "rel_pow r n y z" for n x y z using that
  proof (induction n arbitrary: y z rule: mem_induction)
    case (mem n)
    consider "r y z" | m u where "m \<in> n" "rel_pow r m y u" "r u z"
      using \<open>rel_pow r n y z\<close> by (blast elim: rel_powE)
    then show ?case
    proof cases
      case 1
      from \<open>trans_closure r x y\<close> obtain k where "rel_pow r k x y" unfolding trans_closure_def by auto
      from \<open>r y z\<close> have "rel_pow r (succ k) x z"
        using rel_pow_iff[of r _ x z] \<open>rel_pow r k x y\<close> succ_eq_insert_self by blast
      then show ?thesis unfolding trans_closure_def by blast
    next
      case 2
      have "trans_closure r x u"
        using mem.IH \<open>m \<in> n\<close> \<open>trans_closure r x y\<close> \<open>rel_pow r m y u\<close> by blast
      then obtain k where "rel_pow r k x u" unfolding trans_closure_def by auto
      then have "rel_pow r (succ k) x z" 
        using \<open>r u z\<close> rel_pow_iff[of r _ x z] succ_eq_insert_self by blast
      then show ?thesis unfolding trans_closure_def by blast
    qed
  qed
  then have "trans_closure r x z" if "trans_closure r x y" "trans_closure r y z" for x y z
    using that unfolding trans_closure_def[of r y z] by blast
  then show ?thesis by auto
qed

lemma trans_closure_if_rel: "r x y \<Longrightarrow> trans_closure r x y"
  unfolding trans_closure_def rel_pow_iff[of r _ x y] by blast

lemma trans_closure_cases:
  assumes "trans_closure r x y"
  obtains "r x y" | u where "trans_closure r x u" "r u y"
  using assms unfolding trans_closure_def rel_pow_iff[of r _ x y] 
  using trans_closure_def that by fast

lemma trans_closure_imp_if_rel_imp_if_transitive:
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  fixes s :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<lesssim>" 50)
  assumes "transitive (\<lesssim>)"
  assumes rel_imp: "\<And>x y. x \<prec> y \<Longrightarrow> x \<lesssim> y"
  shows "trans_closure (\<prec>) x y \<Longrightarrow> x \<lesssim> y"
proof -
  assume hxy: "trans_closure (\<prec>) x y"
  have "rel_pow (\<prec>) n x y \<Longrightarrow> x \<lesssim> y" for n
  proof (induction n arbitrary: y rule: mem_induction)
    case (mem n)
    show ?case using rel_powE \<open>rel_pow (\<prec>) n x y\<close>
    proof cases
      case rel
      then show ?thesis using rel_imp by blast
    next
      case (trans m u)
      have "x \<lesssim> u" using \<open>m \<in> n\<close> \<open>rel_pow (\<prec>) m x u\<close> mem.IH by blast
      then show ?thesis using \<open>u \<prec> y\<close> rel_imp \<open>transitive (\<lesssim>)\<close> by blast
    qed
  qed
  then show ?thesis using hxy trans_closure_def by fast
qed

(* 
  Note: Together, transitive_trans_closure, trans_closure_if_rel and 
  trans_closure_imp_if_rel_imp_if_transitive show trans_closure (\<prec>) satisfies the universal
  property of the transtive closure of (\<prec>): It is the smallest transitive relation bigger than
  (\<prec>).
*)

lemma trans_closure_mem_eq_lt: "trans_closure (\<in>) = (<)"
proof -
  have "trans_closure (\<in>) x y \<Longrightarrow> x < y" for x y
    using trans_closure_imp_if_rel_imp_if_transitive transitive_lt lt_if_mem by fastforce
  moreover have "x < y \<Longrightarrow> trans_closure (\<in>) x y" for x y
  proof (induction y rule: mem_induction)
    case (mem y)
    from \<open>x < y\<close> obtain u where "x \<le> u" "u \<in> y" using lt_mem_leE by blast
    then show ?case
    proof (cases rule: leE)
      case lt
      then have "trans_closure (\<in>) x u" using \<open>u \<in> y\<close> mem.IH by blast
      then show ?thesis using \<open>u \<in> y\<close> trans_closure_if_rel transitive_trans_closure by fast
    next
      case eq
      then show ?thesis using \<open>u \<in> y\<close> trans_closure_if_rel by auto
    qed
  qed
  ultimately show ?thesis by blast
qed

context wellfounded_rel
begin

lemma wellfounded_trans_closure: "wellfounded (trans_closure (\<prec>))"
proof (rule ccontr)
  assume "\<not> wellfounded (trans_closure (\<prec>))"
  then obtain P X where "P X" and no_minimal: "\<And>Y. P Y \<Longrightarrow> (\<exists>y. trans_closure (\<prec>) y Y \<and> P y)"
    unfolding wellfounded_def by auto
  have "\<not> P Y \<and> (\<forall>y. trans_closure (\<prec>) y Y \<longrightarrow> \<not> P y)" for Y
  proof (induction Y rule: r_induct)
    case (step Y)
    show ?case
    proof (rule ccontr)
      assume "\<not> (\<not> P Y \<and> (\<forall>y. trans_closure (\<prec>) y Y \<longrightarrow> \<not> P y))"
      then consider "P Y" | y where "trans_closure (\<prec>) y Y" "P y" by blast
      then show "False"
      proof cases
        case 1
        then obtain y where "trans_closure (\<prec>) y Y" "P y" using no_minimal by blast
        then show "False" using trans_closure_cases step.IH by force
      next
        case 2
        then show "False" using trans_closure_cases step.IH by force
      qed
    qed
  qed
  then show "False" using \<open>P X\<close> by blast
qed

interpretation trancl: wellfounded_trans_rel "trans_closure (\<prec>)"
  using transitive_trans_closure wellfounded_trans_closure by unfold_locales blast

definition "wfrec R = trancl.wftrec (\<lambda>f X. R (ord_restrict f X) X)"

theorem wfrec_eq: "wfrec R X = R (ord_restrict (wfrec R) X) X"
proof -
  have fun_restrict_ord_restrict: "ord_restrict (trancl.ord_restrict f X) X = ord_restrict f X" for f
    unfolding fun_restrict_set_eq_fun_restrict_pred fun_restrict_eq_if 
    unfolding ord_restrict_eq_if trancl.ord_restrict_eq_if
    using trans_closure_if_rel by force
  have "wfrec R X = R (ord_restrict (trancl.ord_restrict (wfrec R) X) X) X"
    using trancl.wftrec_eq[of "\<lambda>f X. R (ord_restrict f X) X"] wfrec_def[of R, symmetric] by auto
  then show ?thesis unfolding fun_restrict_ord_restrict by simp
qed

end

end