(*  Title:      Function.thy
    Author:     Alexander Krauss and Joshua Chen

Based on earlier work in Isabelle/ZF by Larry Paulson.
*)

section \<open>Functions, function spaces, and lambda abstraction\<close>

theory Function
imports Relations

begin

definition function :: "[set, set] \<Rightarrow> set type"
  where function_typedef:
  "function A B \<equiv>
    relation A B
  \<bar> Type (\<lambda>f. domain f = A \<and> (\<forall>x y y'. \<langle>x, y\<rangle> \<in> f \<and> \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))"

lemma function_type_iff [iff_st]:
  "f : function A B \<longleftrightarrow>
    f : relation A B \<and> domain f = A \<and> (\<forall>x y y'. \<langle>x, y\<rangle> \<in> f \<and> \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y')"
  using function_typedef by stauto

lemma function_typeI [intro_st]:
  assumes "f: relation A B" and "domain f = A" and "\<And>x y y'. \<lbrakk>\<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'"
  shows "f : function A B"
  using assms function_type_iff by auto

lemma function_is_relation [subtype]: "function A B \<prec> relation A B"
  by stauto

lemma function_type_iff2 [iff_st]:
  "f : function A B \<longleftrightarrow> f : relation A B \<and> (\<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f)"
proof auto
  assume f_fun: "f : function A B"
  thus f_rel: "f : relation A B" by stauto

  fix x assume asm: "x \<in> A"
  have "domain f = A" using f_fun by stauto
  hence "x \<in> domain f" using asm by simp
  thus "\<exists>y. \<langle>x, y\<rangle> \<in> f" using f_rel by (intro domainE)

  fix y y' assume "\<langle>x, y\<rangle> \<in> f" and "\<langle>x, y'\<rangle> \<in> f"
  thus "y = y'" using f_fun function_type_iff by auto
next
  assume f_rel: "f : relation A B" and uniq: "\<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  hence "\<forall>x \<in> A. (\<exists>y. \<langle>x, y\<rangle> \<in> f)" by auto
  hence "A \<subseteq> domain f" using f_rel by (auto intro: domainI)
  moreover have "domain f \<subseteq> A" using f_rel domain_subset by auto
  ultimately have "domain f = A" by extensionality
  thus "f : function A B" using function_type_iff f_rel uniq by stauto
qed

lemma empty_function [intro]: "{} : function {} B"
  by stauto

lemma singleton_function [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} : function {x} B"
  by stauto


subsection \<open>Set-theoretic dependent function space\<close>

definition Pi :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "Pi A B \<equiv> {f \<in> Pow (\<Coprod>x \<in> A. (B x)) | A \<subseteq> domain(f) \<and> f: function}"

abbreviation function_space :: "set \<Rightarrow> set \<Rightarrow> set"  (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> Pi A (\<lambda>_. B)"

syntax
  "_PROD"     :: "[pttrn, set, set] => set"        ("(3\<Prod>_\<in>_./ _)" 10)
translations
  "\<Prod>x\<in>A. B"   == "CONST Pi A (\<lambda>x. B)"




(*
lemma subset_DUnion_imp_relation: "r \<subseteq> DUnion A B ==> r: relation"
by (simp add: relation_def, blast)

lemma relation_converse_converse [simp]:
     "r: relation ==> converse(converse(r)) = r"
by (simp add: relation_def, blast)

lemma relation_restrict [simp]:  "relation (restrict r A)"
by (simp add: restrict_def relation_def, blast)
*)

lemma Pi_iff:
    "f \<in> Pi A B \<longleftrightarrow> f : function \<and> f \<subseteq> DUnion A B \<and> A\<subseteq>domain(f)"
  by (unfold Pi_def, blast)


lemma fun_is_function: "f \<in> Pi A B \<Longrightarrow> f : function"
by (simp only: Pi_iff)

lemma function_imp_Pi:
     "f : function \<Longrightarrow> f \<in> domain(f) \<rightarrow> range(f)"
  oops


(*Functions are relations*)
lemma fun_is_rel: "f \<in> Pi A B ==> f \<subseteq> DUnion A B"
by (unfold Pi_def, blast)

lemma Pi_cong:
    "[| A=A';  !!x. x \<in> A' ==> B(x)=B'(x) |] ==> Pi A B = Pi A' B'"
by (simp add: Pi_def cong add: DUnion_cong)

lemma fun_weaken_type: "[| f \<in> A \<rightarrow> B;  B \<subseteq> D |] ==> f \<in> A \<rightarrow> D"
by (unfold Pi_def, best)


subsection \<open>Lambda and application\<close>

definition Lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "Lambda A b == {\<langle>x,b(x)\<rangle>. x\<in>A}"

syntax
  "_lam"      :: "[pttrn, set, set] => set"        ("(3\<lambda>_\<in>_./ _)" 10)
translations
  "\<lambda>x\<in>A. f"    == "CONST Lambda A (\<lambda>x. f)"

definition "apply" :: "set \<Rightarrow> set \<Rightarrow> set"  (infixl "`" 90)
  where "f ` x = (THE y. \<langle>x, y\<rangle> \<in> f)"


lemma PiI:
  assumes "f : function" "A \<subseteq> domain f" "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x"
  shows "f \<in> Pi A B"
  oops

lemma apply_equality2: "[| \<langle>a,b\<rangle>\<in> f;  \<langle>a,c\<rangle>\<in> f;  f \<in> Pi A B |] ==> b=c"
  unfolding Pi_def function_typedef by auto

lemma function_apply_equality: 
  assumes "f : function" "\<langle>a,b\<rangle> \<in> f"
  shows "f ` a = b"
proof -
  from assms
  have c: "\<And>c. \<langle>a, c\<rangle> \<in> f \<Longrightarrow> c = b"
    unfolding function_typedef by auto
  with `\<langle>a,b\<rangle> \<in> f`
  show ?thesis
    unfolding apply_def by (rule the_equality)
qed

lemma apply_equality: "[| \<langle>a,b\<rangle>\<in> f;  f \<in> Pi A B |] ==> f`a = b"
  unfolding Pi_def by (blast intro: function_apply_equality)

lemma Pi_memberD: "[| f \<in> Pi A B;  c \<in> f |] ==> \<exists>x\<in>A.  c = \<langle>x,f`x\<rangle>"
apply (frule fun_is_rel)
apply (blast dest: apply_equality
done

lemma function_apply_Pair: 
  assumes "f : function" "a \<in> domain(f)"
  shows "\<langle>a, f`a\<rangle> \<in> f"
proof -
  from assms have "\<exists>x. \<langle>a, x\<rangle> \<in> f" by (intro domainE function_is_relation)
  then obtain y where ax: "\<langle>a, y\<rangle> \<in> f" ..
  with `f : function`
  have "f ` a = y" by (rule function_apply_equality)
  with ax show ?thesis
    by simp
qed

lemma apply_Pair: "[| f \<in> Pi A B;  a \<in> A |] ==> \<langle>a,f`a\<rangle>\<in> f"
apply (simp add: Pi_iff)
apply (blast intro: function_apply_Pair)
done

(*Conclusion is flexible -- use rule_tac or else apply_funtype below!*)
lemma apply_type: "[| f \<in> Pi A B;  a \<in> A |] ==> f`a \<in> B a"
by (blast intro: apply_Pair dest: fun_is_rel)

(*This version is acceptable to the simplifier*)
lemma apply_funtype: "f \<in> A \<rightarrow> B \<Longrightarrow>  a \<in> A \<Longrightarrow> f`a \<in> B"
by (blast dest: apply_type)

lemma apply_iff: "f \<in> Pi A B \<Longrightarrow> \<langle>a,b\<rangle>\<in> f \<longleftrightarrow> a \<in> A \<and> f`a = b"
apply (frule fun_is_rel)
apply (blast intro!: apply_Pair apply_equality)
done

(*Refining one Pi type to another*)
lemma Pi_type: "[| f \<in> Pi A C;  !!x. x \<in> A ==> f`x \<in> B(x) |] ==> f \<in> Pi A B"
apply (simp only: Pi_iff)
apply (blast dest: function_apply_equality)
done

(*Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance*)
lemma Pi_Collect_iff:
     "(f \<in> Pi A (%x. {y \<in> B(x). P x y}))
      \<longleftrightarrow>  f \<in> Pi A B \<and> (\<forall>x\<in>A. P x (f`x))"
by (blast intro: Pi_type dest: apply_type)

lemma Pi_weaken_type:
        "[| f \<in> Pi A B;  !!x. x \<in> A ==> B(x)\<subseteq>C(x) |] ==> f \<in> Pi A C"
by (blast intro: Pi_type dest: apply_type)


(** Elimination of membership in a function **)

lemma domain_type: "[| \<langle>a,b\<rangle> \<in> f;  f \<in> Pi A B |] ==> a \<in> A"
by (blast dest: fun_is_rel)

lemma range_type: "[| \<langle>a,b\<rangle> \<in> f;  f \<in> Pi A B |] ==> b \<in> B(a)"
by (blast dest: fun_is_rel

lemma Pair_mem_PiD: "[| \<langle>a,b\<rangle>\<in> f;  f \<in> Pi A B |] ==> a \<in> A \<and> b \<in> B(a) \<and> f`a = b"
by (blast intro: domain_type range_type apply_equality)

subsection\<open>Lambda Abstraction\<close>

lemma lamI: "a \<in> A ==> \<langle>a,b(a)\<rangle> \<in> (\<lambda>x\<in>A. b(x))"
  unfolding Lambda_def by (rule ReplI)

lemma lamE:
    "[| p\<in> (\<lambda>x\<in>A. b(x));  !!x.[| x \<in> A; p=\<langle>x,b(x)\<rangle> |] ==> P
     |] ==>  P"
by (simp add: Lambda_def, blast)

lemma lamD: "[| \<langle>a,c\<rangle>\<in> (\<lambda>x\<in>A. b(x)) |] ==> c = b(a)"
by (simp add: Lambda_def)

lemma lam_function:
  shows "Lambda A f : function"
  unfolding Lambda_def function_typedef
  by (auto intro: relation_collectI)
 
lemma lam_type:
  "(!!x. x \<in> A ==> b(x)\<in> B(x)) \<Longrightarrow> (\<lambda>x\<in>A. b(x)) \<in> Pi A B"
  unfolding Lambda_def Pi_def function_typedef
  by (auto intro: relation_collectI)

lemma lam_funtype: "(\<lambda>x\<in>A. b(x)) \<in> A \<rightarrow> {b(x). x \<in> A}"
by (blast intro: lam_type)

lemma beta: "a \<in> A ==> (\<lambda>x\<in>A. b(x)) ` a = b(a)"
  by (auto simp: Lambda_def apply_def)

lemma domain_lam [simp]: "domain(Lambda A b) = A"
  by (auto simp: Lambda_def)

(*congruence rule for lambda abstraction*)
lemma lam_cong [cong]:
    "[| A=A';  !!x. x \<in> A' ==> b(x)=b'(x) |] ==> Lambda A b = Lambda A' b'"
  by (simp only: Lambda_def cong add: Repl_cong)

lemma lam_eqE: "[| (\<lambda>x\<in>A. f(x)) = (\<lambda>x\<in>A. g(x));  a \<in> A |] ==> f(a)=g(a)"
by (fast intro!: lamI elim: equalityE lamE)


(*Empty function spaces*)
lemma Pi_empty1 [simp]: "Pi {} A = {{}}"
  unfolding Pi_def
  by extensionality

(*The singleton function*)
lemma singleton_fun [simp]: "{\<langle>a,b\<rangle>} \<in> {a} \<rightarrow> {b}"
  unfolding Pi_def by auto

lemma Pi_empty2 [simp]: "(A\<rightarrow>{}) = (if A={} then {{}} else {})"
  unfolding Pi_def by extensionality

lemma  fun_space_empty_iff [iff]: "(A\<rightarrow>X)={} \<longleftrightarrow> X={} \<and> (A \<noteq> {})"
apply (auto intro: lam_type)
apply (fast intro: lam_type)
done


subsection\<open>Extensionality\<close>

(*

(*LCP: Semi-extensionality!*)

lemma fun_subset:
    "[| f \<in> Pi A B;  g \<in> Pi C D;  A\<subseteq>C;
        !!x. x \<in> A ==> f`x = g`x       |] ==> f\<subseteq>g"
by (force dest: Pi_memberD intro: apply_Pair)

lemma fun_extension:
    "[| f \<in> Pi A B; g \<in> Pi A D;
        !!x. x \<in> A ==> f`x = g`x  |] ==> f=g"
by (blast del: subsetI intro: subset_refl sym fun_subset)

lemma eta [simp]: "f \<in> Pi A B ==> (\<lambda>x\<in>A. f`x) = f"
apply (rule fun_extension)
apply (auto simp add: lam_type apply_type beta)
done

lemma fun_extension_iff:
     "[| f \<in> Pi A B; g \<in> Pi A C |] ==> (\<forall>a\<in>A. f`a = g`a) \<longleftrightarrow> f=g"
by (blast intro: fun_extension)

(*thm by Mark Staples, proof by lcp*)
lemma fun_subset_eq: "[| f \<in> Pi A B; g \<in> Pi A C |] ==> f \<subseteq> g \<longleftrightarrow> (f = g)"
by (blast dest: apply_Pair
          intro: fun_extension apply_equality [symmetric])


(*Every element of Pi(A,B) may be expressed as a lambda abstraction!*)
lemma Pi_lamE:
  assumes major: "f \<in> Pi A B"
      and minor: "!!b. [| \<forall>x\<in>A. b(x)\<in>B(x);  f = (\<lambda>x\<in>A. b(x)) |] ==> P"
  shows "P"
apply (rule minor)
apply (rule_tac [2] eta [symmetric])
apply (blast intro: major apply_type)+
done

*)


end
