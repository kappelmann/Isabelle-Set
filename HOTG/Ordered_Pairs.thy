section \<open>Ordered Pairs (\<Sigma>-types)\<close>

theory Ordered_Pairs
imports Foundation
begin

definition opair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "opair a b \<equiv> {{a}, {a, b}}"

definition fst :: \<open>set \<Rightarrow> set\<close>
  where "fst p \<equiv> THE a. \<exists>b. p = opair a b"

definition snd :: \<open>set \<Rightarrow> set\<close>
  where "snd p \<equiv> THE b. \<exists>a. p = opair a b"

syntax
  "_tuple" :: \<open>args \<Rightarrow> set\<close> ("\<langle>(_)\<rangle>")
translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST opair x y"

lemma opair_eq_iff [simp]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<longleftrightarrow> a = c \<and> b = d"
  unfolding opair_def
  by (subst singleton_eq_pair[of a], subst singleton_eq_pair[of c]) (auto simp: pair_eq_iff)

lemma opair_inject[elim!]:
  assumes "\<langle>a, b\<rangle> = \<langle>c, d\<rangle>"                                      
  obtains "a = c" and "b = d"
  using assms by auto
  
lemma eq_if_opair_eq_left: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> a = c" by simp

lemma eq_if_opair_eq_right: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> b = d" by simp

lemma opair_nonempty [simp, intro]: "\<langle>a, b\<rangle> \<noteq> {}"
  unfolding opair_def by (blast elim: equalityE)

lemma opair_emptyD: "\<langle>a, b\<rangle> = {} \<Longrightarrow> P" by auto

lemma opair_ne_fst: "\<langle>a, b\<rangle> = a \<Longrightarrow> P"
  unfolding opair_def by (auto intro: mem_asymE)

lemma opair_ne_snd: "\<langle>a, b\<rangle> = b \<Longrightarrow> P"
unfolding opair_def
proof (subst (asm) singleton_eq_pair[of a])
  assume *: "{{a, a}, {a, b}} = b"
  have "{a, b} \<in> {{a, a}, {a, b}}" by auto
  then have "{a, b} \<in> b" by (simp add: *)
  moreover have "b \<in> {a, b}" by auto
  ultimately show "P" by (rule mem_asymE)
qed                                      

lemma fst_opair_eq [simp]: "fst \<langle>a,b\<rangle> = a"                                   
  by (simp add: fst_def)

lemma snd_opair_eq [simp]: "snd \<langle>a,b\<rangle> = b"
  by (simp add: snd_def)

lemma opair_fst_snd_eq [simp]: "p = \<langle>a, b\<rangle> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by simp

lemma opair_not_in_fst: "\<langle>a, b\<rangle> \<notin> a"
  unfolding opair_def by (auto intro: mem_3_cycle)

lemma opair_not_in_snd: "\<langle>a, b\<rangle> \<notin> b"
  unfolding opair_def by (auto intro: equalityI' dest: mem_3_cycle)


subsection \<open>Set-Theoretic Dependent Pair Type\<close>

definition pairset :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
  where "pairset A B \<equiv> \<Union>x \<in> A. \<Union>y \<in> B x. {\<langle>x, y\<rangle>}"

syntax
  "_pairset" :: \<open>[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set\<close> ("\<Sum>_ \<in> _./ _" [0, 0, 100])
translations
  "\<Sum>x \<in> A. B" \<rightleftharpoons> "CONST pairset A (\<lambda>x. B)"

abbreviation prodset :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "prodset A B \<equiv> \<Sum>_ \<in> A. B"

bundle hotg_prodset_syntax begin notation prodset (infixl "\<times>" 80) end
bundle no_hotg_prodset_syntax begin no_notation prodset (infixl "\<times>" 80) end

unbundle hotg_prodset_syntax

lemma pairset_iff [simp]: "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x) \<longleftrightarrow> a \<in> A \<and> b \<in> B a"
  by (auto simp: pairset_def)
                        
lemma pairsetI [intro!]: "\<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> \<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x)"
  by simp

lemma pairsetI2 [elim]: "\<lbrakk>p = \<langle>a, b\<rangle>; a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> p \<in> \<Sum>x \<in> A. (B x)"
  by simp

theorem pairsetD1: "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> a \<in> A" by simp
theorem pairsetD2: "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> b \<in> B a" by simp

lemma pairsetE [elim!]:
  assumes "c \<in> \<Sum>x \<in> A. (B x)"
  obtains x y where "x \<in> A" "y \<in> B x" "c = \<langle>x, y\<rangle>"   
  using assms unfolding pairset_def by blast

lemma pairsetE2 [elim!]:
  assumes "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x)"
  obtains "a \<in> A" "b \<in> B a"
  using assms unfolding pairset_def by blast

lemma pairset_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Sum>x \<in> A. (B x) = \<Sum>x \<in> A'. (B' x)"
  by (simp add: pairset_def)

lemma pairset_fst: "p \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> fst p \<in> A"
  by auto

lemma pairset_snd: "p \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> snd p \<in> B (fst p)"
  by auto

lemma pairset_elem: "p \<in> \<Sum>x \<in> P. (B x) \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by auto                                            

lemma pairset_subset_elem:
  "\<lbrakk>p \<in> R; R \<subseteq> \<Sum>x \<in> A. (B x)\<rbrakk> \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by auto
                                                
lemma pairset_subset_elemE:
  assumes "p \<in> R"                  
  and "R \<subseteq> \<Sum>x \<in> A. (B x)"
  obtains a b where "a \<in> A" "b \<in> B a" "p = \<langle>a, b\<rangle>"
  using assms by auto
  
lemma pairset_empty_index [simp]: "\<Sum>x\<in> {}. (B x) = {}"
  by (rule extensionality) auto

lemma pairset_empty_sets [simp]: "\<Sum>x\<in> A. {} = {}"
  by (rule extensionality) auto

lemma pairset_empty_iff: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (auto intro!: equalityI')

lemma setprod_singletons [simp]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (rule equalityI) auto

lemma pairset_subset_setprod: "\<Sum>x\<in> A. (B x) \<subseteq> A \<times> (\<Union>x\<in> A. (B x))"
  by auto

  
text \<open>Splitting quantifiers:\<close>

lemma split_paired_bex_pair [simp]:
  "(\<exists>z \<in> \<Sum>x \<in> A. (B x). P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma split_paired_ball_pair [simp]:
  "(\<forall>z \<in> \<Sum>x \<in> A. (B x). P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast
                    
           
subsection \<open>Monotonicity\<close>

lemma setprod_monotone: "A \<subseteq> A' \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B'" by auto
lemma setprod_monotone1: "A \<subseteq> A' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B" by auto
lemma setprod_monotone2: "B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A \<times> B'" by auto
                                                 

subsection \<open>Functions on dependent pairs\<close>

definition uncurry :: "(set \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" \<comment>\<open>for pattern-matching\<close>
  where "uncurry f \<equiv> \<lambda>p. f (fst p) (snd p)"

(*Larry: Patterns—extends pre-defined type "pttrn" used in abstractions*)
nonterminal patterns
syntax
  "_pattern"  :: "patterns => pttrn" ("\<langle>_\<rangle>")
  ""          :: "pttrn => patterns" ("_")
  "_patterns" :: "[pttrn, patterns] => patterns" ("_,/ _")
translations
  "\<lambda>\<langle>x, y, zs\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x \<langle>y, zs\<rangle>. b)"
  "\<lambda>\<langle>x, y\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x y. b)"

lemma uncurry [simp]: "uncurry f \<langle>a, b\<rangle> = f a b"
  by (simp add: uncurry_def)

lemma uncurry_type:
  "\<lbrakk>p \<in> \<Sum>x \<in> A. (B x); \<And>x y. \<lbrakk>x \<in> A; y \<in> B x\<rbrakk> \<Longrightarrow> c x y \<in> C \<langle>x,y\<rangle>\<rbrakk> \<Longrightarrow> uncurry c p \<in> C p"
  by (erule pairsetE) auto

lemma expand_uncurry:
  "u \<in> A \<times> B \<Longrightarrow> R (uncurry c u) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B. u = \<langle>x,y\<rangle> \<longrightarrow> R (c x y))"
  by (force simp add: uncurry_def)

lemma uncurryI: "R a b \<Longrightarrow> uncurry R \<langle>a,b\<rangle>"
  by (simp add: uncurry_def)

lemma uncurryE:
  "\<lbrakk>uncurry R z; z \<in> \<Sum>x \<in> A. (B x); \<And>x y. \<lbrakk>z = \<langle>x, y\<rangle>; R x y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: uncurry_def)

lemma uncurryD: "uncurry R \<langle>a, b\<rangle> \<Longrightarrow> R a b"
  by (simp add: uncurry_def)


end
