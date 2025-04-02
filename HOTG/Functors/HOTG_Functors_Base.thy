\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Nils Harmsen"\<close>
section \<open>Natural Functors\<close>
subsection \<open>Basic Setup\<close>
theory HOTG_Functors_Base
  imports
    HOTG_Pairs
    Transport.Restricted_Equality
begin

definition "K x \<equiv> \<lambda>_. x"

lemma K_eq: "K = (\<lambda>x _. x)"
  unfolding K_def by simp

lemma K_eq' [simp]: "K x y = x"
  unfolding K_eq by simp

lemma mono_K: "((A :: 'a \<Rightarrow> bool) \<Rightarrow> B \<Rightarrow> A) K" by fastforce

text \<open>Indexed identity function\<close>

definition "iid \<equiv> K id"

lemma iid_eq [simp]: "iid i x = x"
  unfolding iid_def by simp

lemma iid_eq_K_id: "iid = K id"
  by (intro ext) simp

lemma mono_iid: "((i : (I :: 'i \<Rightarrow> bool)) \<Rightarrow> (iT i :: 'a \<Rightarrow> bool) \<Rightarrow> iT i) iid" by fastforce

text \<open>Indexed composition\<close>

definition "comp_ifun (f :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) (g :: 'i \<Rightarrow> 'a \<Rightarrow> 'b) i \<equiv> f i \<circ> g i"
adhoc_overloading comp \<rightleftharpoons> comp_ifun

lemma comp_ifun_eq [simp]: "((f :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) \<circ> g) i = f i \<circ> g i"
  unfolding comp_ifun_def by simp

lemma comp_ifun_assoc:
  "(f :: 'i \<Rightarrow> 'c \<Rightarrow> 'd) \<circ> (g :: 'i \<Rightarrow> 'b \<Rightarrow> 'c) \<circ> (h :: 'i \<Rightarrow> 'a \<Rightarrow> 'b) = f \<circ> (g \<circ> h)"
  unfolding comp_ifun_def by (auto simp add: fun_eq_iff)

lemma mono_mono_wrt_mono_wrt_comp_ifun:
  "(((I :: 'i \<Rightarrow> bool) \<Rightarrow> (B :: 'b \<Rightarrow> bool) \<Rightarrow> C) \<Rightarrow> (I \<Rightarrow> A \<Rightarrow> B) \<Rightarrow> I \<Rightarrow> A \<Rightarrow> C) (\<circ>)"
  by force

lemma comp_iid_eq [simp]: "(f :: 'i \<Rightarrow> _) \<circ> (iid :: 'i \<Rightarrow> _) = f"
  by (intro ext) simp

lemma iid_comp_eq [simp]: "(iid :: 'i \<Rightarrow> _) \<circ> (f :: 'i \<Rightarrow> _) = f"
  by (intro ext) simp

definition "rel_comp_irel (R :: 'i \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool) (S :: 'i \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) i \<equiv> R i \<circ>\<circ> S i"
adhoc_overloading rel_comp \<rightleftharpoons> rel_comp_irel

lemma rel_comp_irel_eq [simp]: "((R :: 'i \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool) \<circ>\<circ> S) i = R i \<circ>\<circ> S i"
  unfolding rel_comp_irel_def by simp

(*copied from HOL*)
definition "fun_upd f i y = (\<lambda>x. if x = i then y else f x)"

nonterminal updbinds and updbind
open_bundle fun_upd_syntax
begin
syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             (\<open>(\<open>indent=2 notation=\<open>mixfix update\<close>\<close>_ :=/ _)\<close>)
  ""         :: "updbind \<Rightarrow> updbinds"             (\<open>_\<close>)
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" (\<open>_,/ _\<close>)
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"
    (\<open>(\<open>open_block notation=\<open>mixfix function update\<close>\<close>_/'((2_)'))\<close> [1000, 0] 900)
end
syntax_consts
  "_updbind" "_updbinds" "_Update" \<rightleftharpoons> fun_upd
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x := y)" \<rightleftharpoons> "CONST fun_upd f x y"

lemma fun_upd_apply [simp]: "(f(x := y)) z = (if z = x then y else f z)"
  unfolding fun_upd_def by simp

lemma fun_upd_triv [simp]: "f(x := f x) = f"
  by (intro ext) simp
(*end of copy*)

lemma iid_upd_comp_iid_upd_eq_iid_upd_comp [simp]:
  "comp_ifun (iid(i := g)) (iid(i := h)) = iid(i := g \<circ> h)" for g :: "_ \<Rightarrow> 'b"
  by (intro ext) auto


end