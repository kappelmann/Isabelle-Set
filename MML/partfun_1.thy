theory partfun_1
imports funct_1
begin

mtheorem partfun_cl_1:
  mlet "X be set","Y be set"
  "cluster empty \<bar> Function_like for Relation-of X,Y"
  proof(standard,standard)
    have A1: "{} is empty \<bar> Function_like" by mauto
    have "{} c= [:X,Y:]" using tarski_def_3I[of "{}"] xb by mauto
    thus "{} be (empty \<bar> Function_like) \<bar> (Relation-of X,Y)"
         using tarski_def_3 A1 zfmisc_1_def_1 Subset_of_rule by auto
  qed

text_raw {*\DefineSnippet{PartFuncprefix}{*}
abbreviation PartFunc_prefix ("( PartFunc-of _,_ )" 105)
  where " PartFunc-of X,Y \<equiv> Function_like\<bar> (Relation-of X,Y)"
text_raw {*}%EndSnippet*}

mtheorem patfun1_th_4:
  "for f be Function st f is Y-valued \<and> x in dom f holds f. x in Y"
proof(standard,standard)
  fix f assume [ty]: "f be Function" and A0: "f is Y-valued \<and> x in dom f"
  hence [ty]:"f is Y-valued" by simp
  have
A1: "f. x in rng f" using funct_1_def_3 A0 by mauto
  have "rng f \<subseteq> Y" using A1 relat_1_def_19E by mauto
  thus "f. x in Y" using A1 tarski_def_3 by mauto
qed mauto


text_raw {*\DefineSnippet{partfun1def2a}{*}
mdef partfun_1_def_2 ("_ : total" [110] 110)where
  mlet "X be set"
  " attr X :total for X-defined \<bar> Relation means
      (\<lambda> IT. dom IT = X)".
text_raw {*}%EndSnippet*}


end
