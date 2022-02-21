theory Dep_Rel
  imports HOL.HOL
begin

definition Rel_Fun' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool"
  where "Rel_Fun' R S f g \<equiv> \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y)"

definition rel_adj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  where "rel_adj R p \<equiv> (\<lambda>a b. R a b \<and> p a b)"

definition dep_rel_fun :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  where "dep_rel_fun R S \<equiv> (\<lambda>f g. \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y))"

definition no_dep_rel_fun :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  where "no_dep_rel_fun R S \<equiv> dep_rel_fun R (\<lambda>x y. S)"

definition rel_weak :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  where "rel_weak P R \<equiv> (\<lambda>a b. P \<longrightarrow> R a b)"

definition dep_rel_weak_fun :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  where "dep_rel_weak_fun P R S \<equiv> (\<lambda>f g. \<forall>x y. (P \<longrightarrow> R x y) \<longrightarrow> S x y (f x) (g y))"

definition no_dep_rel_weak_fun :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  where "no_dep_rel_weak_fun P R S \<equiv> dep_rel_weak_fun P R (\<lambda>x y. S)"

lemmas no_dep_rel_weak_fun_unfold = no_dep_rel_weak_fun_def[unfolded dep_rel_weak_fun_def]

syntax "_rel_adj" :: "pttrn \<Rightarrow> pttrn \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  ("[_/ _/ \<Colon>/ _/| _]" [101, 101, 101, 101] 100)

syntax "_no_dep_rel_fun" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  ("(_) \<Rrightarrow> (_)" [101, 100] 100)

syntax "_dep_rel_fun" :: "pttrn \<Rightarrow> pttrn \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  ("[_/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [101, 101, 101, 100] 100)

syntax "_dep_rel_adj_fun" :: "pttrn \<Rightarrow> pttrn \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  ("[_/ _/ \<Colon>/ _/| _] \<Rrightarrow> (_)" [101, 101, 101, 101, 100] 100)

syntax "_rel_weak" :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  ("[_ \<longrightarrow> _]" [101, 101] 100)

syntax "_dep_rel_weak_fun" :: "bool \<Rightarrow> pttrn \<Rightarrow> pttrn \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  ("[_ \<longrightarrow> _/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [101, 101, 101, 101, 100] 100)

syntax "_no_dep_rel_weak_fun" :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)"
  ("[_ \<longrightarrow> _] \<Rrightarrow> (_)" [101, 101, 100] 100)

translations
  "[x y \<Colon> R | P]" \<rightleftharpoons> "CONST rel_adj R (\<lambda>x y. P)"
  "R \<Rrightarrow> S" \<rightleftharpoons> "CONST no_dep_rel_fun R S"
  "[x y \<Colon> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST dep_rel_fun R (\<lambda>x y. S)"
  "[x y \<Colon> R | P] \<Rrightarrow> S" \<rightharpoonup> "CONST dep_rel_fun (CONST rel_adj R (\<lambda>x y. P)) (\<lambda>x y. S)"
  "[P \<longrightarrow> R]" \<rightleftharpoons> "CONST rel_weak P R"
  "[P \<longrightarrow> x y \<Colon> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST dep_rel_weak_fun P R (\<lambda>x y. S)"
  "[P \<longrightarrow> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST no_dep_rel_weak_fun P R S"

(* Tests *)
term "[x x' \<Colon> R | p x]"
term "R \<Rrightarrow> S"
term "[x x' \<Colon> R] \<Rrightarrow> S"
term "[x x' \<Colon> R | p x] \<Rrightarrow> S"
term "S \<Rrightarrow> [z z' \<Colon> T | r z]"
term "[x x' \<Colon> R] \<Rrightarrow> S \<Rrightarrow> [z z' \<Colon> T | r x z]"
term "[x x' \<Colon> R | p x] \<Rrightarrow> [y y' \<Colon> S | q x y]"
term "R \<Rrightarrow> [y y' \<Colon> S | q y] \<Rrightarrow> [z z' \<Colon> T | r y z]"
term "[x x' \<Colon> R | p x] \<Rrightarrow> [y y' \<Colon> S | q x y] \<Rrightarrow> T"
term "[x x' \<Colon> R] \<Rrightarrow> [y y' \<Colon> S] \<Rrightarrow> [z z' \<Colon> T | r x y z]"
term "[x x' \<Colon> R | p x] \<Rrightarrow> [y y' \<Colon> S | q x y] \<Rrightarrow> [z z' \<Colon> T | r x y z]"
term "[x x' \<Colon> R] \<Rrightarrow> [p x \<longrightarrow> S]"
term "[x x' \<Colon> R] \<Rrightarrow> [p x \<longrightarrow> S] \<Rrightarrow> T"
term "[x x' \<Colon> R] \<Rrightarrow> [p x \<longrightarrow> y y' \<Colon> S] \<Rrightarrow> T"
term "[x x' \<Colon> R] \<Rrightarrow> [p x \<longrightarrow> y y' \<Colon> S] \<Rrightarrow> [q x y \<longrightarrow> T] \<Rrightarrow> U"

end