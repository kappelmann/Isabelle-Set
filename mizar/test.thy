theory test
imports mizar_ty

begin

declare[[ty_debug]]

axiomatization empty finite bla :: Ty where
*[clus]: "x is empty \<Longrightarrow> x is finite" and
**[clus]: "x is finite \<Longrightarrow> x is bla"

lemma
  assumes [ty]: "a is empty"
  shows "a is bla"
by mauto


axiomatization s t :: Set and Subset_of :: "Set \<Rightarrow> Ty" and z where
test[clus]: "s is set \<Longrightarrow> t is set \<Longrightarrow> z(s, t) is non empty \<bar> set" and
subset[clus]: "\<And>x y. x is set \<Longrightarrow> y is Subset_of(x) \<Longrightarrow> y is set"

lemma
  assumes [ty]: "s is set" "t is Subset_of(s)"
  shows "z(s, t) is non empty"
by mauto

axiomatization
Prod :: "[Set, Set] \<Rightarrow> Set" and
quasi_total :: "[Set, Set] \<Rightarrow> Ty" and
Function_like Relation_like :: Ty
where
***[clus]: "X is set ==> Y is set ==> R is Subset_of(Prod(X,Y)) ==> R is Relation_like"

abbreviation "Relation_of(X,Y) == Subset_of(Prod(X,Y))"
abbreviation "PartFunc_of(X,Y) == Function_like \<bar> Relation_of(X,Y)"
abbreviation "Function_of(X,Y) == quasi_total(X,Y) \<bar> PartFunc_of(X,Y)"

lemma
  assumes
    [ty]: "X is set" "Y is set" "F is Function_of(X, Y)"
  shows
    "F is Relation_like"
by mauto


end
