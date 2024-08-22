theory HOTG_Natural_Functors 
  imports HOTG_Vectors HOTG_Functions_Composition
begin
term "{}`x"
term codom
locale HOTG_Natural_Functor = 
  fixes F 
  and n :: set
  and Fmap
  and vFset
  assumes "n \<in> \<omega>"
  and Fmap_id: "\<And>U v. vector U n v \<Longrightarrow> Fmap (map set_id v) = set_id (F v)"
  and Fmap_comp: "\<And>vf vg.
    Fmap (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) = Fmap vg \<circ> Fmap vf"
  and Fset_types:
    "\<And>U v i. vector U n v \<Longrightarrow> 0 \<le> i  \<Longrightarrow> i < n \<Longrightarrow> (F v \<Rightarrow> v !! i) (vFset !! i)"
begin

end


typedecl ('d, 'a, 'b, 'c) F


consts Fmap :: "('a1 \<Rightarrow> 'a2) \<Rightarrow> ('b1 \<Rightarrow> 'b2) \<Rightarrow> ('c1 \<Rightarrow> 'c2) \<Rightarrow>
    ('d, 'a1, 'b1, 'c1) F \<Rightarrow> ('d, 'a2, 'b2, 'c2) F"
  Fset1 :: "('d, 'a, 'b, 'c) F \<Rightarrow> 'a set"
  Fset2 :: "('d, 'a, 'b, 'c) F \<Rightarrow> 'b set"
  Fset3 :: "('d, 'a, 'b, 'c) F \<Rightarrow> 'c set"

axiomatization
  where Fmap_id: "Fmap id id id = id"
  and Fmap_comp: "\<And>f1 f2 f3 g1 g2 g3.
    Fmap (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) = Fmap g1 g2 g3 \<circ> Fmap f1 f2 f3"
  and Fmap_cong: "\<And>f1 f2 f3 g1 g2 g3 x.
    (\<And>x1. x1 \<in> Fset1 x \<Longrightarrow> f1 x1 = g1 x1) \<Longrightarrow>
    (\<And>x2. x2 \<in> Fset2 x \<Longrightarrow> f2 x2 = g2 x2) \<Longrightarrow>
    (\<And>x3. x3 \<in> Fset3 x \<Longrightarrow> f3 x3 = g3 x3) \<Longrightarrow>
    Fmap f1 f2 f3 x = Fmap g1 g2 g3 x"
  and Fset1_natural: "\<And>f1 f2 f3. Fset1 \<circ> Fmap f1 f2 f3 = image f1 \<circ> Fset1"
  and Fset2_natural: "\<And>f1 f2 f3. Fset2 \<circ> Fmap f1 f2 f3 = image f2 \<circ> Fset2"
  and Fset3_natural: "\<And>f1 f2 f3. Fset3 \<circ> Fmap f1 f2 f3 = image f3 \<circ> Fset3"


end