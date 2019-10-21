theory funct_6
  imports funct_2 nat_1 finseq_1
begin




mdef Func3 ("Func3'( _ , _ , _ ')") where
  mlet "a be object", "b be object", "c be object"
  "func Func3(a,b,c)  \<rightarrow>  FinSequence equals
    (<* a *> ^ <* b *>) ^ <*c *> " 
by auto

mtheorem
  mlet "A be non empty\<bar>set", 
        "a be Element-of A", "b be Element-of A", "c be Element-of A"
  "redefine func Func3(a,b,c)  \<rightarrow>  FinSequence-of A" 
proof
  show "Func3(a,b,c) is FinSequence-of A" using Func3[of a b c] by mty auto 
qed
  
  
