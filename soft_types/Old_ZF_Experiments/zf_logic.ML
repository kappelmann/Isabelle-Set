signature ZF_LOGIC =
sig

val iT : typ;
val oT : typ;
val Trueprop : term
val True : term

val mk_mem : term -> term -> term 


end



structure ZF_Logic : ZF_LOGIC =
struct

val iT = @{typ "i"};
val oT = @{typ "o"};
val Trueprop = @{term "Trueprop"}
val True = @{term "True"}


fun mk_mem x A = Const (@{const_name "mem"}, iT --> iT --> oT) $ x $ A


end







