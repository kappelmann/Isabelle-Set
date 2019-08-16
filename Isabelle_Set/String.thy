section \<open>Strings\<close>

text \<open>
  Alphanumeric characters are encoded as sets. Strings are ordered tuples of characters.
\<close>

theory String
imports Ordered_Pair Ordinal

begin

syntax "_str" :: \<open>pttrn \<Rightarrow> set\<close> ("@_")

ML \<open>
(*Use unary encoding for now; this can be swapped out for something more efficient later*)
fun von_neumann i = funpow i (fn t => \<^const>\<open>succ\<close> $ t) \<^term>\<open>{}\<close>

val chars =
  ["0","1","2","3","4","5","6","7","8","9",
  "a","b","c","d","e","f","g","h","i","j",
  "k","l","m","n","o","p","q","r","s","t",
  "u","v","w","x","y","z","_"] ~~ map_range von_neumann 37
\<close>

local_setup \<open>
fn lthy =>
  let
    val transforms = chars |> map (fn (char, tm) =>
      let val name = "char'" ^ char ^ "'"
      in
        snd o Local_Theory.define (
          (Binding.qualified_name name, NoSyn),
          ((Binding.qualified_name (name ^ "_def"), []), tm)
        )
      end)
  in
    foldl1 (op o) transforms lthy
  end
\<close>

ML \<open>
fun char_tm c = case c of
    #"0" => \<^term>\<open>char'0'\<close>
  | #"1" => \<^term>\<open>char'1'\<close>
  | #"2" => \<^term>\<open>char'2'\<close>
  | #"3" => \<^term>\<open>char'3'\<close>
  | #"4" => \<^term>\<open>char'4'\<close>
  | #"5" => \<^term>\<open>char'5'\<close>
  | #"6" => \<^term>\<open>char'6'\<close>
  | #"7" => \<^term>\<open>char'7'\<close>
  | #"8" => \<^term>\<open>char'8'\<close>
  | #"9" => \<^term>\<open>char'9'\<close>
  | #"a" => \<^term>\<open>char'a'\<close>
  | #"b" => \<^term>\<open>char'b'\<close>
  | #"c" => \<^term>\<open>char'c'\<close>
  | #"d" => \<^term>\<open>char'd'\<close>
  | #"e" => \<^term>\<open>char'e'\<close>
  | #"f" => \<^term>\<open>char'f'\<close>
  | #"g" => \<^term>\<open>char'g'\<close>
  | #"h" => \<^term>\<open>char'h'\<close>
  | #"i" => \<^term>\<open>char'i'\<close>
  | #"j" => \<^term>\<open>char'j'\<close>
  | #"k" => \<^term>\<open>char'k'\<close>
  | #"l" => \<^term>\<open>char'l'\<close>
  | #"m" => \<^term>\<open>char'm'\<close>
  | #"n" => \<^term>\<open>char'n'\<close>
  | #"o" => \<^term>\<open>char'o'\<close>
  | #"p" => \<^term>\<open>char'p'\<close>
  | #"q" => \<^term>\<open>char'q'\<close>
  | #"r" => \<^term>\<open>char'r'\<close>
  | #"s" => \<^term>\<open>char's'\<close>
  | #"t" => \<^term>\<open>char't'\<close>
  | #"u" => \<^term>\<open>char'u'\<close>
  | #"v" => \<^term>\<open>char'v'\<close>
  | #"w" => \<^term>\<open>char'w'\<close>
  | #"x" => \<^term>\<open>char'x'\<close>
  | #"y" => \<^term>\<open>char'y'\<close>
  | #"z" => \<^term>\<open>char'z'\<close>
  | #"_" => \<^term>\<open>char'_'\<close>
  | _ => raise Match

fun str_tm s =
  (foldr1 (fn (t1, t2) => \<^const>\<open>opair\<close> $ t1 $ t2) (map char_tm (String.explode s)))

fun str_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
      c $ str_tr [t] $ u
  | str_tr [t] =
      (case t of
        Free (s, _) => str_tm s
      | Const (s, _) => str_tm s
      | _ => raise TERM ("str_tr", [t]))
  | str_tr ts = raise TERM ("str_tr", ts)
\<close>

setup \<open>Sign.parse_translation [(\<^syntax_const>\<open>_str\<close>, K str_tr)]\<close>

lemmas char_simps [simp] =
  char'0'_def char'1'_def char'2'_def char'3'_def char'4'_def char'5'_def char'6'_def
  char'7'_def char'8'_def char'9'_def char'a'_def char'b'_def char'c'_def char'd'_def
  char'e'_def char'f'_def char'g'_def char'h'_def char'i'_def char'j'_def char'k'_def
  char'l'_def char'm'_def char'n'_def char'o'_def char'p'_def char'q'_def char'r'_def
  char's'_def char't'_def char'u'_def char'v'_def char'w'_def char'x'_def char'y'_def
  char'z'_def char'_'_def

lemma opair_neq_succ [simp]: "\<langle>a, b\<rangle> \<noteq> succ n"
unfolding opair_def succ_def
oops

lemma "@ab \<noteq> @b" apply (auto dest!: succ_inject) oops


end
