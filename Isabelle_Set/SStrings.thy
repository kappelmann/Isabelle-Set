\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Strings\<close>
theory SStrings
  imports
    HOTG.HOTG_Ordinals_Base
    Soft_Types.Soft_Types_HOL
begin

text \<open>Alphanumeric characters are encoded as ordinals. Strings are ordered tuples of
characters.\<close>

subsection \<open>Characters\<close>

ML \<open>
(*Use unary encoding for now; this can be swapped out for something more
  efficient later.*)
fun von_neumann i = funpow i (fn t => \<^const>\<open>succ\<close> $ t) \<^term>\<open>{}\<close>

val chars =
  ["0","1","2","3","4","5","6","7","8","9",
  "a","b","c","d","e","f","g","h","i","j", "k","l","m",
  "n","o","p","q","r","s","t","u","v","w","x","y","z",
  "A","B","C","D","E","F","G","H","I","J","K","L","M",
  "N","O","P","Q","R","S","T","U","V","W","X","Y","Z",
  "_","'"] ~~ map_range von_neumann 64
\<close>

local_setup \<open>
  let val transforms = chars |> map (fn (char, tm) =>
    let
      val name = "char'" ^ char ^ "'"
      val mx = "'''" ^ char ^ "''"
    in
      snd o Local_Theory.define (
        (Binding.qualified_name name, Mixfix.mixfix mx),
        ((Binding.qualified_name (name ^ "_def"), []), tm)
      )
    end)
  in foldl1 (op o) transforms end
\<close>

subsection \<open>Strings\<close>

definition string :: \<open>set \<Rightarrow> set\<close>
  where "string s \<equiv> s" \<comment>\<open>Wraps tuples of characters into strings.\<close>

text \<open>Strings should be opaque to the type derivator.\<close>

opaque "string"

syntax "_string" :: \<open>pttrn \<Rightarrow> set\<close> ("$_")

ML \<open>
  fun term_of_char c = case c of
      #"0" => \<^term>\<open>'0'\<close> | #"1" => \<^term>\<open>'1'\<close> | #"2" => \<^term>\<open>'2'\<close> | #"3" => \<^term>\<open>'3'\<close>
    | #"4" => \<^term>\<open>'4'\<close> | #"5" => \<^term>\<open>'5'\<close> | #"6" => \<^term>\<open>'6'\<close> | #"7" => \<^term>\<open>'7'\<close>
    | #"8" => \<^term>\<open>'8'\<close> | #"9" => \<^term>\<open>'9'\<close> | #"a" => \<^term>\<open>'a'\<close> | #"b" => \<^term>\<open>'b'\<close>
    | #"c" => \<^term>\<open>'c'\<close> | #"d" => \<^term>\<open>'d'\<close> | #"e" => \<^term>\<open>'e'\<close> | #"f" => \<^term>\<open>'f'\<close>
    | #"g" => \<^term>\<open>'g'\<close> | #"h" => \<^term>\<open>'h'\<close> | #"i" => \<^term>\<open>'i'\<close> | #"j" => \<^term>\<open>'j'\<close>
    | #"k" => \<^term>\<open>'k'\<close> | #"l" => \<^term>\<open>'l'\<close> | #"m" => \<^term>\<open>'m'\<close> | #"n" => \<^term>\<open>'n'\<close>
    | #"o" => \<^term>\<open>'o'\<close> | #"p" => \<^term>\<open>'p'\<close> | #"q" => \<^term>\<open>'q'\<close> | #"r" => \<^term>\<open>'r'\<close>
    | #"s" => \<^term>\<open>'s'\<close> | #"t" => \<^term>\<open>'t'\<close> | #"u" => \<^term>\<open>'u'\<close> | #"v" => \<^term>\<open>'v'\<close>
    | #"w" => \<^term>\<open>'w'\<close> | #"x" => \<^term>\<open>'x'\<close> | #"y" => \<^term>\<open>'y'\<close> | #"z" => \<^term>\<open>'z'\<close>
    | #"A" => \<^term>\<open>'A'\<close> | #"B" => \<^term>\<open>'B'\<close> | #"C" => \<^term>\<open>'C'\<close> | #"D" => \<^term>\<open>'D'\<close>
    | #"E" => \<^term>\<open>'E'\<close> | #"F" => \<^term>\<open>'F'\<close> | #"G" => \<^term>\<open>'G'\<close> | #"H" => \<^term>\<open>'H'\<close>
    | #"I" => \<^term>\<open>'I'\<close> | #"J" => \<^term>\<open>'J'\<close> | #"K" => \<^term>\<open>'K'\<close> | #"L" => \<^term>\<open>'L'\<close>
    | #"M" => \<^term>\<open>'M'\<close> | #"N" => \<^term>\<open>'N'\<close> | #"O" => \<^term>\<open>'O'\<close> | #"P" => \<^term>\<open>'P'\<close>
    | #"Q" => \<^term>\<open>'Q'\<close> | #"R" => \<^term>\<open>'R'\<close> | #"S" => \<^term>\<open>'S'\<close> | #"T" => \<^term>\<open>'T'\<close>
    | #"U" => \<^term>\<open>'U'\<close> | #"V" => \<^term>\<open>'V'\<close> | #"W" => \<^term>\<open>'W'\<close> | #"X" => \<^term>\<open>'X'\<close>
    | #"Y" => \<^term>\<open>'Y'\<close> | #"Z" => \<^term>\<open>'Z'\<close> | #"_" => \<^term>\<open>'_'\<close> | #"'" => \<^term>\<open>'''\<close>
    | _ => raise Match

  fun pairify s =
    (foldr1 (fn (t1, t2) => \<^const>\<open>mk_pair\<close> $ t1 $ t2) (map term_of_char (String.explode s)))

  fun str_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
        c $ (\<^const>\<open>string\<close> $ str_tr [t]) $ u
    | str_tr [t] =
        (case t of
          Free (s, _) => pairify s
        | Const ("_idtdummy", _) => error "Cannot begin string with underscore"
        | Const (s, _) => pairify s
        | _ => raise TERM ("str_tr", [t]))
    | str_tr ts = raise TERM ("str_tr", ts)

  fun tuple_to_string t =
    let
      fun char (Const (s, _)) =
            let
              val base_name = nth (space_explode "." s) 1
            in
              nth_string base_name 5
            end
        | char _ = raise Match

      (*
        Josh: Some issue I can't figure out: at the stage at which
        print_translation is called, the scope of \<open>pair\<close> hasn't been resolved
        fully, so using \<^const_name>\<open>pair\<close> fails in the code below.
      *)
      fun tuple_to_string (_ $ t $ ts) = (*Underscore should be \<open>pair\<close>!*)
            char t :: tuple_to_string ts
        | tuple_to_string t = [char t]
    in
      implode (
        case t of
          (*Underscore should be \<open>pair\<close>!*)
          (_ $ t $ ts) => char t :: tuple_to_string ts
        | _ => [char t])
    end

  fun str_tr' [] = Syntax.const \<^syntax_const>\<open>_string\<close>
    | str_tr' [t] = Syntax.const \<^syntax_const>\<open>_string\<close> $ Syntax.free (tuple_to_string t)
    | str_tr' ts = raise TERM ("str_tr'", ts)
\<close>

parse_translation \<open>[(\<^syntax_const>\<open>_string\<close>, K str_tr)]\<close>
print_translation \<open>[(\<^const_syntax>\<open>string\<close>, K str_tr')]\<close>

lemmas char_simps =
  char'0'_def char'1'_def char'2'_def char'3'_def char'4'_def char'5'_def char'6'_def
  char'7'_def char'8'_def char'9'_def char'a'_def char'b'_def char'c'_def char'd'_def
  char'e'_def char'f'_def char'g'_def char'h'_def char'i'_def char'j'_def char'k'_def
  char'l'_def char'm'_def char'n'_def char'o'_def char'p'_def char'q'_def char'r'_def
  char's'_def char't'_def char'u'_def char'v'_def char'w'_def char'x'_def char'y'_def
  char'z'_def char'A'_def char'B'_def char'C'_def char'D'_def char'E'_def char'F'_def
  char'G'_def char'H'_def char'I'_def char'J'_def char'K'_def char'L'_def char'M'_def
  char'N'_def char'O'_def char'P'_def char'Q'_def char'R'_def char'S'_def char'T'_def
  char'U'_def char'V'_def char'W'_def char'X'_def char'Y'_def char'Z'_def char'_'_def

text \<open>The following lemma is used to prove distinctness of non-identical strings.\<close>

lemma pair_ne_succ: "\<langle>a, b\<rangle> \<noteq> succ n" \<comment>\<open>Very encoding-dependent!\<close>
unfolding mk_pair_def succ_eq_insert_self
proof
  let ?pair = "{{a}, {a, b}}"
  presume asm: "?pair = n \<union> {n}"
  then have
    "n \<in> ?pair"
    by auto
  hence
    "n = {a} \<or> n = {a, b}"
    by auto
  hence
    "a \<in> ?pair"
    by (auto simp: asm)
  then show False by auto
qed simp

lemmas succ_ne_pair = pair_ne_succ[symmetric]


subsection \<open>String Disequality\<close>

lemma False_if_ne_if_eq: "a = b \<Longrightarrow> a \<noteq> b \<Longrightarrow> False" by auto

lemma string_conj_simp [simp]:
  "\<lbrakk>string a \<noteq> string b; P\<rbrakk> \<Longrightarrow> string a \<noteq> string b \<and> P" ..

ML \<open>
  fun string_ne_tac ctxt =
    let
      val char_ne_word_tac = SUBGOAL (fn (_, i) =>
        rewrite_goal_tac ctxt @{thms char_simps} i
        THEN HEADGOAL (eresolve0_tac @{thms succ_ne_pair pair_ne_succ}))

      fun word_ne_tac i =
        let
          val char_ne_tac = SUBGOAL (fn (_, i) =>
            rewrite_goal_tac ctxt @{thms char_simps} i
            THEN REPEAT (HEADGOAL (dresolve0_tac @{thms succ_inj}))
            THEN HEADGOAL (eresolve0_tac @{thms False_if_ne_if_eq})
            THEN HEADGOAL (resolve0_tac @{thms succ_ne_zero succ_ne_zero[symmetric]}))

          val first_char_ne_tac =
            TRY o dresolve0_tac @{thms eq_if_mk_pair_eq_left} THEN' char_ne_tac
        in
          REPEAT (CHANGED
            ((char_ne_word_tac
            ORELSE' first_char_ne_tac
            ORELSE' dresolve0_tac @{thms eq_if_mk_pair_eq_right}) i))
        end
    in
      resolve_tac ctxt @{thms notI}
      THEN' rewrite_goal_tac ctxt @{thms string_def}
      THEN' word_ne_tac
    end

  val string_simp_solver = map_theory_simpset
    (fn ctxt => ctxt addSolver (mk_solver "distinguish strings" string_ne_tac))
\<close>

setup \<open>string_simp_solver\<close>

method_setup string_ne =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (
    (TRY o eresolve_tac ctxt @{thms False_if_ne_if_eq})
    THEN' string_ne_tac ctxt))\<close>

(* Example *)
notepad
begin
  have
    "$Alex \<noteq> $Josh" and
    "$abcd \<noteq> $asdf" and
    "$abcd \<noteq> $asdf" and
    "$abcdefg \<noteq> $asdfghj" and
    "$a10 \<noteq> $b_"
    by simp_all
end


end
