section \<open>Structures\<close>

(*
Title:  structure.thy
Author: Joshua Chen
Date:   Jun 2019

Mathematical structures as set-theoretic functions.
*)

theory Structure
imports Ordinal Function
keywords "struct" :: thy_decl

begin


subsection \<open>Labels for structure fields\<close>

ML \<open>
structure Labels: sig
  val string_to_hash : string -> term
end = struct

val char_hash : term HashArray.hash = HashArray.hash 36

(* Populate char_hash *)
val _ =
let
  (* We hash characters as set-theoretic naturals *)
  fun hash i =
    let val O = @{term "{}"}
    in
      if i = 0 then O
      else @{const "Succ"} $ (hash (i-1))
    end

  fun upd (s, v) = HashArray.update (char_hash, s, v)
in
  upd ("0", hash 0);
  upd ("1", hash 1);
  upd ("2", hash 2);
  upd ("3", hash 3);
  upd ("4", hash 4);
  upd ("5", hash 5);
  upd ("6", hash 6);
  upd ("7", hash 7);
  upd ("8", hash 8);
  upd ("9", hash 9);
  upd ("a", hash 10);
  upd ("b", hash 11);
  upd ("c", hash 12);
  upd ("d", hash 13);
  upd ("e", hash 14);
  upd ("f", hash 15);
  upd ("g", hash 16);
  upd ("h", hash 17);
  upd ("i", hash 18);
  upd ("j", hash 19);
  upd ("k", hash 20);
  upd ("l", hash 21);
  upd ("m", hash 22);
  upd ("n", hash 23);
  upd ("o", hash 24);
  upd ("p", hash 25);
  upd ("q", hash 26);
  upd ("r", hash 27);
  upd ("s", hash 28);
  upd ("t", hash 29);
  upd ("u", hash 30);
  upd ("v", hash 31);
  upd ("w", hash 32);
  upd ("x", hash 33);
  upd ("y", hash 34);
  upd ("z", hash 35)
end

fun get_hash str = HashArray.sub (char_hash, str)

(* Convert strings to ordered tuples of the hashes of each letter. *)
fun string_to_hash str =
  let
    fun mk_pair (tm1, tm2) = @{const "Pair"} $ tm1 $ tm2
  in
    String.explode str |>  map (the o get_hash o Char.toString) |> foldl1 mk_pair
  end

end
\<close>

(* Example *)
ML_val \<open>Syntax.pretty_term @{context} (Labels.string_to_hash "01")\<close>


subsection \<open>Notation and syntax\<close>

nonterminal struct_arg and struct_args and struct_sig

syntax
  "_struct_sig"  :: "pttrn \<Rightarrow> struct_args \<Rightarrow> set type" ("(; _ . _ ;)")
  "_struct_cond" :: "pttrn \<Rightarrow> struct_args \<Rightarrow> bool \<Rightarrow> set type" ("(; _ . _ where _ ;)")
  ""             :: "pttrn \<Rightarrow> struct_args" ("_")
  ""             :: "struct_arg \<Rightarrow> struct_args" ("_")
  "_struct_arg"  :: "set \<Rightarrow> (set \<Rightarrow> set type) \<Rightarrow> struct_arg" (infix ":" 45)
  "_struct_args" :: "struct_arg \<Rightarrow> struct_args \<Rightarrow> struct_args" (infixr "," 40)
  "_struct"    :: "set type \<Rightarrow> set type" ("'(;_;')")

translations
  "(; ty ;)" \<rightharpoonup> "CONST uniq_valued \<cdot> ty"
  "; ref . lbl : typ ;" \<rightharpoonup> "CONST Type (\<lambda>ref. lbl \<in> CONST domain ref \<and> ref`lbl : typ)"
  "; ref . lbl1 : typ1, fields ;" \<rightharpoonup> "; ref . lbl1 : typ1 ; \<bar> ; ref . fields ;"
  "; ref . lbl : typ where P ;" \<rightharpoonup>
    "CONST Type (\<lambda>ref. lbl \<in> CONST domain ref \<and> ref`lbl : typ) \<bar> CONST Type (\<lambda>ref. P)"
  "; ref . lbl1 : typ1, fields where P ;" \<rightharpoonup>
    "; ref . lbl1 : typ1 ; \<bar> ; ref . fields where P ;"


(* Examples *)
term "(;; x. carrier: non-empty\<cdot>set ;;)"

term "(;; m. carrier: non-empty\<cdot>set, op: element(m`carrier \<rightarrow> m`carrier \<rightarrow> m`carrier) ;;)"

term "(;; it.
  carrier: non-empty\<cdot>set,
  op: element(it`carrier \<rightarrow> it`carrier \<rightarrow> it`carrier),
  e: element(it`carrier) where
    \<forall>x \<in> it`carrier. op`x`e = x \<and> op`e`x = x \<and>
    (\<forall>x \<in> it`carrier. \<forall>y \<in> it`carrier. \<forall>z \<in> it`carrier. op`x`(op`y`z) = op`(op`x`y)`z)
  ;;)"


(* Testing *)
ML \<open>
Outer_Syntax.local_theory
  @{command_keyword struct}
  "Declare structure definitions"
  let
    val parser = Parse.text -- (Parse.$$$ "=" |-- Parse.term)
    fun print_info (name : string, def) lthy = (
      @{print} name;
      @{print} (Syntax.read_term lthy def); lthy);
  in
    (parser >> (fn (name : string, tm) => fn lthy => print_info (name, tm) lthy))
  end
\<close>

term "(;; m. carrier: non-empty\<cdot>set, op: element(m`carrier \<rightarrow> m`carrier \<rightarrow> m`carrier) ;;)"
struct magma = "(;; m. carrier: non-empty\<cdot>set, op: element(m`carrier \<rightarrow> m`carrier \<rightarrow> m`carrier) ;;)"



end
