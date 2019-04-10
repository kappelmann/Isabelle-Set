theory mizar_import
  imports "mizar_fraenkel"
    "mizar_fraenkel_more"
begin

section "TARSKI_0"
reserve x for object
theorem tarski_0_1:
  "\<forall>x. x be set" using SET_def by simp
theorem set_exists[ex]: "inhabited(set)"
  using tarski_0_1 inhabited_def by auto

ML {*
datatype t =
  E of string * (string * string) list * t list
| T of term
| C of cterm
| S of string
val nodata = filter (fn XML.Elem _ => true | _ => false)
fun premizify (XML.Elem ((n, a), t)) = E(n, a, (map premizify (nodata t)))
  | premizify _ = raise Fail "assert false"
*}

ML {*
fun read_xml fname =
   let val XML.Elem (_,x) = XML.parse (File.read (Path.explode fname)) in
   map premizify (nodata x) end 
*}


ML {* exception WSX of t list *}

ML {*
fun nqterm lthy t = Pretty.string_of (Syntax.pretty_term lthy t);
fun term lthy t =
  let val s = nqterm lthy t in
  if exists_string (fn c => c = " ") s then "\"" ^ s ^ "\"" else s
  end
*}

ML {* 
fun seq_to_seq ("_" :: t) = "'_" :: seq_to_seq t
  | seq_to_seq ("'" :: t) = "''" :: seq_to_seq t
  | seq_to_seq ("/" :: t) = "'/" :: seq_to_seq t
  | seq_to_seq (x :: t) = x :: seq_to_seq t
  | seq_to_seq [] = []
fun notate s = implode (seq_to_seq (Symbol.explode s))
*}
ML {*
fun mixfix suffix (E ("pattern", ("spelling", s) :: ("argsL", argl) :: ("argsR", argr) :: ("spellingR", sr) :: _, [])) =
  let 
    val s = if suffix = "" then s else s ^ "\<^bsub>" ^ suffix ^ "\<^esub>"
    fun mkargs a = space_implode "," (map (fn _ => "_") (1 upto (Option.valOf (Int.fromString a))))
    val al = if argl = "0" then "" else (mkargs argl) ^ " ";
    val ar = if argr = "0" then "" else " " ^ (mkargs argr);
    val sr = if sr = "" then "" else " " ^ sr
  in (al ^ (notate s) ^ ar ^ (notate sr)) end
  | mixfix _ _ = raise Fail "mixfix"
*} 

ML {*
fun mis_var_ty "set" 0 _ = @{typ Set}
  | mis_var_ty "ty" 0 _ = @{typ Ty}
  | mis_var_ty "o" 0 _ = @{typ o}
  | mis_var_ty t n "set" = @{typ Set} --> (mis_var_ty t (n - 1) "set")
  | mis_var_ty t _ at = raise Fail ("mis_var_ty:" ^ t ^ at)
*}
ML {*
Syntax.parse_term @{context} "autogen3.T"
handle Exn.EXCEPTIONS x => (tracing (@{make_string} x); @{term True}) 
*}

(* TODO *)
definition "FlexOr(a, b) \<equiv> a \<or> b"
definition "FlexAnd(a, b) \<equiv> a \<and> b"

ML {*
fun mis_tm _    (E ("var", ("id", tn)::("type", t)::("args", argn)::("argsType", argt)::_, [])) = Free(tn, mis_var_ty t (Option.valOf (Int.fromString argn)) argt)
  | mis_tm _    (E ("var_const", ("id", tn)::("type", t)::("args", argn)::("argsType", argt)::_, [])) = Free(tn, mis_var_ty t (Option.valOf (Int.fromString argn)) argt)
  | mis_tm _    (E ("schemevar", ("id", tn)::("type", t)::("args", argn)::("argsType", argt)::_, [])) = Free(tn, mis_var_ty t (Option.valOf (Int.fromString argn)) argt)
  | mis_tm ctxt (E ("app", _, l)) = foldl1 ($) (map (mis_tm ctxt) l)
  | mis_tm ctxt (E ("abs", ("id", n)::("type", "set")::_, [t])) = absfree (n, @{typ Set}) (mis_tm ctxt t)
 
  | mis_tm _    (E ("logic", ("id", "impl")::_, [])) = @{term "(implies)"}
  | mis_tm _    (E ("logic", ("id", "iff")::_, [])) = @{term "(iff)"}
  | mis_tm _    (E ("logic", ("id", "or")::_, [])) = @{term "(\<or>)"}
  | mis_tm _    (E ("logic", ("id", "and")::_, [])) = @{term "(\<and>)"}
  | mis_tm _    (E ("logic", ("id", "not")::_, [])) = @{term "Not"}
  | mis_tm _    (E ("logic", ("id", "False")::_, [])) = @{term "False"}
  | mis_tm _    (E ("logic", ("id", "True")::_, [])) = @{term "True"}
  | mis_tm _    (E ("logic", ("id", "ball")::_, [])) = @{term "Ball"}
  | mis_tm _    (E ("logic", ("id", "bex")::_, [])) = @{term "Bex"}
  | mis_tm _    (E ("logic", ("id", "hidden_ball")::_, [])) = @{term "Ball"}
  | mis_tm _    (E ("logic", ("id", "neg")::_, [])) = @{term "NON"}

  | mis_tm _    (E ("const", ("id", "HIDDENM1")::_, [])) = @{term "object"}
  | mis_tm _    (E ("const", ("id", "HIDDENM2")::_, [])) = @{term "set"}
  | mis_tm _    (E ("const", ("id", "HIDDENR1")::_, [])) = @{term "(=)"}
  | mis_tm _    (E ("const", ("id", "HIDDENR2")::_, [])) = @{term "(<>)"}
  | mis_tm _    (E ("const", ("id", "HIDDENR3")::_, [])) = @{term "(in)"}

  | mis_tm ctxt (E ("reservedconst",("id","number"):: ("value", n)::_, [])) =
      let
        val zero = Syntax.parse_term ctxt "ORDINAL1K5"(*"{}"*)
        val succ = Syntax.parse_term ctxt "ORDINAL1K1"
        val num = Option.valOf (Int.fromString n)
      in fold (fn _ => fn t => succ $ t) (1 upto num) zero end
  | mis_tm _    (E ("reservedconst", ("id", "global_choice")::_, [])) = @{term "choice"}
  | mis_tm _    (E ("reservedconst", ("id", "is_ty")::_, [])) = @{term "ty_membership"}
  | mis_tm _    (E ("reservedconst", ("id", "ty_ty")::_, [])) = @{term "ty_intersection"}
  | mis_tm _    (E ("reservedconst", ("id", "fraenkel") :: ("type", "set"):: ("args", "3")::_, [])) = @{term Fraenkel1}
  | mis_tm _    (E ("reservedconst", ("id", "fraenkel") :: ("type", "set"):: ("args", "4")::_, [])) = @{term Fraenkel2}
  | mis_tm _    (E ("reservedconst", ("id", "fraenkel") :: ("type", "set"):: ("args", "5")::_, [])) = @{term Fraenkel3}
  | mis_tm _    (E ("reservedconst", ("id", "fraenkel") :: ("type", "set"):: ("args", "6")::_, [])) = @{term Fraenkel4}

 (* | mis_tm ctxt (E ("reservedconst", ("id", "fraenkel") :: ("type", "set"):: ("args", "3")::_, [a1, a2, a3])) =
      @{term Fraenkel1} $ (mis_tm ctxt a1) $ (mis_tm ctxt a2) $ (mis_tm ctxt a3)

 | mis_tm ctxt (E ("reservedconst",("id","fraenkel")::  ("type", "set"):: ("args", "4")::_, [a1, a2, a3, a4])) =
      @{term Fraenkel2} $ (mis_tm ctxt a1) $ (mis_tm ctxt a2) $ (mis_tm ctxt a3) $ (mis_tm ctxt a4)
*)

(*  | mis_tm ctxt (E ("fraenkel", ("args", "1")::_, [a1, a2, a3])) =
      @{term Fraenkel1} $ (mis_tm ctxt a1) $ (mis_tm ctxt a2) $ (mis_tm ctxt a3)
  | mis_tm ctxt (E ("fraenkel", ("args", "2")::_, [a1, a2, a3, a4])) =
      @{term Fraenkel2} $ (mis_tm ctxt a1) $ (mis_tm ctxt a2) $ (mis_tm ctxt a3) $ (mis_tm ctxt a4)
  | mis_tm ctxt (E ("fraenkel", ("args", "3")::_, [a1, a2, a3, a4, a5])) =
      @{term Fraenkel3} $ (mis_tm ctxt a1) $ (mis_tm ctxt a2) $ (mis_tm ctxt a3) $ (mis_tm ctxt a4) $ (mis_tm ctxt a5)
  | mis_tm ctxt (E ("fraenkel", ("args", "4")::_, [a1, a2, a3, a4, a5, a6])) =
      @{term Fraenkel4} $ (mis_tm ctxt a1) $ (mis_tm ctxt a2) $ (mis_tm ctxt a3) $ (mis_tm ctxt a4) $ (mis_tm ctxt a5) $ (mis_tm ctxt a6)
*)
  | mis_tm ctxt (E ("const", ("id", unk)::_, [])) =
      let
        val t = Syntax.parse_term ctxt ("autogen3." ^ unk)
                handle Exn.EXCEPTIONS _ => Syntax.parse_term ctxt unk
        val t2 = Syntax.check_term ctxt t
      in
        if is_Free t2 andalso not (Variable.is_fixed ctxt unk) then raise Fail ("const not fixed: " ^ unk) else t2
      end

  | mis_tm ctxt (E ("reservedconst", ("id", unk)::(x,y)::_, [])) =
      let
        val t = Syntax.parse_term ctxt ("autogen3." ^ unk)
                handle Exn.EXCEPTIONS _ => Syntax.parse_term ctxt unk
        val t2 = Syntax.check_term ctxt t
      in
        if is_Free t2 andalso not (Variable.is_fixed ctxt unk) then raise Fail ("reservedconst not fixed: " ^ unk^x^y) else t2
      end


  | mis_tm ctxt (E ("ReservationType", [("id", n)], _)) =
     (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
       NONE => @{term "reserved :: Ty"}
     | SOME ty => ty)
  | mis_tm _ (E ("Brak", (x, y)::_, _)) = Free ("Brak" ^ x ^ "=" ^ y, @{typ Set})
  | mis_tm _ unk = raise WSX [S "tm", unk];
fun mis_tm2 ctxt t = Syntax.check_term ctxt (mis_tm ctxt t)
fun mis_tm ctxt t = mis_tm2 ctxt t
*}
ML {*
fun mis_lab l = if l = "" orelse l = " " then "" else l ^ ":";
fun mis_prop ctxt (E ("proposition", ("label",l)::_, [prop])) =
  let
    val tm = Syntax.check_term ctxt (mis_tm ctxt prop);
  in
    if fastype_of tm = @{typ o}
    then (l, mk_Trueprop (mis_tm ctxt prop))
    else ((*warning "proposition around a prop!";*) (l, tm))
  end
(*  | mis_prop ctxt t = (warning "term as prop!"; ("", mis_tm ctxt t))*)
  | mis_prop _ unk = raise WSX [S "prop", unk]
*}

ML {*
fun mlet_str _ _    [] = ""
  | mlet_str s lthy l = "\n  " ^ s ^ " " ^ (space_implode ", " (map (term lthy) l))
*}

(*
local_setup {* fn lthy =>
let
 val (_, lthy1) = Local_Theory.open_target lthy
 val (_, lthy1') = Variable.add_fixes ["b"] lthy1
 val ((t, (_, th)), lthy2) =
    Specification.definition NONE [] [] 
   ((Binding.empty, []), @{term "a == True"}) lthy1';
 val lthy3 = Local_Theory.close_target lthy2
 val _ = Syntax.check_term lthy3 (Const ("autogen4.a", @{typ o}))
 in
  lthy3
 end
*}
*)

ML {*
fun c_abbreviation id lets pat l r lthy =
  let 
    val l = mis_tm lthy l
    val r = mis_tm lthy r
    val eq = Syntax.check_term lthy (Logic.mk_equals (l, r))
    val _ = Thm.cterm_of lthy eq
    val mix = mixfix id pat
    val (_, lthy1) = Local_Theory.open_target lthy
    val (_, lthy2) = Specification.definition (SOME ((Binding.make (id, Position.none), NONE, (Mixfix.mixfix mix)))) [] [] ((Binding.make (id ^ "_def", Position.none), []), Logic.mk_equals (l, r)) lthy1
(*    val lthy' = Specification.abbreviation Syntax.mode_input (SOME ((Binding.make (id, Position.none), NONE, (Mixfix.mixfix mix)))) [] (Logic.mk_equals (l, r)) false lthy*)
    val lthy3 = Local_Theory.close_target lthy2
    val s = "abbreviation " ^ id ^ " (\"" ^ mix ^ "\") where\n  " ^ (term lthy3 eq)
  in (s, lthy3) end
*}
ML {*
fun c_thm lets prop lthy =
  let
    val _ = Syntax.check_term lthy @{term "P :: o"}
    val lets = map (mk_Trueprop o mis_tm lthy) lets
    val (label, prop) = mis_prop lthy prop
    val label = if label = " " then "" else label
    val prop2 = Syntax.check_term lthy prop
    val (_, lthy1) = Local_Theory.open_target lthy
    val state = mtheorem_cmd false true (Binding.make (label, Position.none)) [] lets prop2 lthy1
    val lthy2 = Proof.global_skip_proof true state
    val lthy3 = Local_Theory.close_target lthy2
    val s = "mtheorem " ^ (mis_lab label) ^ (mlet_str "mlet" lthy3 lets) ^ "\n  " ^ (term lthy3 prop2)
  in (s, lthy3)
  end

fun c_reservation vs ty lthy =
  let 
    val vs = map (fst o dest_Free o (mis_tm lthy)) vs
    val ty = mis_tm lthy ty
    val s = "reserve " ^ (space_implode "," vs) ^ " for " ^ (term lthy ty)
    val lthy' = reserve_cmd (vs, ty) lthy
  in (s, lthy') end
*}


ML {*
fun c_def id lab pat lets defn lthy =
  let
    val lets = map (mk_Trueprop o (mis_tm lthy)) lets
    val defn = Syntax.check_term lthy (mk_Trueprop (mis_tm lthy defn))
    val mix = mixfix "" pat
    val (_, lthy1) = Local_Theory.open_target lthy
    val pstate = mdef_cmd (SOME lab, (((Binding.make (id, Position.none), NONE, (Mixfix.mixfix mix)), lets), defn)) lthy1
    val lthy2 = Proof.global_skip_proof true pstate
    val lthy3 = Local_Theory.close_target lthy2
(*    val lthy'' = Proof_Context.init_global (Proof_Context.theory_of lthy')*)
    val def = the_single (Proof_Context.get_thms lthy3 (id ^ "_def"))
    val s = "mdef " ^ lab ^ " : " ^ id ^ " (\"" ^ mix ^ "\") where" ^ (mlet_str "mlet" lthy3 lets) ^ "\n  " (*^ (term lthy' defn) ^ "\n  "*) ^ (Thm.string_of_thm lthy3 def) 
  in
    (s, lthy3)
  end
*}

ML {*
fun c_scheme assumes prop lthy =
  let
    val assumes = map (snd o mis_prop lthy) assumes
    val (label, prop) = mis_prop lthy prop
    val prop2 = Syntax.check_term lthy prop
    val state = mtheorem_cmd true true (Binding.make (label, Position.none)) [] assumes prop2 lthy
    val lthy2 = Proof.global_skip_proof true state
    val s = "mscheme " ^ (mis_lab label) ^ (mlet_str "assumes" lthy assumes) ^ "\n  " ^ (term lthy2 prop2)
  in (s, lthy2)
  end
*}

ML {*
fun c (E ("command", ("id", "reservation")::_, [E ("list", _, vs), ty])) lthy = c_reservation vs ty lthy
  | c (E ("mtheorem", _, (E ("let", _, lets))::prop::_)) lthy = c_thm lets prop lthy
  | c (E ("mscheme", _, _ :: (E ("provisional", _, ps))::prop::_)) lthy = c_scheme ps prop lthy
 (* | c (E ("command", ("id", "scheme")::_, _)) lthy = (warning "Schmeme ignored!"; ("", lthy))*)
  | c (E ("command", ("id", "reconsider")::_, _)) lthy = (warning "Reconsider ignored!"; ("", lthy))
  | c (E ("command", ("id", "consider")::_, _)) lthy = (warning "Consider ignored!"; ("", lthy))
  | c (E ("command", ("id", "AlsoHave")::_, _)) lthy = (warning "AlsoHave ignored!"; ("", lthy))
  | c (E ("command", ("id", "FinallyHave")::_, _)) lthy = (warning "FinallyHave ignored!"; ("", lthy))
  | c (E ("localset", _, _)) lthy = (warning "Localset ignored!"; ("", lthy))
  | c (E ("command", ("id", "cluster")::_, (E ("let", _, lets))::prop::_)) lthy = c_thm lets prop lthy
  | c (E ("command", ("id", "identify")::_, (E ("let", _, lets))::prop::_)) lthy = c_thm lets prop lthy
  | c (E ("mlemma", _, prop::_)) lthy = (*(warning "Lemma ignored!"; ("", lthy))*) c_thm [] prop lthy
  | c (E ("abbreviation", ("kind",_)::("identifier",id)::_, lets::pat::l::r::_)) lthy = c_abbreviation id lets pat l r lthy
  | c (E ("comment", ("text", t)::_, [])) lthy = ("text \"" ^ t ^ "\"", lthy)
  | c (E ("mdefinition", ("identifier", id)::("label", lab)::_, pat::(E ("let",_,lets))::(E ("definiens",_,[defn]))::_)) lthy = c_def id lab pat lets defn lthy
  | c unk _ = raise WSX [S "cmd", unk]
*}

ML {*
(*fun readx s = read_xml ("/s/a/miz-wsx-xml/mml100/" ^ s ^ ".mis")*)
fun readx s = read_xml ("/mml100/" ^ s ^ ".mis")
              handle _ => read_xml ("./mml100/" ^ s ^ ".mis")

(*fun readx1 s = read_xml ("/s/a/miz-wsx-xml/mml/" ^ s ^ ".mis")*)
fun readx1 s = read_xml ("/mml/" ^ s ^ ".mis")

fun do_xml xml lthy =
  let val (s, lthy') = c xml lthy in (tracing s; lthy') end
fun ffun x (i, sfs, lthy) =
  let val (s, lthy2) =
    (c x lthy)
    handle ERROR s => (warning ("ERROR in " ^ (Int.toString i) ^ s); ("", lthy))
  in
  (tracing s; (i + 1, sfs ^ "\n\n" ^ s, lthy2)) end;
fun do_xmls xmls lthy =
  let val (_, _, lthy2) = fold ffun xmls (0, "", lthy) in (lthy2) end 
fun dof s = do_xmls (readx s)
fun dof1 s = do_xmls (readx1 s)
fun debugf s i j = let val xml = readx s in fold do_xml (List.map (nth xml) (i upto j)) end
*}
  
end
