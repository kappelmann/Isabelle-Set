theory mizar_ty_old
imports mizar
begin

named_theorems ex
declare object_exists[ex]
(*declare object_exists[ex del]*)

(*local_setup {*
Context.proof_map (Named_Theorems.add_thm "mizar_ty.ex" @{thm refl})
*}*)
ML {*
structure Miz_Ty_Data = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);
structure Miz_Ty_Func_Data = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);
structure Miz_Ty_Clus_Data = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);
structure Miz_Ty_Fwd_Data = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);
*}

(* premises are filled with "ty" and singletons from "ty_func"
   We return theorems with missing premises*)
ML {*
fun fast_prove_prems_fromr ctxt th =
  let
(*    val _ = tracing ("fpp:" ^ Thm.string_of_thm ctxt th)*)
    val ty = @{thm object_root} :: Proof_Context.get_thms ctxt "ty";
    val ty_func = filter (fn th => Thm.nprems_of th = 0) (Proof_Context.get_thms ctxt "ty_func");
    fun dorl ths =
      if Thm.nprems_of (hd ths) = 0 then hd ths
      else
        let val rlres = ((ty @ ty_func) RLN (Thm.nprems_of (hd ths), ths))
        in case rlres of [] => hd ths | _ => dorl rlres end
  in dorl [th] end;
*}

ML {*
fun is_in_ty thm ctxt =
  let
    val there = Item_Net.retrieve (Miz_Ty_Data.get (Context.Proof ctxt)) (Thm.concl_of thm)
(*    val _ = if length there2 > 0 then tracing (@{make_string} (Thm.prop_of thm, Thm.prop_of (hd there))) else ()*)
  in
    filter (fn p => p aconv (Thm.concl_of thm)) (map Thm.concl_of there) <> []
  end
*}
(* Derive all 'is' and 'not is' types of 'tm' by matching with conclusion of theorem ith *)
ML {*
fun mty_tm_thm tm ith ctxt =
  let
    val itm =
      case dest_Trueprop (Thm.concl_of ith) of
        (Const (@{const_name ty_membership}, _)) $ itm $ _ => itm
      | Const (@{const_name Not}, _) $ ((Const (@{const_name ty_membership}, _)) $ itm $ _) => itm
      | _ => raise ERROR "mty_tm_thm: incorrect thm conclusion"
  in
    (*if fst (Term.strip_comb itm) <> fst (Term.strip_comb tm) then []
    else*) (let
      val ct = Thm.cterm_of ctxt tm
      val ict = Thm.cterm_of ctxt itm
(*      val _ = tracing ("try:" ^ Thm.string_of_thm ctxt ith)*)
      val inst = Thm.first_order_match (ict, ct)
      val ith2 = Thm.instantiate inst ith
(*      val _ = tracing ("syc0:" ^ Thm.string_of_thm ctxt ith2)*)
      (* Pre-test, even before trying to prove and fill potential holes *)
      val _ = if is_in_ty ith2 ctxt then raise Pattern.MATCH else ()
(*      val _ = tracing ("syc:" ^ Thm.string_of_thm ctxt ith2)*)
      val th = (*asm_full_simplify*) fast_prove_prems_fromr ctxt ith2
(*      val _ = tracing ("syc2<:" ^ Thm.string_of_thm ctxt th)*)
      val _ = if (Item_Net.member o Miz_Ty_Data.get) (Context.Proof ctxt) th then raise Pattern.MATCH else ()
(*      val _ = tracing ("syc2>:" ^ Thm.string_of_thm ctxt th)*)
     in
       if Thm.concl_of th <> @{prop True} andalso Thm.nprems_of th = 0 then [th] else []
     end)
     handle Pattern.MATCH => []
   end
*}

(* When adding a theorem th1 to "ty" we use theorems from "ty_fwd".
   Last premise is instantiated with th1.
 *)
ML {*
fun ty_compute_fwd ctxt thm =
  let
    fun tryt th =
      let
        val th = thm RSN (Thm.nprems_of th, th)
      in
        [fast_prove_prems_fromr ctxt th]
        handle Empty => []
      end
      handle THM _ => []
           | ERROR _ => []
    val ty_fwd = Proof_Context.get_thms ctxt "ty_cond_cluster";
  in
    flat (map tryt ty_fwd)
  end
*}

ML {*
fun fold_sets f (t as Const (_, @{typ Set})) = f t
  | fold_sets f (t as Free (_, @{typ Set})) = f t
  | fold_sets f (tm as t $ u) =
     if fastype_of tm = @{typ Set} then
       case strip_comb t of
         (Const ("mizar_struct.aggr", _), _) => fold_sel f tm #> f tm
         | _ => fold_sets f t #> fold_sets f u #> f tm
     else fold_sets f t #> fold_sets f u
  | fold_sets _ _ = I
and fold_sel f ((Const ("mizar_struct.sel_t", _) $ _ $ t)) = fold_sets f t
  | fold_sel f (t $ u) = fold_sel f t #> fold_sel f u
  | fold_sel _ _ = I
*}


ML {*
fun conj_elims th =
  (case dest_Trueprop (Thm.concl_of th) of
    (Const (@{const_name conj}, _) $ _ $ _) =>
      conj_elims (th RS @{thm conjunct1}) @
      conj_elims (th RS @{thm conjunct2})
  | _ => [th])
  handle TERM _ => [th]
*}

ML {*
(* For every term in tms, add to the context all typings derivable for every typable subterm of the term. Return the final augmented context. *)
fun mty_tms ty_add_thm tms ctxt =
  let
(*    val _ = tracing ("mty:" ^ space_implode " " (map (Pretty.string_of o Syntax.pretty_term ctxt) tms))*)
    val ty_func = Proof_Context.get_thms ctxt "ty_func";
    val ty_clus = Proof_Context.get_thms ctxt "ty_func_cluster";

    fun do_mty tm th (sfnew, ctxt) =
      let
        val new = mty_tm_thm tm th ctxt
(*        val _ = if length new > 0 then tracing (string_of_int (length new)) else ()*)
      in
        (sfnew orelse length new > 0, Context.proof_map (fold ty_add_thm new) ctxt)
      end

    (* I think do_tm repeatedly derives and adds new typings to the context until there are no more *)
    fun do_tm tm (ctxt, sf) =
      if Termtab.defined sf tm orelse maxidx_of_term tm <> ~1 then (ctxt, sf) else
      let
(*        val _ = tracing ("mty_do:" ^ Pretty.string_of (Syntax.pretty_term ctxt tm))*)
        val (new, ctxt2) = fold (do_mty tm) (ty_clus @ ty_func) (false, ctxt)
      in
        if new then do_tm tm (ctxt2, sf) else (ctxt2, Termtab.update (tm, ()) sf)
      end

    fun do_subtms tm (ctxt, sf) = fold_sets do_tm tm (ctxt, sf)
  in
    fst (fold do_subtms tms (ctxt, Termtab.empty))
  end
*}
ML {*
fun simp_thm thm ctxt =
  let
    val pctxt = Context.proof_of ctxt
    val ths = conj_elims (Object_Logic.rulify pctxt (Simplifier.full_simplify (put_simpset main_ss pctxt addsimps @{thms ty_intersection non_property object_root}) thm))
  in
    filter (fn th => not (Term.is_Const (dest_Trueprop (Thm.concl_of th)))) ths
  end
*}
ML {*
fun ty_func_add_thm thm ctxt =
  fold (fn th => Miz_Ty_Func_Data.map (Item_Net.update th)) (simp_thm thm ctxt) ctxt
fun ty_clus_add_thm thm ctxt =
  fold (fn th => Miz_Ty_Clus_Data.map (Item_Net.update th)) (simp_thm thm ctxt) ctxt
fun ty_fwd_add_thm thm ctxt =
  fold (fn th => Miz_Ty_Fwd_Data.map (Item_Net.update th)) (simp_thm thm ctxt) ctxt
fun ty_add_nofwd thm ctxt =
  let
(*    val _ = tracing ("tanf: " ^ Thm.string_of_thm (Context.proof_of ctxt) thm)*)
    val ctxt = Miz_Ty_Data.map (Item_Net.update thm) ctxt
    val ctxt = Simplifier.map_ss (fn ctxt => ctxt addsimps [thm]) ctxt
    fun fast_ty_add thm ctxt = ctxt |> ty_add_nofwd thm |> ty_add_consequences_ok thm
    fun nonot (Const (@{const_name Not}, _) $ t) = t
      | nonot t = t
  in
(*    Simplifier.map_ss (mty_tms fast_ty_add [(snd o dest_comb o nonot o dest_Trueprop) (Thm.prop_of thm)])*)
    ctxt
    handle TERM _ => ctxt
  end

and ty_add_consequences_ok thm ctxt =
  let
    val pctxt = Context.proof_of ctxt
    val todos0 = ty_compute_fwd pctxt thm
    val todos1 = filter (fn th => Thm.nprems_of th = 0) todos0
    val to_fwd = filter_out (fn th => Thm.nprems_of th = 0) todos0
(*    val _ = map warning (map (fn th => Thm.string_of_thm pctxt th) to_fwd)*)
(*    val _ = (case to_fwd of [] => () | _ => warning (string_of_int (length to_fwd)))*)
    val ctxt = fold ty_fwd_add_thm to_fwd ctxt
    val todos = filter (fn th => not ((Item_Net.member o Miz_Ty_Data.get) ctxt th)) todos1;
(*    val _ = map (fn th => tracing ("conseq" ^ Thm.string_of_thm pctxt th)) todos*)
    val ctxt = fold ty_add_nofwd todos ctxt
  in fold ty_add_consequences_ok todos ctxt end;

fun fast_ty_add thm ctxt =
  ctxt |> ty_add_nofwd thm |> ty_add_consequences_ok thm

fun ty_add_consequences thm ctxt =
  case Thm.prop_of thm of
    Const (@{const_name Trueprop}, _) $ (Const (@{const_name ty_membership},_) $ _ $ _) =>
      ty_add_consequences_ok thm ctxt
  | Const (@{const_name Trueprop}, _) $ (Const (@{const_name Not}, _) $ (Const (@{const_name ty_membership},_) $ _ $ _)) =>
      ty_add_consequences_ok thm ctxt
  | Const (@{const_name Trueprop}, _) $ (Const (@{const_name True}, _)) => ctxt
  | _ => (warning ("Not a simple justification added to ty. ty_fwd \<not> computed: " ^ Thm.string_of_thm (Context.proof_of ctxt) thm); ctxt)

fun ty_add_thm thm ctxt =
  let
    val pctxt = Context.proof_of ctxt
(*    val _ = map (fn th => tracing ("add0" ^ Thm.string_of_thm pctxt th)) [thm]*)
    val thms = rev (conj_elims thm)
(*    val _ = map (fn th => tracing ("add1" ^ Thm.string_of_thm pctxt th)) thms*)
    fun simp thm = (conj_elims (Simplifier.full_simplify (put_simpset main_ss pctxt addsimps @{thms ty_intersection non_property}) thm))
    val ths0 = rev (flat (map simp thms));
(*    val _ = map (fn th => tracing ("add2" ^ Thm.string_of_thm pctxt th)) ths0*)
    val ths = filter (fn th => not ((Item_Net.member o Miz_Ty_Data.get) ctxt th)) ths0;
(*    val _ = tracing (string_of_int (length ths0) ^ " / " ^ string_of_int (length ths))*)
    val ctxt = fold ty_add_nofwd ths ctxt
  in fold ty_add_consequences ths ctxt end;

fun ty_del_thm thm ctxt = Miz_Ty_Data.map (Item_Net.remove thm) ctxt;

fun add_or_del aod_fn = Thm.declaration_attribute (fn thm => fn ctxt => aod_fn thm ctxt);

val ty_attrib = Attrib.add_del (add_or_del ty_add_thm) (add_or_del ty_del_thm)
*}

setup {* Attrib.setup @{binding "ty"} ty_attrib "Declare as Mizar type local type" *}
setup {* Global_Theory.add_thms_dynamic (@{binding "ty"}, (Item_Net.content o Miz_Ty_Data.get)) *}

ML {*
fun ty_func_del_thm thm ctxt = Miz_Ty_Func_Data.map (Item_Net.remove thm) ctxt;
fun ty_clus_del_thm thm ctxt = Miz_Ty_Clus_Data.map (Item_Net.remove thm) ctxt;
fun ty_fwd_del_thm thm ctxt = Miz_Ty_Clus_Data.map (Item_Net.remove thm) ctxt;

fun add_or_del aod_fn = Thm.declaration_attribute (fn thm => fn ctxt => aod_fn thm ctxt);

val ty_func_attrib = Attrib.add_del (add_or_del ty_func_add_thm) (add_or_del ty_func_del_thm);
val ty_clus_attrib = Attrib.add_del (add_or_del ty_clus_add_thm) (add_or_del ty_clus_del_thm)
val ty_fwd_attrib = Attrib.add_del (add_or_del ty_fwd_add_thm) (add_or_del ty_fwd_del_thm)
*}

setup {* Attrib.setup @{binding "ty_func"} ty_func_attrib "Declare as Mizar functor rule" *}
setup {* Global_Theory.add_thms_dynamic (@{binding "ty_func"}, (Item_Net.content o Miz_Ty_Func_Data.get)) *}

setup {* Attrib.setup @{binding "ty_func_cluster"} ty_clus_attrib "Declare as Mizar cluster rule" *}
setup {* Attrib.setup @{binding "ty_parent"} ty_fwd_attrib "Declare as Mizar cluster rule" *}
setup {* Global_Theory.add_thms_dynamic (@{binding "ty_func_cluster"}, (Item_Net.content o Miz_Ty_Clus_Data.get)) *}
setup {* Global_Theory.add_thms_dynamic (@{binding "ty_parent"}, (Item_Net.content o Miz_Ty_Fwd_Data.get)) *}

setup {* Attrib.setup @{binding "ty_cond_cluster"} ty_fwd_attrib "Declare as Mizar fwd rule" *}
setup {* Global_Theory.add_thms_dynamic (@{binding "ty_cond_cluster"}, (Item_Net.content o Miz_Ty_Fwd_Data.get)) *}

(*
consts empty :: Ty
consts finite :: Ty
consts bla :: Ty
consts set :: Ty
lemma [ty_cond_cluster]: "x is empty \<Longrightarrow> x is finite" sorry
lemma [ty_cond_cluster]: "x is finite \<Longrightarrow> x is bla" sorry
lemma
  assumes [ty]: "a is empty \<bar> set"
  shows "x"
thm ty
oops
*)

ML {*
fun get_ty_prems ctxt =
  let fun ffun th =
    (case dest_Trueprop (Thm.prop_of th) of
    (Const (@{const_name ty_membership},_) $ _ $ _) => true
  | (Const (@{const_name Not}, _) $ (Const (@{const_name ty_membership}, _) $ _ $ _)) => true
  | _ => false)
  handle TERM _ => false
(*  val _ = tracing (string_of_int (length (Simplifier.prems_of ctxt)))*)
  in filter ffun (Simplifier.prems_of ctxt) end
*}

simproc_setup ex_simp ("inhabited(x)") = {*
  fn _ => fn ctxt => fn ct =>
    let
(*      val _ = tracing "in_simproc"*)
      val ty_prems = get_ty_prems ctxt
(*      val _ = map (tracing o @{make_string} o Thm.prop_of) ty_prems*)
      val ctxt = Context.proof_map (fold ty_add_thm ty_prems) ctxt
      val ex = Proof_Context.get_thms ctxt "ex";
      val ty = Proof_Context.get_thms ctxt "ty";
      val ty_func = Proof_Context.get_thms ctxt "ty_func";
      val th = Simplifier.asm_full_rewrite (put_simpset main_ss ctxt addsimps ty addsimps ty_func addsimps ex) ct;
      val ((_ $ _) $ r) = Thm.prop_of th;
    in
      if r = @{term True} orelse r = @{term False} then SOME th else NONE
    end
*}

ML {*
fun mby_tac ths ctxt facts i th =
  let
    val ty = Proof_Context.get_thms ctxt "ty";
    fun do_simped_th n th =
      if n = 0 then [th] else
      case nth (Thm.prems_of th) (n - 1) of
        (Const (@{const_name Trueprop}, _) $ ((Const (@{const_name ty_membership}, _) $ _ $ _))) =>
          flat (map (do_simped_th (n - 1)) (ty RLN (n, [th])))
      | (Const (@{const_name Trueprop}, _) $ (Const (@{const_name Not}, _) $ ((Const (@{const_name ty_membership}, _) $ _ $ _)))) =>
          flat (map (do_simped_th (n - 1)) (ty RLN (n, [th])))
      | _ => do_simped_th (n - 1) th
    fun do_th th =
      let
        val simp_th = Simplifier.full_simplify ((put_simpset basic_ss ctxt) addsimps @{thms ty_intersection non_property}) th
        val rsth = Object_Logic.rulify ctxt simp_th
        val sith = do_simped_th (Thm.nprems_of rsth) rsth
      in
        case sith of [] => [th] | _ => sith
      end;
    val ths2 = flat (map do_th (ths @ facts));
   in
     Method.insert_tac ctxt ((*ths @ facts @ *) ths2) i th
  end
*}

ML {*
fun mty ths facts ctxt th =
  mty_tms fast_ty_add (map Thm.prop_of (th :: facts @ ths)) ctxt;
fun mty_tac ths ctxt facts = Method.insert_tac ctxt (ths @ facts);
fun mty_method ths _ facts (ctxt, th) =
  let
(*    val _ = tracing (Syntax.string_of_term ctxt (Thm.prop_of th))*)
    val ctxt = mty ths facts ctxt th
  in
    (METHOD oo (ALLGOALS ooo mty_tac)) ths ctxt facts (ctxt, th)
  end
*}

ML {*
val _ =
  Theory.setup
    (Method.setup @{binding mty}
      (Attrib.thms >> (mty_method))
      "Mty")
*}
ML {*
fun mby_method ths _ facts (ctxt, th) =
  let val ctxt = mty ths facts ctxt th
  in (METHOD oo (ALLGOALS ooo mby_tac)) ths ctxt facts (ctxt, th)
  end
val _ =
  Theory.setup
    (Method.setup @{binding mby}
      (Attrib.thms >> mby_method)
      "Mby")
fun mauto_method ths _ facts (ctxt, th) =
  let val ctxt = mty ths facts ctxt th
   val tac = (mby_tac ths ctxt facts)
  in METHOD (fn _ => ALLGOALS tac THEN Clasimp.auto_tac ctxt) facts (ctxt, th)
  end
val _ =
  Theory.setup
    (Method.setup @{binding mauto}
      (Attrib.thms >> mauto_method)
      "Mauto")
(*fun mauto_method ths _ facts (ctxt, th) =
  let val ctxt = mty ths facts ctxt th
  in METHOD (fn _ => ALLGOALS (Method.insert_tac ctxt (ths@facts)) THEN Clasimp.auto_tac ctxt) facts (ctxt, th)
  end
val _ =
  Theory.setup
    (Method.setup @{binding mauto}
      (Attrib.thms >> mauto_method)
      "Mauto")*)
*}

method ty = (simp only: ty ty_func)

end
