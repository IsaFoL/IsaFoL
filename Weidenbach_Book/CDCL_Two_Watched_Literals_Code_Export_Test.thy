theory CDCL_Two_Watched_Literals_Code_Export_Test
  imports CDCL_Two_Watched_Literals_List_Simple_Code
begin

schematic_goal valued_impl: "RETURN ?c \<le> valued M L"
  unfolding unit_propagation_inner_loop_body_l_def valued_def Let_def
  apply (refine_transfer find_unwatched_impl)
  done

concrete_definition valued_impl uses valued_impl

prepare_code_thms valued_impl_def
export_code valued_impl in SML

declare find_unwatched_impl[refine_transfer] valued_impl[refine_transfer]
schematic_goal unit_propagation_inner_loop_body_list: "RETURN ?c \<le> unit_propagation_inner_loop_body_l L C S"
  unfolding unit_propagation_inner_loop_body_l_def
  apply refine_transfer
  done

(*
To generate code, remove assertions!
concrete_definition backtrack_l''_impl uses
  backtrack_l'_def
prepare_code_thms backtrack_l''_impl_def
thm backtrack_l''_impl_def
export_code backtrack_l''_impl in Haskell *)
term nat_assn

term valued
term nfoldli

definition valued'  :: "('a, 'b) ann_lit list \<Rightarrow> 'a literal \<Rightarrow> bool option nres" where
  \<open>valued' M L = nfoldli [0..<length M]
  (\<lambda>v. is_None v)
  (\<lambda>i v.
    do {
      if True (* atm_of (lit_of (op_list_get M i)) = atm_of L *)
      then
        if op_list_get M i = op_list_get M i
        then do {RETURN (Some True)}
        else do {RETURN (Some False)}
      else do {RETURN (None)}
    })
  None\<close>

definition test :: "('a, 'b) ann_lit list \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>test M i = do {ASSERT(i < length M); RETURN (op_list_get M i = op_list_get M i)}\<close>

sepref_register \<open>valued\<close>

term set_rel term map2

type_synonym lit_refined = \<open>int\<close>


record lit_prop = lvl :: nat cause :: nat

type_synonym trail_refined = \<open>lit_refined list \<times> nat option list \<times> int list\<close>

fun lit_of_refined :: \<open>int \<Rightarrow> nat literal\<close> where
  \<open>lit_of_refined n = (if n < 0 then Neg (nat (-n)) else Pos (nat n))\<close>

context
  fixes N :: nat
begin

fun trail_of_refined :: "(nat, nat) ann_lit list \<Rightarrow> trail_refined \<Rightarrow> bool" where
  \<open>trail_of_refined M (Ls, Ls', _) \<longleftrightarrow>
    map2
      (\<lambda>L n. if n = None then Decided (lit_of_refined L) else Propagated (lit_of_refined L) (the n))
      (rev Ls) (rev Ls') =  M\<close>

  term trail_rel
definition trail_ref_rel :: "(trail_refined \<times> (nat, nat) ann_lits) set" where trail_rel_def_internal:
  \<open>trail_ref_rel = {((lit_order, reasons, assignement), M). trail_of_refined M (lit_order, reasons, assignement) \<and>
     length reasons = length lit_order(*  \<and>
     (\<forall>L. lit_of_refined L \<in> lits_of_l M \<longrightarrow> sgn (assignement!(nat (abs L))) = sgn L) *)}\<close>

lemmas trail_ref_rel_def[refine_rel_defs] = trail_rel_def_internal

fun assign_lit :: \<open>(nat, nat) ann_lit \<Rightarrow> trail_refined \<Rightarrow> trail_refined\<close> where
  \<open>assign_lit (Propagated (Pos L) C) (lit_order, reasons, assignement) =
     (lit_order @ [(int L)], reasons @ [Some C], list_update assignement L (abs (assignement ! L)))\<close>
|  \<open>assign_lit (Propagated (Neg L) C) (lit_order, reasons, assignement) =
     (lit_order @ [-(int L)], reasons @ [Some C], list_update assignement L (-abs (assignement ! L)))\<close>
|  \<open>assign_lit (Decided (Pos L)) (lit_order, reasons, assignement) =
     (lit_order @ [(int L)], reasons @ [None], list_update assignement L (-abs (assignement ! L)))\<close>
|  \<open>assign_lit (Decided (Neg L)) (lit_order, reasons, assignement) =
     (lit_order @ [-(int L)], reasons @ [None], list_update assignement L (-abs (assignement ! L)))\<close>

fun assign_Decided_lit :: \<open>int \<Rightarrow> trail_refined \<Rightarrow> trail_refined\<close> where
   \<open>assign_Decided_lit L (lit_order, reasons, assignement) =
     (lit_order @ [L], reasons @ [None], list_update assignement (nat (abs L)) (-abs (assignement ! nat (abs L))))\<close>

definition ann_lit_rel where ann_lit_rel_def_internal:
  "ann_lit_rel R \<equiv> {(l,l'). rel_ann_lit (\<lambda>x x'. (x,x')\<in>fst R) (\<lambda>x x'. (x,x')\<in>snd R) l l'}"

abbreviation literal_rel :: "(nat literal \<times> nat literal) set" where
"literal_rel \<equiv> Id::(nat literal \<times>_) set"

definition nat_lit_int_assn :: "nat literal \<Rightarrow> int \<Rightarrow> assn" where
  \<open>nat_lit_int_assn = pure {(L', L). L = lit_of_refined L'}\<close>

sepref_decl_op Pos': "Pos :: nat \<Rightarrow> nat literal" ::  "nat_rel \<rightarrow> literal_rel" .

lemma [def_pat_rules]:
  "Pos \<equiv> op_Pos'"
  by auto

term id_assn

definition literal_assn where
"literal_assn \<equiv> hr_comp nat_assn {(L', L). L = lit_of_refined L'}"

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "literal_assn"]

lemma [sepref_import_param]: \<open>(RETURN \<circ> Pos, RETURN o Pos) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: nres_rel_def)

end

context
  notes [fcomp_norm_unfold] = literal_assn_def[symmetric]
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI] frefI
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin
  lemma int_Pos_refine[sepref_fr_rules]: \<open>(return o int, RETURN o op_Pos') \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_int_assn\<close>
    unfolding nat_lit_int_assn_def by sep_auto
  sepref_decl_impl trscp: int_Pos_refine .
end
term test

definition test2 :: \<open>nat \<Rightarrow> nat literal nres\<close> where
  \<open>test2 n = do {ASSERT (n > 0);  RETURN (Pos n)}\<close>
term arl_length

sepref_definition test' is test2 :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_int_assn\<close>
  unfolding test2_def
  apply sepref
  done

sepref_decl_intf nat_lit is "nat literal"

(* lemma [sepref_import_param]: \<open>(RETURN \<circ> Pos, RETURN o Pos) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: nres_rel_def) *)


definition nat_lits_trail_assn :: "(nat, nat) ann_lit list \<Rightarrow> trail_refined \<Rightarrow> assn" where
  \<open>nat_lits_trail_assn = pure trail_ref_rel\<close>

sepref_decl_op cons_Decided_lit': "(\<lambda>L M. Decided L # M) :: nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits" ::
   "(Id :: (nat literal \<times> _) set ) \<rightarrow> (Id :: ((nat, nat) ann_lits \<times> _) set) \<rightarrow>
   (Id :: ((nat, nat) ann_lits \<times> _) set)"
    .


lemma assign_lit_cons_trail_ref_rel:
  \<open>((aa, ab, b), ba) \<in> trail_ref_rel \<Longrightarrow> 0 < atm_of (lit_of a) \<Longrightarrow>
  (assign_lit a (aa, ab, b), a # ba) \<in> trail_ref_rel\<close>
  unfolding trail_ref_rel_def
  apply (cases a; cases \<open>lit_of a\<close>)
  by auto

lemma assign_Decided_lit_cons_trail_ref_rel:
  \<open>ai < 0 \<Longrightarrow>
       ((a, aa, ba), b) \<in> trail_ref_rel \<Longrightarrow>
       (ab, bb) \<Turnstile> emp \<Longrightarrow>
       ((a @ [ai], aa @ [None], ba[nat (- ai) := - \<bar>ba ! nat (- ai)\<bar>]),
        Decided (Neg (nat (- ai))) # b)
       \<in> trail_ref_rel\<close>
  \<open>0 < ai \<Longrightarrow>
       ((a, aa, ba), b) \<in> trail_ref_rel \<Longrightarrow>
       (ab, bb) \<Turnstile> emp \<Longrightarrow>
       ((a @ [ai], aa @ [None], ba[nat ai := - \<bar>ba ! nat ai\<bar>]),
        Decided (Pos (nat ai)) # b)
       \<in> trail_ref_rel\<close>
  unfolding trail_ref_rel_def
  by auto

context
  notes [fcomp_norm_unfold] = array_assn_def[symmetric]
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def is_array_def invalid_assn_def
begin
term \<open> (\<lambda>a b. nat_lit_int_assn b a)\<close>
lemma assign_lit[sepref_fr_rules]:
  \<open>(uncurry (return oo assign_Decided_lit), uncurry (RETURN oo op_cons_Decided_lit')) \<in>
    [\<lambda>(L :: nat literal, M). atm_of L \<noteq> 0]\<^sub>a (\<lambda>a b. nat_lit_int_assn a b)\<^sup>k *\<^sub>a nat_lits_trail_assn\<^sup>d \<rightarrow> nat_lits_trail_assn\<close>
  unfolding nat_lits_trail_assn_def
  by sepref_to_hoare (sep_auto simp: nat_lit_int_assn_def assign_Decided_lit_cons_trail_ref_rel)

thm HOL_list_prepend_hnr[sepref_fr_rules]

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "nat_lits_trail_assn"]
sepref_decl_impl trscp2: assign_lit
  apply auto
  .

end

lemma [def_pat_rules]:
  \<open>op # $ (Decided $ L) $ M \<equiv> op_cons_Decided_lit' $ L $ M\<close>
  by auto
thm def_pat_rules

text \<open>We don't want to use the translation to \<^term>\<open>op_cons_lit'\<close> instead of
  \<^term>\<open>op_list_prepend\<close>:\<close>
declare Sepref_Id_Op.def_pat_rules(47)[def_pat_rules del]

definition test3 :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>test3 L M = do {ASSERT (atm_of L > 0);  RETURN (Decided L # M)}\<close>

definition positive_lit_id where
  \<open>positive_lit_id = pure {(L', L). L = L' \<and>  atm_of (lit_of L) > 0}\<close>

sepref_definition test_42 is \<open>uncurry test3\<close> :: \<open>nat_lit_int_assn\<^sup>k *\<^sub>a nat_lits_trail_assn\<^sup>d \<rightarrow>\<^sub>a nat_lits_trail_assn\<close>
  unfolding test3_def
  apply sepref
  done

definition rand_nat :: \<open>nat \<Rightarrow> nat nres\<close> where
  \<open>rand_nat n = SPEC (\<lambda>m. m \<le> n)\<close>
sepref_register rand_nat
(* sepref_decl_op rand_nat: rand_nat :: \<open>(Id :: (nat\<times>nat) set) \<rightarrow> (Id :: (nat \<times> nat) set)\<close>
  apply (auto simp: rand_nat_def)
  sorry
 *)


definition rand_nat_stgy1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>rand_nat_stgy1 _ = 0\<close>

context
  notes [fcomp_norm_unfold] = array_assn_def[symmetric]
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def is_array_def invalid_assn_def
begin
term \<open> (\<lambda>a b. nat_lit_int_assn b a)\<close>

definition \<open>nat_pair \<equiv> pure {(m, n). True}\<close>

lemma rand_nat_stgy[sepref_fr_rules]:
  \<open>(return o rand_nat_stgy1, rand_nat) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
    apply (clarsimp intro!: nres_relI)
  unfolding rand_nat_def rand_nat_stgy1_def nat_pair_def
  by (sep_auto simp: rand_nat_def rand_nat_stgy1_def)

end


definition rand_rand :: \<open>nat \<Rightarrow> nat nres\<close> where
  \<open>rand_rand n = do {n' \<leftarrow> rand_nat n; RETURN n'}\<close>

sepref_definition rand_nat_stgy_test is rand_rand :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding rand_rand_def
  apply sepref
  done

end