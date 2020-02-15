theory IsaSAT_Literals_LLVM
  imports WB_More_Word IsaSAT_Literals Watched_Literals.WB_More_IICF_LLVM
begin

(* TODO: Move *)
lemma inline_ho[llvm_inline]: \<open>doM { f \<leftarrow> return f; m f } = m f\<close> for f :: \<open>_ \<Rightarrow> _\<close> by simp



(* TODO: Move
  TODO:  Write generic postprocessing for that!
  Maybe just beta contraction of form (\<lambda>x. f x)$x = f$x
*)
lemma RETURN_comp_5_10_hnr_post[to_hnr_post]:
  \<open>(RETURN ooooo f5)$a$b$c$d$e = RETURN$(f5$a$b$c$d$e)\<close>
  \<open>(RETURN oooooo f6)$a$b$c$d$e$f = RETURN$(f6$a$b$c$d$e$f)\<close>
  \<open>(RETURN ooooooo f7)$a$b$c$d$e$f$g = RETURN$(f7$a$b$c$d$e$f$g)\<close>
  \<open>(RETURN oooooooo f8)$a$b$c$d$e$f$g$h = RETURN$(f8$a$b$c$d$e$f$g$h)\<close>
  \<open>(RETURN ooooooooo f9)$a$b$c$d$e$f$g$h$i = RETURN$(f9$a$b$c$d$e$f$g$h$i)\<close>
  \<open>(RETURN oooooooooo f10)$a$b$c$d$e$f$g$h$i$j = RETURN$(f10$a$b$c$d$e$f$g$h$i$j)\<close>
  \<open>(RETURN o\<^sub>1\<^sub>1 f11)$a$b$c$d$e$f$g$h$i$j$k = RETURN$(f11$a$b$c$d$e$f$g$h$i$j$k)\<close>
  \<open>(RETURN o\<^sub>1\<^sub>2 f12)$a$b$c$d$e$f$g$h$i$j$k$l = RETURN$(f12$a$b$c$d$e$f$g$h$i$j$k$l)\<close>
  \<open>(RETURN o\<^sub>1\<^sub>3 f13)$a$b$c$d$e$f$g$h$i$j$k$l$m = RETURN$(f13$a$b$c$d$e$f$g$h$i$j$k$l$m)\<close>
  \<open>(RETURN o\<^sub>1\<^sub>4 f14)$a$b$c$d$e$f$g$h$i$j$k$l$m$n = RETURN$(f14$a$b$c$d$e$f$g$h$i$j$k$l$m$n)\<close>
  by simp_all


(*  TODO/FIXME: Ad-hoc optimizations for large tuples *)
definition [simp,llvm_inline]: \<open>case_prod_open \<equiv> case_prod\<close>
lemmas fold_case_prod_open = case_prod_open_def[symmetric]

lemma case_prod_open_arity[sepref_monadify_arity]:
  \<open>case_prod_open \<equiv> \<lambda>\<^sub>2fp p. SP case_prod_open$(\<lambda>\<^sub>2a b. fp$a$b)$p\<close>
  by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)

lemma case_prod_open_comb[sepref_monadify_comb]:
  \<open>\<And>fp p. case_prod_open$fp$p \<equiv> Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. (SP case_prod_open$fp$p))\<close>
  by (simp_all)

lemma case_prod_open_plain_comb[sepref_monadify_comb]:
  "EVAL$(case_prod_open$(\<lambda>\<^sub>2a b. fp a b)$p) \<equiv>
    Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. case_prod_open$(\<lambda>\<^sub>2a b. EVAL$(fp a b))$p)"
  apply (rule eq_reflection, simp split: list.split prod.split option.split)+
  done

lemma hn_case_prod_open'[sepref_comb_rules]:
  assumes FR: \<open>\<Gamma> \<turnstile> hn_ctxt (prod_assn P1 P2) p' p ** \<Gamma>1\<close>
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk>
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 ** hn_ctxt P2 a2' a2 ** \<Gamma>1) (f a1 a2)
          (\<Gamma>2 a1 a2 a1' a2') R (f' a1' a2')"
  assumes FR2: \<open>\<And>a1 a2 a1' a2'. \<Gamma>2 a1 a2 a1' a2' \<turnstile> hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** \<Gamma>1'\<close>
  shows \<open>hn_refine \<Gamma> (case_prod_open f p) (hn_ctxt (prod_assn P1' P2') p' p ** \<Gamma>1')
                   R (case_prod_open$(\<lambda>\<^sub>2a b. f' a b)$p')\<close> (is \<open>?G \<Gamma>\<close>)
  unfolding autoref_tag_defs PROTECT2_def
  apply1 (rule hn_refine_cons_pre[OF FR])
  apply1 (cases p; cases p'; simp add: prod_assn_pair_conv[THEN prod_assn_ctxt])
  apply (rule hn_refine_cons[OF _ Pair _ entails_refl])
  applyS (simp add: hn_ctxt_def)
  applyS simp using FR2
  by (simp add: hn_ctxt_def)


lemma ho_prod_open_move[sepref_preproc]: \<open>case_prod_open (\<lambda>a b x. f x a b) = (\<lambda>p x. case_prod_open (f x) p)\<close>
  by (auto)


definition \<open>tuple4 a b c d \<equiv> (a,b,c,d)\<close>
definition \<open>tuple7 a b c d e f g \<equiv> tuple4 a b c (tuple4 d e f g)\<close>
definition \<open>tuple13 a b c d e f g h i j k l m \<equiv> (tuple7 a b c d e f (tuple7 g h i j k l m))\<close>

lemmas fold_tuples = tuple4_def[symmetric] tuple7_def[symmetric] tuple13_def[symmetric]

sepref_register tuple4 tuple7 tuple13

sepref_def tuple4_impl [llvm_inline] is \<open>uncurry3 (RETURN oooo tuple4)\<close> ::
  \<open>A1\<^sup>d *\<^sub>a A2\<^sup>d *\<^sub>a A3\<^sup>d *\<^sub>a A4\<^sup>d \<rightarrow>\<^sub>a A1 \<times>\<^sub>a A2 \<times>\<^sub>a A3 \<times>\<^sub>a A4\<close>
  unfolding tuple4_def by sepref

sepref_def tuple7_impl [llvm_inline] is \<open>uncurry6 (RETURN ooooooo tuple7)\<close> ::
  \<open>A1\<^sup>d *\<^sub>a A2\<^sup>d *\<^sub>a A3\<^sup>d *\<^sub>a A4\<^sup>d *\<^sub>a A5\<^sup>d *\<^sub>a A6\<^sup>d *\<^sub>a A7\<^sup>d \<rightarrow>\<^sub>a A1 \<times>\<^sub>a A2 \<times>\<^sub>a A3 \<times>\<^sub>a A4 \<times>\<^sub>a A5 \<times>\<^sub>a A6 \<times>\<^sub>a A7\<close>
  unfolding tuple7_def by sepref

sepref_def tuple13_impl [llvm_inline] is \<open>uncurry12 (RETURN o\<^sub>1\<^sub>3 tuple13)\<close> ::
  "A1\<^sup>d *\<^sub>a A2\<^sup>d *\<^sub>a A3\<^sup>d *\<^sub>a A4\<^sup>d *\<^sub>a A5\<^sup>d *\<^sub>a A6\<^sup>d *\<^sub>a A7\<^sup>d *\<^sub>a A8\<^sup>d *\<^sub>a A9\<^sup>d *\<^sub>a A10\<^sup>d *\<^sub>a A11\<^sup>d *\<^sub>a A12\<^sup>d *\<^sub>a A13\<^sup>d
  \<rightarrow>\<^sub>a A1 \<times>\<^sub>a A2 \<times>\<^sub>a A3 \<times>\<^sub>a A4 \<times>\<^sub>a A5 \<times>\<^sub>a A6 \<times>\<^sub>a A7 \<times>\<^sub>a A8 \<times>\<^sub>a A9 \<times>\<^sub>a A10 \<times>\<^sub>a A11 \<times>\<^sub>a A12 \<times>\<^sub>a A13"
  unfolding tuple13_def by sepref

lemmas fold_tuple_optimizations = fold_tuples fold_case_prod_open



(*
(* TODO: Also for max_unat, and move to default simpset of Sepref! *)
lemma max_snat_numeral[simp]:
  \<open>0 < max_snat n\<close>
  \<open>1 < max_snat n \<longleftrightarrow> n>1\<close>
  \<open>numeral x < max_snat n \<longleftrightarrow> (numeral x ::nat) < 2^(n-1)\<close>
  subgoal by (auto simp: max_snat_def) []
  subgoal unfolding max_snat_def by (metis nat_neq_iff nat_power_eq_Suc_0_iff nat_zero_less_power_iff not_less_eq numerals(2) power_0 zero_less_Suc zero_less_diff)
  subgoal by (auto simp: max_snat_def) []
  done

lemma max_unat_numeral[simp]:
  \<open>0 < max_unat n\<close>
  \<open>1 < max_unat n \<longleftrightarrow> n>0\<close>
  \<open>numeral x < max_unat n \<longleftrightarrow> (numeral x ::nat) < 2^n\<close>
  subgoal by (auto simp: max_unat_def) []
  subgoal unfolding max_unat_def by (metis nat_neq_iff nat_power_eq_Suc_0_iff nat_zero_less_power_iff not_less_eq numerals(2) power_0 zero_less_Suc)
  subgoal by (auto simp: max_unat_def) []
  done
*)

(* TODO: Move!
  TODO: General max functions!
  TODO: Name should be snatN_max

*)
lemma sint64_max_refine[sepref_import_param]: \<open>(0x7FFFFFFFFFFFFFFF, sint64_max)\<in>snat_rel' TYPE(64)\<close>
  apply (auto simp: snat_rel_def snat.rel_def in_br_conv sint64_max_def snat_invar_def)
  apply (auto simp: snat_def)
  done

lemma sint32_max_refine[sepref_import_param]: \<open>(0x7FFFFFFF, sint32_max)\<in>snat_rel' TYPE(32)\<close>
  apply (auto simp: snat_rel_def snat.rel_def in_br_conv sint32_max_def snat_invar_def)
  apply (auto simp: snat_def)
  done

lemma uint64_max_refine[sepref_import_param]: \<open>(0xFFFFFFFFFFFFFFFF, uint64_max)\<in>unat_rel' TYPE(64)\<close>
  apply (auto simp: unat_rel_def unat.rel_def in_br_conv uint64_max_def)
  done

lemma uint32_max_refine[sepref_import_param]: \<open>(0xFFFFFFFF, uint32_max)\<in>unat_rel' TYPE(32)\<close>
  apply (auto simp: unat_rel_def unat.rel_def in_br_conv uint32_max_def)
  done





lemma convert_fref:
  \<open>WB_More_Refinement.fref = Sepref_Rules.frefnd\<close>
  \<open>WB_More_Refinement.freft = Sepref_Rules.freftnd\<close>
  unfolding WB_More_Refinement.fref_def Sepref_Rules.fref_def
  by auto

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

(* TODO: Move *)

abbreviation \<open>uint32_nat_assn \<equiv> unat_assn' TYPE(32)\<close>
abbreviation \<open>uint64_nat_assn \<equiv> unat_assn' TYPE(64)\<close>

abbreviation \<open>sint32_nat_assn \<equiv> snat_assn' TYPE(32)\<close>
abbreviation \<open>sint64_nat_assn \<equiv> snat_assn' TYPE(64)\<close>


lemmas [sepref_bounds_simps] =
  uint32_max_def sint32_max_def
  uint64_max_def sint64_max_def


lemma is_up'_32_64[simp,intro!]: \<open>is_up' UCAST(32 \<rightarrow> 64)\<close> by (simp add: is_up')
lemma is_down'_64_32[simp,intro!]: \<open>is_down' UCAST(64 \<rightarrow> 32)\<close>  by (simp add: is_down')

lemma ins_idx_upcast64:
  \<open>l[i:=y] = op_list_set l (op_unat_snat_upcast TYPE(64) i) y\<close>
  \<open>l!i = op_list_get l (op_unat_snat_upcast TYPE(64) i)\<close>
  by simp_all

type_synonym 'a array_list32 = \<open>('a,32)array_list\<close>
type_synonym 'a array_list64 = \<open>('a,64)array_list\<close>

abbreviation \<open>arl32_assn \<equiv> al_assn' TYPE(32)\<close>
abbreviation \<open>arl64_assn \<equiv> al_assn' TYPE(64)\<close>


type_synonym 'a larray32 = \<open>('a,32) larray\<close>
type_synonym 'a larray64 = \<open>('a,64) larray\<close>

abbreviation \<open>larray32_assn \<equiv> larray_assn' TYPE(32)\<close>
abbreviation \<open>larray64_assn \<equiv> larray_assn' TYPE(64)\<close>



definition \<open>unat_lit_rel == unat_rel' TYPE(32) O nat_lit_rel\<close>
lemmas [fcomp_norm_unfold] = unat_lit_rel_def[symmetric]

abbreviation unat_lit_assn :: \<open>nat literal \<Rightarrow> 32 word \<Rightarrow> assn\<close> where
  \<open>unat_lit_assn \<equiv> pure unat_lit_rel\<close>

subsection \<open>Atom-Of\<close>

type_synonym atom_assn = \<open>32 word\<close>

definition \<open>atom_rel \<equiv> b_rel (unat_rel' TYPE(32)) (\<lambda>x. x<2^31)\<close>
abbreviation \<open>atom_assn \<equiv> pure atom_rel\<close>

lemma atom_rel_alt: \<open>atom_rel = unat_rel' TYPE(32) O nbn_rel (2^31)\<close>
  by (auto simp: atom_rel_def)

interpretation atom: dflt_pure_option_private \<open>2^32-1\<close> atom_assn \<open>ll_icmp_eq (2^32-1)\<close>
  apply unfold_locales
  subgoal
    unfolding atom_rel_def
    apply (simp add: pure_def fun_eq_iff pred_lift_extract_simps)
    apply (auto simp: unat_rel_def unat.rel_def in_br_conv unat_minus_one_word)
    done
  subgoal proof goal_cases
    case 1
      interpret llvm_prim_arith_setup .
      show ?case unfolding bool.assn_def by vcg'
    qed
  subgoal by simp
  done


lemma atm_of_refine: \<open>(\<lambda>x. x div 2 , atm_of) \<in> nat_lit_rel \<rightarrow> nat_rel\<close>
  by (auto simp: nat_lit_rel_def in_br_conv)


sepref_def atm_of_impl is [] \<open>RETURN o (\<lambda>x::nat. x div 2)\<close>
  :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding atom_rel_def b_assn_pure_conv[symmetric]
  apply (rule hfref_bassn_resI)
  subgoal by sepref_bounds
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemmas [sepref_fr_rules] = atm_of_impl.refine[FCOMP atm_of_refine]


definition Pos_rel :: \<open>nat \<Rightarrow> nat\<close> where
 [simp]: \<open>Pos_rel n = 2 * n\<close>

lemma Pos_refine_aux: \<open>(Pos_rel,Pos)\<in>nat_rel \<rightarrow> nat_lit_rel\<close>
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits)

lemma Neg_refine_aux: \<open>(\<lambda>x. 2*x + 1,Neg)\<in>nat_rel \<rightarrow> nat_lit_rel\<close>
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits)

sepref_def Pos_impl is [] \<open>RETURN o Pos_rel\<close> :: \<open>atom_assn\<^sup>d \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding atom_rel_def Pos_rel_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def Neg_impl is [] \<open>RETURN o (\<lambda>x. 2*x+1)\<close> :: \<open>atom_assn\<^sup>d \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding atom_rel_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

(*sepref_definition Neg_impl is \<open>RETURN o (\<lambda>x. 2*x+1)\<close> :: \<open>[\<lambda>x. x \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref
*)

lemmas [sepref_fr_rules] =
  Pos_impl.refine[FCOMP Pos_refine_aux]
  Neg_impl.refine[FCOMP Neg_refine_aux]

sepref_def atom_eq_impl is \<open>uncurry (RETURN oo (=))\<close> :: \<open>atom_assn\<^sup>d *\<^sub>a atom_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding atom_rel_def
  by sepref


definition value_of_atm :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>value_of_atm A = A\<close>

lemma value_of_atm_rel: \<open>(\<lambda>x. x, value_of_atm) \<in> nat_rel \<rightarrow> nat_rel\<close>
  by (auto)

sepref_def value_of_atm_impl
  is [] \<open>RETURN o (\<lambda>x. x)\<close>
  :: \<open>atom_assn\<^sup>d \<rightarrow>\<^sub>a unat_assn' TYPE(32)\<close>
  unfolding value_of_atm_def atom_rel_def
  by sepref

lemmas [sepref_fr_rules] = value_of_atm_impl.refine[FCOMP value_of_atm_rel]

definition index_of_atm :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>index_of_atm A = value_of_atm A\<close>

lemma index_of_atm_rel: \<open>(\<lambda>x. value_of_atm x, index_of_atm) \<in> nat_rel \<rightarrow> nat_rel\<close>
  by (auto)


sepref_def index_of_atm_impl
  is [] \<open>RETURN o (\<lambda>x. value_of_atm x)\<close>
  :: \<open>atom_assn\<^sup>d \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding index_of_atm_def
  apply (rewrite at \<open>_\<close> eta_expand)
  apply (subst annot_unat_snat_upcast[where 'l=64])
  by sepref

lemmas [sepref_fr_rules] = index_of_atm_impl.refine[FCOMP index_of_atm_rel]

lemma annot_index_of_atm: \<open>xs ! x = xs ! index_of_atm x\<close>
   \<open>xs [x := a] = xs [index_of_atm x := a]\<close>
  by auto

definition index_atm_of where
[simp]: \<open>index_atm_of L = index_of_atm (atm_of L)\<close>

(* TODO: Use at more places! *)
context fixes x y :: nat assumes \<open>NO_MATCH (index_of_atm y) x\<close> begin
  lemmas annot_index_of_atm' = annot_index_of_atm[where x=x]
end

method_setup annot_all_atm_idxs = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD'
    let
      val ctxt = put_simpset HOL_basic_ss ctxt
      val ctxt = ctxt addsimps @{thms annot_index_of_atm'}
      val ctxt = ctxt addsimprocs [@{simproc NO_MATCH}]
    in
      simp_tac ctxt
    end
  )\<close>

lemma annot_index_atm_of[def_pat_rules]:
  \<open>nth$xs$(atm_of$x) \<equiv> nth$xs$(index_atm_of$x)\<close>
  \<open>list_update$xs$(atm_of$x)$a \<equiv> list_update$xs$(index_atm_of$x)$a\<close>
  by auto


sepref_def index_atm_of_impl
  is \<open>RETURN o index_atm_of\<close>
  :: \<open>unat_lit_assn\<^sup>d \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding index_atm_of_def
  by sepref




lemma nat_of_lit_refine_aux: \<open>((\<lambda>x. x), nat_of_lit) \<in> nat_lit_rel \<rightarrow> nat_rel\<close>
  by (auto simp: nat_lit_rel_def in_br_conv)

sepref_def nat_of_lit_rel_impl is [] \<open>RETURN o (\<lambda>x::nat. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  apply (rewrite annot_unat_snat_upcast[where 'l=64])
  by sepref
lemmas [sepref_fr_rules] = nat_of_lit_rel_impl.refine[FCOMP nat_of_lit_refine_aux]

lemma uminus_refine_aux: \<open>(\<lambda>x. x XOR 1, uminus) \<in> nat_lit_rel \<rightarrow> nat_lit_rel\<close>
  apply (auto simp: nat_lit_rel_def in_br_conv bitXOR_1_if_mod_2[simplified])
  subgoal by linarith
  subgoal by (metis dvd_minus_mod even_Suc_div_two odd_Suc_minus_one)
  done

sepref_def uminus_impl is [] \<open>RETURN o (\<lambda>x::nat. x XOR 1)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemmas [sepref_fr_rules] = uminus_impl.refine[FCOMP uminus_refine_aux]

lemma lit_eq_refine_aux: \<open>( (=), (=) ) \<in> nat_lit_rel \<rightarrow> nat_lit_rel \<rightarrow> bool_rel\<close>
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits; auto?; presburger)

sepref_def lit_eq_impl is [] \<open>uncurry (RETURN oo (=))\<close> :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = lit_eq_impl.refine[FCOMP lit_eq_refine_aux]

lemma is_pos_refine_aux: \<open>(\<lambda>x. x AND 1 = 0, is_pos) \<in> nat_lit_rel \<rightarrow> bool_rel\<close>
  by (auto simp: nat_lit_rel_def in_br_conv bitAND_1_mod_2[simplified] split: if_splits)

sepref_def is_pos_impl is [] \<open>RETURN o (\<lambda>x. x AND 1 = 0)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemmas [sepref_fr_rules] = is_pos_impl.refine[FCOMP is_pos_refine_aux]

end
