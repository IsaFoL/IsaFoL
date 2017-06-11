theory CDCL_Two_Watched_Literals_List_Watched_Trail_Code
  imports CDCL_Two_Watched_Literals_List_Watched_Code_Common
begin

notation prod_rel_syn (infixl "\<times>\<^sub>f" 70)

type_synonym trail_int = \<open>(nat, nat) ann_lits \<times> bool option list \<times> nat list \<times> nat\<close>
type_synonym trail_assn = \<open>(uint32 \<times> nat option) list \<times> bool option array \<times> uint32 array \<times> uint32\<close>

type_synonym twl_st_wll_trail =
  "trail_assn \<times> clauses_wl \<times> nat \<times> uint32 array_list option \<times> unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l \<times> watched_wl"

definition valued_atm_on_trail where
  \<open>valued_atm_on_trail M L =
    (if Pos L \<in> lits_of_l M then Some True
    else if Neg L \<in> lits_of_l M then Some False
    else None)\<close>

text \<open>TODO: It would be more performant to have:
   \<^term>\<open>defined_lit M L \<longrightarrow> lvls ! (atm_of L) = get_level M L\<close>\<close>
definition (in twl_array_code_ops) trail_ref :: \<open>(trail_int \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trail_ref = {((M', xs, lvls, k), M). M = M' \<and> no_dup M \<and>
    (\<forall>L \<in># N\<^sub>1. atm_of L < length xs \<and> xs ! (atm_of L) = valued_atm_on_trail M (atm_of L)) \<and>
    (\<forall>L \<in># N\<^sub>1. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1)}\<close>


context twl_array_code
begin

abbreviation (in twl_array_code_ops) trail_conc :: \<open>trail_int \<Rightarrow> trail_assn \<Rightarrow> assn\<close> where
  \<open>trail_conc \<equiv> pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn
      array_assn uint32_nat_assn *assn uint32_nat_assn\<close>

definition cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', xs, lvls, k).
     (Propagated L C # M', xs[atm_of L := Some (is_pos L)],
      lvls[atm_of L := k], k))\<close>

definition (in twl_array_code_ops) trail_assn :: "(nat, nat) ann_lits \<Rightarrow> trail_assn \<Rightarrow> assn" where
  \<open>trail_assn = hr_comp trail_conc trail_ref\<close>

lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst (fst x)\<close>)
    (auto simp: trail_ref_def valued_atm_on_trail_def cons_trail_Propagated_def uminus_lit_swap
      cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update')

lemma is_pos_nat_lit_hnr:
  \<open>(return o (\<lambda>L. bitAND L 1 = 0), RETURN o is_pos) \<in> nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding bitAND_1_mod_2
  apply (sepref_to_hoare, rename_tac x xi, case_tac x)
   apply (sep_auto simp: p2rel_def lit_of_natP_def unat_lit_rel_def uint32_nat_rel_def nat_lit_rel_def br_def
      split: if_splits)+
  by presburger

lemma is_pos_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>L. bitAND L 1 = 0), RETURN o is_pos) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -

  have 1: \<open>(RETURN o (\<lambda>L. bitAND L 1 = 0), RETURN o is_pos) \<in> nat_lit_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding bitAND_1_mod_2
    by (intro nres_relI frefI) (auto simp: nat_lit_rel_def lit_of_natP_def split: if_splits)
  have 2: \<open>(return o (\<lambda>L. bitAND L 1 = 0), RETURN o (\<lambda>L. bitAND L 1 = 0)) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    apply (sepref_to_hoare)
    using nat_of_uint32_ao[of _ 1]
    by (sep_auto simp: p2rel_def lit_of_natP_def unat_lit_rel_def uint32_nat_rel_def
        nat_lit_rel_def br_def nat_of_uint32_012
        nat_of_uint32_0_iff nat_0_AND uint32_0_AND
        split: if_splits)+
  show ?thesis
    using 2[FCOMP 1] unfolding unat_lit_rel_def .
qed

lemma (in -) array_set_hnr_u[sepref_fr_rules]:
    \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 (\<lambda>xs i. heap_array_set xs (nat_of_uint32 i)), uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (array_assn A)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> array_assn A\<close>
  by (sepref_to_hoare)
    (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update)

lemma (in -)array_get_hnr_u[sepref_fr_rules]:
    \<open>CONSTRAINT is_pure A \<Longrightarrow>
(uncurry (\<lambda>xs i. Array.nth xs (nat_of_uint32 i)), uncurry (RETURN \<circ>\<circ> op_list_get))
\<in> [pre_list_get]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> A\<close>
  apply (sepref_to_hoare) -- \<open>TODO proof\<close>
   apply (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
       hr_comp_def list_rel_pres_length list_rel_update param_nth)
  by (metis ent_pure_pre_iff ent_refl_true pair_in_Id_conv param_nth pure_app_eq pure_the_pure)

lemma (in -) distinct_subseteq_iff :
  assumes dist: "distinct_mset M" and fin: "distinct_mset N"
  shows "set_mset M \<subseteq> set_mset N \<longleftrightarrow> M \<subseteq># N"
proof
  assume "set_mset M \<subseteq> set_mset N"
  then show "M \<subseteq># N"
    using dist fin by auto
next
  assume "M \<subseteq># N"
  then show "set_mset M \<subseteq> set_mset N"
    by (metis set_mset_mono)
qed
lemma (in -) nat_of_uint32_add_less_upperN:
  \<open>nat_of_uint32 ai + nat_of_uint32 bi < 2 ^32 \<Longrightarrow>
    nat_of_uint32 (ai + bi) = nat_of_uint32 ai + nat_of_uint32 bi\<close>
  by transfer (auto simp: unat_def uint_plus_if' upperN_def nat_add_distrib)

lemma (in -) uint32_nat_assn_plus[sepref_fr_rules]:
  \<open>(uncurry (return oo op +), uncurry (RETURN oo op +)) \<in> [\<lambda>(m, n). m + n < upperN]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def nat_of_uint32_add_less_upperN upperN_def
      br_def)

lemma undefined_lit_count_decided_upperN:
  assumes
    M_N\<^sub>1: \<open>(\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1)\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close>
  shows \<open>Suc (count_decided M) < upperN\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have \<open>atm_of `# lit_of `# mset (Decided L # M) \<subseteq># remdups_mset (atm_of `# N\<^sub>1)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  from size_mset_mono[OF this] have 1: \<open>count_decided M + 1 \<le> size (remdups_mset (atm_of `# N\<^sub>1))\<close>
    using length_filter_le[of is_decided M] unfolding upperN_def count_decided_def
    by (auto simp del: length_filter_le)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset N\<^sub>1))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># N\<^sub>1 \<Longrightarrow> atm_of xa < upperN div 2\<close> for xa
    using in_N1_less_than_upperN[of xa]
    by (cases xa) (auto simp: upperN_def)
  have \<open>remdups_mset (atm_of `# N\<^sub>1) \<subseteq># mset [0..<upperN div 2]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (auto simp del: literal_of_nat.simps simp: distinct_mset_mset_set)
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset N\<^sub>1) = size (remdups_mset N\<^sub>1)\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# N\<^sub>1)) \<le> upperN div 2\<close>
    by auto

  show ?thesis
    using 1 2 by (auto simp: upperN_def)
qed

sepref_thm cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), (M, xs, lvls, k)). atm_of L < length xs \<and> atm_of L < length lvls]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d\<rightarrow>
    trail_conc\<close>
  unfolding cons_trail_Propagated_tr_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Propagated_tr_code
  uses "twl_array_code.cons_trail_Propagated_tr_code.refine_raw"
  is "(uncurry2 ?f,_)\<in>_"

prepare_code_thms (in -) cons_trail_Propagated_tr_code_def

lemmas cons_trail_Propagated_tr_code[sepref_fr_rules] = cons_trail_Propagated_tr_code.refine[OF twl_array_code_axioms]

lemma cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]:
  \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref)
     (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((L, C), M, xs, lvls, k). atm_of L < length xs \<and> atm_of L < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
                      (pair_nat_ann_lits_assn *assn
                       array_assn (option_assn bool_assn) *assn
                       array_assn uint32_nat_assn *assn uint32_nat_assn)\<^sup>d)
                     (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      trail_ref) \<rightarrow> hr_comp
                                     (pair_nat_ann_lits_assn *assn
                                      array_assn (option_assn bool_assn) *assn
                                      array_assn uint32_nat_assn *assn uint32_nat_assn)
                                     trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_code.refine cons_trail_Propagated_tr,
        OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

fun cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

definition cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Decided_tr = (\<lambda>L (M', xs, lvls, k).
     (Decided L # M', xs[atm_of L := Some (is_pos L)], lvls[atm_of L := k+1], k+1))\<close>

lemma cons_trail_Decided_tr:
  \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst x\<close>)
    (auto simp: trail_ref_def valued_atm_on_trail_def cons_trail_Decided_tr_def
      Decided_Propagated_in_iff_in_lits_of_l nth_list_update' uminus_lit_swap)

lemma (in -) uint32_nat_assn_one:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN 1)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012)
lemma (in -) uint32_nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012)

sepref_thm cons_trail_Decided_tr_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[\<lambda>(L, (M, xs, lvls, k)). atm_of L < length xs \<and> atm_of L < length lvls \<and>
       (\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1) \<and> k = count_decided M \<and> undefined_lit M L \<and> no_dup M \<and>
        L \<in> snd ` D\<^sub>0]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d \<rightarrow>
    trail_conc\<close>
  unfolding cons_trail_Decided_tr_def
  supply [[goals_limit = 1]]
  supply undefined_lit_count_decided_upperN[intro!]
  supply uint32_nat_assn_one[sepref_fr_rules]
  by sepref

concrete_definition (in -) cons_trail_Decided_tr_code
  uses "twl_array_code.cons_trail_Decided_tr_code.refine_raw"
  is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) cons_trail_Decided_tr_code_def

lemmas cons_trail_Decided_tr_code[sepref_fr_rules] = cons_trail_Decided_tr_code.refine[OF twl_array_code_axioms]

lemma cons_trail_Decided_tr_code_cons_trail_Decided_tr[sepref_fr_rules]:
  \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN \<circ>\<circ> cons_trail_Decided))
\<in> [comp_PRE (Id \<times>\<^sub>f trail_ref) (\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, M, xs, lvls, k).
         atm_of L < length xs \<and>
         atm_of L < length lvls \<and>
         (\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1) \<and>
         k = count_decided M \<and> undefined_lit M L \<and> no_dup M \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a
                      (pair_nat_ann_lits_assn *assn
                       array_assn (option_assn bool_assn) *assn
                       array_assn uint32_nat_assn *assn uint32_nat_assn)\<^sup>d)
                     (Id \<times>\<^sub>f
                      trail_ref) \<rightarrow> hr_comp
                                     (pair_nat_ann_lits_assn *assn
                                      array_assn (option_assn bool_assn) *assn
                                      array_assn uint32_nat_assn *assn
                                      uint32_nat_assn)
                                     trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Decided_tr_code.refine cons_trail_Decided_tr, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def image_image intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

definition tl_trail_tr :: \<open>trail_int \<Rightarrow> trail_int\<close> where
  \<open>tl_trail_tr = (\<lambda>(M', xs, lvls, k). (tl M', xs[atm_of (lit_of (hd M')) := None], lvls[atm_of (lit_of (hd M')) := 0],
    if is_decided (hd M') then k-1 else k))\<close>

lemma tl_trail_tr:
  \<open>((RETURN o tl_trail_tr), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
proof -
  have [iff]: \<open>is_proped L \<longleftrightarrow> \<not>is_decided L\<close> for L
    by (cases L) auto
  have [simp]: \<open>is_pos L \<longleftrightarrow> (\<exists>K. L = Pos K)\<close> for L
    by (cases L) auto
  show ?thesis -- \<open>TODO tune proof\<close>
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
     apply (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_def
        Decided_Propagated_in_iff_in_lits_of_l nth_list_update' uminus_lit_swap
        eq_commute[of _ \<open>lit_of _\<close>] atm_of_eq_atm_of get_level_cons_if
        dest: no_dup_consistentD)
    apply (metis literal.exhaust_sel uminus_Pos uminus_Neg)+
    done
qed

sepref_thm tl_trail_tr_code
  is \<open>RETURN o tl_trail_tr\<close>
  :: \<open>[\<lambda>(M, xs, lvls, k). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs \<and>
          atm_of (lit_of (hd M)) < length lvls]\<^sub>a
        trail_conc\<^sup>d \<rightarrow> trail_conc\<close>
  unfolding tl_trail_tr_def
  supply [[goals_limit = 1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_zero[sepref_fr_rules]
  by sepref

concrete_definition (in -) tl_trail_tr_code
  uses twl_array_code.tl_trail_tr_code.refine_raw
  is "(?f,_)\<in>_"

prepare_code_thms (in -) tl_trail_tr_code_def

lemmas tl_trail_tr_coded_refine[sepref_fr_rules] =
   tl_trail_tr_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma tl_trail_tr_code_op_list_tl[sepref_fr_rules]:
  \<open>(tl_trail_tr_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(tl_trail_tr_code, RETURN \<circ> tl)  \<in> [comp_PRE trail_ref (\<lambda>M. M \<noteq> [])
       (\<lambda>_ (M, xs, lvls, k). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs \<and> atm_of (lit_of (hd M)) < length lvls)
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_conc\<^sup>d) trail_ref \<rightarrow>
      hr_comp trail_conc trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_code.refine tl_trail_tr, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed

definition (in twl_array_code_ops) twl_st_l_trail_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_l_trail_assn \<equiv>
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  unit_lits_assn *assn
  unit_lits_assn *assn
  clause_l_assn *assn
  array_watched_assn
  )\<close>

definition (in -) valued_trail :: \<open>trail_int \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
  \<open>valued_trail = (\<lambda>(M, xs, lvls, k) L. do {
     ASSERT(atm_of L < length xs);
     (case xs ! (atm_of L) of
       None \<Rightarrow> RETURN None
     | Some v \<Rightarrow> if is_pos L then RETURN (Some v)
       else RETURN (Some (\<not>v)))
  })\<close>

sepref_thm valued_trail_code
  is \<open>uncurry valued_trail\<close>
  :: \<open>trail_conc\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_trail_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) valued_trail_code
   uses twl_array_code.valued_trail_code.refine_raw
   is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) valued_trail_code_def

lemmas valued_trail_code_valued_refine_code[sepref_fr_rules] =
   valued_trail_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_l_trail_assn_def]

lemma valued_trail_code_valued_refine[sepref_fr_rules]:
  \<open>(uncurry valued_trail_code, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>valued_atm_on_trail M (atm_of L) = (if is_pos L then valued M L else map_option uminus (valued M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: valued_atm_on_trail_def valued_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry valued_trail, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trail_ref \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
      (auto simp: trail_ref_def valued_def valued_trail_def
        split: if_splits option.splits)

  show ?thesis
    using valued_trail_code.refine[FCOMP 2, unfolded trail_assn_def[symmetric],
        OF twl_array_code_axioms] .
qed

definition find_unwatched'' :: "(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> (nat option) nres" where
\<open>find_unwatched'' M N' C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length (N'!C) \<and> (\<forall>j\<in>{2..<i}. -((N'!C)!j) \<in> lits_of_l M) \<and>
    (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M ((N'!C)!j) \<or> (N'!C)!j \<in> lits_of_l M) \<and> j < length (N'!C) \<and> j \<ge> 2)) \<and>
    literals_are_in_N\<^sub>0 (mset (N'!C))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length (N'!C))
    (\<lambda>(_, i). do {
      ASSERT(i < length (N'!C));
      ASSERT((N'!C)!i \<in> snd ` D\<^sub>0);
      case valued M ((N'!C)!i) of
        None \<Rightarrow> do { RETURN (Some i, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some i, i)} else do { RETURN (None, i+1)})
      }
    )
    (None, 2::nat);
   RETURN (fst S)
  }
\<close>
sepref_thm find_unwatched''_code
  is \<open>uncurry2 find_unwatched''\<close>
  :: \<open>[\<lambda>((M, N), C). C < length N]\<^sub>a trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
        option_assn nat_assn\<close>
  unfolding find_unwatched''_def
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
  by sepref

concrete_definition (in -) find_unwatched''_code
  uses "twl_array_code.find_unwatched''_code.refine_raw"
  is "(uncurry2 ?f,_)\<in>_"

prepare_code_thms (in -) find_unwatched''_code_def

lemmas find_unwatched''_code_refine = find_unwatched''_code.refine[of N\<^sub>0]

lemma literals_are_in_N\<^sub>0_in_N\<^sub>1:
  assumes
    N1: \<open>literals_are_in_N\<^sub>0 (mset xs)\<close> and
    i_xs: \<open>i < length xs\<close>
  shows \<open>xs ! i \<in># N\<^sub>1\<close>
proof -
  have \<open>xs ! i \<in># mset xs\<close>
    using i_xs by auto
  then have \<open>xs ! i \<in> set_mset (lits_of_atms_of_m (mset xs))\<close>
    by (auto simp: in_lits_of_atms_of_m_ain_atms_of_iff)
  then show ?thesis
    using N1 unfolding literals_are_in_N\<^sub>0_def by blast
qed

lemma find_unwatched''_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 find_unwatched''_code, uncurry2 find_unwatched') \<in>
     [\<lambda>((M, N), C). literals_are_in_N\<^sub>0 (mset (N!C)) \<and> C < length N]\<^sub>a
     trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
proof -
  have 0: \<open>((None, 2), None, 2) \<in> Id\<close>
    by auto
  have val: \<open>(val, val') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>val = val'\<close> for val val'
    using that by auto
  have 1: \<open>(uncurry2 find_unwatched'', uncurry2 find_unwatched') \<in>
       [\<lambda>((M, N), C). literals_are_in_N\<^sub>0 (mset (N!C))]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
      unfolding find_unwatched''_def find_unwatched'_def uncurry_def
      apply (intro frefI nres_relI)
      apply (refine_vcg 0 val)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: image_image literals_are_in_N\<^sub>0_in_N\<^sub>1)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
  show ?thesis
    using find_unwatched''_code.refine[FCOMP 1, OF twl_array_code_axioms] .
qed

sepref_register unit_propagation_inner_loop_body_wl_D
sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_trail_assn\<close>
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app' watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty twl_st_l_trail_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  unfolding cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]
  by sepref -- \<open>slow!\<close>

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_body_wl_D.refine_raw
   is "(uncurry2 ?f,_)\<in>_"
prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]


sepref_register unit_propagation_inner_loop_wl_loop_D
sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_trail_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding twl_st_l_trail_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def
lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]


sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_inner_loop_wl_D_def twl_st_l_trail_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_D.refine_raw
   is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]


lemma literals_to_update_wll_empty_hnr[unfolded twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(return o (\<lambda>(M, N, U, D, NP, UP, Q, W). is_Nil Q), RETURN o literals_to_update_wl_empty) \<in> twl_st_l_trail_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S'\<close>)
  by (sep_auto simp: twl_st_l_trail_assn_def literals_to_update_wll_empty_def literals_to_update_wl_empty_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil
      split: list.splits)+

concrete_definition (in -) literals_to_update_wll_empty'
   uses twl_array_code.literals_to_update_wll_empty_hnr
   is "(?f,_)\<in>_"

prepare_code_thms (in -) literals_to_update_wll_empty'_def

lemmas literals_to_update_wll_empty'_code[sepref_fr_rules] =
   literals_to_update_wll_empty'.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]

lemma hd_select_and_remove_from_literals_to_update_wl''_refine:
  \<open>(return o (\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q)),
       select_and_remove_from_literals_to_update_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty S]\<^sub>a
    twl_st_l_trail_assn\<^sup>d \<rightarrow> twl_st_l_trail_assn *assn unat_lit_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  let ?int = \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>
  define twl_st_l_interm_rel_1 :: \<open>(_ \<times> nat twl_st_wl) set\<close> where
    \<open>twl_st_l_interm_rel_1 \<equiv> Id \<times>\<^sub>r \<langle>\<langle>Id\<rangle> list_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r
     \<langle>Id\<rangle>option_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r list_mset_rel \<times>\<^sub>r Id\<close>
  have 1:
    \<open>(RETURN o ?int,
       select_and_remove_from_literals_to_update_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> {#}]\<^sub>f
    twl_st_l_interm_rel_1 \<rightarrow> \<langle>twl_st_l_interm_rel_1 \<times>\<^sub>r Id\<rangle>nres_rel\<close>
    unfolding fref_def
    apply clarify
    apply (rename_tac a aa ab ac ad ae af b ag ah ai aj ak al am ba)
    apply (case_tac af)
     apply (auto simp: fref_def nres_rel_def twl_st_l_interm_rel_1_def
        select_and_remove_from_literals_to_update_wl_def RETURN_RES_refine_iff list_mset_rel_def br_def)
    done
  define twl_st_l_interm_assn_2 :: \<open>_ \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
    \<open>twl_st_l_interm_assn_2 \<equiv>
       (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
       conflict_option_assn *assn
       unit_lits_assn *assn
       unit_lits_assn *assn
       list_assn unat_lit_assn *assn
       array_watched_assn
      )\<close>
  have 2:
    \<open>(return o (\<lambda>(M, N, U, D, NP, UP, Q, W). ((M, N, U, D, NP, UP, tl Q, W), hd Q)), RETURN o ?int) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> []]\<^sub>a
    twl_st_l_interm_assn_2\<^sup>d \<rightarrow> twl_st_l_interm_assn_2 *assn unat_lit_assn\<close>
    unfolding twl_st_l_interm_assn_2_def
    apply sepref_to_hoare
    by (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) x\<close>;
        case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) xi\<close>) sep_auto+
  have H: \<open>(return \<circ> (\<lambda>(M, N, U, D, NP, UP, Q, W). ((M, N, U, D, NP, UP, tl Q, W), hd Q)),
             select_and_remove_from_literals_to_update_wl)
            \<in> [comp_PRE twl_st_l_interm_rel_1
                 (\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> {#})
                 (\<lambda>_ (_, _, _, _, _, _, Q, _). Q \<noteq> [])
                 (\<lambda>_. True)]\<^sub>a
              hrp_comp (twl_st_l_interm_assn_2\<^sup>d) twl_st_l_interm_rel_1 \<rightarrow>
              hr_comp (twl_st_l_interm_assn_2 *assn unat_lit_assn) (twl_st_l_interm_rel_1 \<times>\<^sub>r Id)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF 2 1] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def twl_st_l_interm_rel_1_def in_br_conv list_mset_rel_def
        literals_to_update_wl_empty_def)

  have im: \<open>?im' = ?im\<close>
    unfolding twl_st_l_interm_assn_2_def twl_st_l_interm_rel_1_def prod_hrp_comp
    by (auto simp: prod_hrp_comp hrp_comp_def list_assn_list_mset_rel_eq_list_mset_assn
        twl_st_l_trail_assn_def hr_comp_invalid)

 have post: \<open>?f' = ?f\<close>
   by (auto simp: comp_PRE_def twl_st_l_interm_assn_2_def
       twl_st_l_trail_assn_def list_assn_list_mset_rel_eq_list_mset_assn
       twl_st_l_interm_rel_1_def)
  show ?thesis using H unfolding pre post im .
qed

concrete_definition (in -) hd_select_and_remove_from_literals_to_update_wl''
   uses twl_array_code.hd_select_and_remove_from_literals_to_update_wl''_refine
   is "(?f,_)\<in>_"

prepare_code_thms (in -) hd_select_and_remove_from_literals_to_update_wl''_def

lemmas [sepref_fr_rules] =
   hd_select_and_remove_from_literals_to_update_wl''.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def twl_st_l_trail_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D_code
   uses twl_array_code.unit_propagation_outer_loop_wl_D.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_code_def

lemmas unit_propagation_outer_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]

sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil)\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_def twl_st_l_trail_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses twl_array_code.get_conflict_wll_is_Nil_code.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def,
    FCOMP get_conflict_wll_is_Nil_get_conflict_wl_is_Nil]

lemma get_conflict_wll_is_Nil_hnr[unfolded twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, RETURN o get_conflict_wl_is_Nil) \<in>
     twl_st_l_trail_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). D) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). D) S'\<close>)
  by (sep_auto simp: twl_st_l_trail_assn_def get_conflict_wl_is_Nil_def get_conflict_wll_is_Nil_def
      Multiset.is_empty_def Nil_list_mset_rel_iff empty_list_mset_rel_iff
      get_conflict_wll_is_Nil_code_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil arl_assn_def hr_comp_def null_def)+

lemma hd_trail[sepref_fr_rules]:
  \<open>(return o hd o fst, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>k \<rightarrow> pair_nat_ann_lit_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x)
   apply auto
  apply (case_tac a)
   apply (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>hd _\<close>]
      mod_star_conv pure_app_eq)+
  done

sepref_thm is_decided_hd_trail_wll_code
  is \<open>is_decided_hd_trail_wll\<close>
  :: \<open>[\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a twl_st_l_trail_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wll_def twl_st_l_trail_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) is_decided_hd_trail_wll_code
   uses twl_array_code.is_decided_hd_trail_wll_code.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) is_decided_hd_trail_wll_code_def

lemmas is_decided_hd_trail_wll_code_refine[sepref_fr_rules] =
   is_decided_hd_trail_wll_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]

text \<open>Splitting in \<open>\<exists>\<^sub>A\<close> does not seem to work, leading to splitting by hand:\<close>
lemma
  trail_assn_Cons_Nil: \<open>trail_assn (a # list) ([], ah, ba) = false\<close> and
  trail_assn_Cons_Decided_Some: \<open>trail_assn (Decided x1 # list) ((aba, Some x2) # list', ah, ba) = false\<close> and
  trail_assn_Cons_Propagated_None:
    \<open>trail_assn (Propagated x21 x22 # list) ((aba, None) # list', ah, ba) = false\<close>
proof -
  have [simp]: \<open>(case b of (a, b, c) \<Rightarrow> P a b c) = P (fst b) (fst (snd b)) (snd (snd b))\<close> for P b
    by (cases b) auto
  have [simp]: \<open>(case b of (a, b) \<Rightarrow> P a b) = P (fst b) (snd b)\<close> for P b
    by (cases b) auto
  have [simp]: \<open>trail_conc b (a, ah, ba) = trail_conc (fst b, fst (snd b), snd (snd b)) (a, ah, ba)\<close>
    for f b a
    by (cases b) auto
  have [simp]: \<open>(fst b = [] \<and> fst b = a # list \<and> P) \<longleftrightarrow> False\<close> for b P
    by auto
  show \<open>trail_assn (a # list) ([], ah, ba) = false\<close>
    by (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>]
        simp del: prod.collapse)
  have H: \<open>(\<exists>\<^sub>A b. f (fst b) * P b * \<up>(fst b = a \<and> Q b)) = (\<exists>\<^sub>A b. f a * P b * \<up>(fst b = a \<and> Q b))\<close> for f P Q a
  proof -
    { fix pp
      have "fst pp = a \<longrightarrow> f (fst pp) * P pp * \<up> (fst pp = a \<and> Q pp) = f a * P pp * \<up> (fst pp = a \<and> Q pp)"
        by meson
      then have "f (fst pp) * P pp * \<up> (fst pp = a \<and> Q pp) = f a * P pp * \<up> (fst pp = a \<and> Q pp)"
        by force }
    then show ?thesis
      by auto
  qed
  have [simp]: \<open>pair_nat_ann_lit_assn (Decided x1) (aba, Some x2) = false\<close> and
    [simp]: \<open>pair_nat_ann_lit_assn (Propagated x21 x22) (aba, None) = false\<close>
    by (auto simp: nat_ann_lit_rel_def pure_def)

  show \<open>trail_assn (Decided x1 # list) ((aba, Some x2) # list', ah, ba) = false\<close>
    apply (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>]
        simp del: prod.collapse)
    apply (subst H)
    by (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>]
        simp del: prod.collapse)
  show \<open>trail_assn (Propagated x21 x22 # list) ((aba, None) # list', ah, ba) = false\<close>
    apply (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>]
        simp del: prod.collapse)
    apply (subst H)
    by (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>]
        simp del: prod.collapse)
qed

lemma is_decided_hd_trail_wll_hnr[unfolded twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(is_decided_hd_trail_wll_code, RETURN o is_decided_hd_trail_wl) \<in> [\<lambda>(M, _). M \<noteq> []]\<^sub>atwl_st_l_trail_assn\<^sup>k \<rightarrow> bool_assn\<close>
  apply sepref_to_hoare
  unfolding is_decided_hd_trail_wl_def is_decided_wl_code_def is_decided_hd_trail_wll_code_def
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). fst M) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). M) S'\<close>;
     case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). hd (fst M)) S\<close>;
     case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). hd M) S'\<close>)
  by (sep_auto simp: twl_st_l_trail_assn_def is_decided_hd_trail_wll_code_def is_decided_hd_trail_wl_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil hr_comp_def null_def trail_assn_Cons_Decided_Some
      pair_nat_ann_lit_assn_Decided_Some pair_nat_ann_lit_assn_Propagated_None trail_assn_Cons_Nil
      trail_assn_Cons_Propagated_None
      split: option.splits)+

definition get_level_trail :: \<open>trail_int \<Rightarrow> uint32 \<Rightarrow> nat\<close> where
  \<open>get_level_trail = (\<lambda>(M, xs, lvls, k) L. lvls! (nat_of_uint32 (L >> 1)))\<close>

text \<open>TODO MOve\<close>
lemma (in -)shiftr1[sepref_fr_rules]:
   \<open>(uncurry (return oo (op >> )), uncurry (RETURN oo (op >>))) \<in> uint32_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def uint32_nat_rel_def br_def)

lemma shiftl1[sepref_fr_rules]: \<open>(return o shiftl1, RETURN o shiftl1) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

lemma (in -)nat_of_uint32_rule[sepref_fr_rules]:
  \<open>(return o nat_of_uint32, RETURN o nat_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto)

sepref_thm get_level_code
  is \<open>uncurry (RETURN oo get_level_trail)\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), L). nat_of_uint32 L div 2 < length lvls]\<^sub>a
  trail_conc\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_trail_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_level_code
   uses twl_array_code.get_level_code.refine_raw
   is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) get_level_code_def

lemmas get_level_code_get_level_code[sepref_fr_rules] =
   get_level_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_l_trail_assn_def]

lemma get_level_code_get_level:
  \<open>(uncurry get_level_code, uncurry (RETURN oo get_level)) \<in>
   [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [simp]: \<open>(ba, bb) \<in> nat_lit_rel \<Longrightarrow> ba div 2 = atm_of bb\<close> for ba bb
    by (auto simp: p2rel_def lit_of_natP_def atm_of_lit_of_nat nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 1: \<open>(uncurry (RETURN oo get_level_trail), uncurry (RETURN oo get_level)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trail_ref \<times>\<^sub>f unat_lit_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI) (auto simp: image_image trail_ref_def get_level_trail_def
        nat_shiftr_div2 shiftr1_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
        nat_of_uint32_shiftr)

  have H: \<open>(uncurry get_level_code, uncurry (RETURN \<circ>\<circ> get_level))
\<in> [comp_PRE (trail_ref \<times>\<^sub>f unat_lit_rel) (\<lambda>(M, L). L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((M, xs, lvls, k), L). nat_of_uint32 L div 2 < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((pair_nat_ann_lits_assn *assn
                       array_assn (option_assn bool_assn) *assn
                       array_assn uint32_nat_assn *assn uint32_nat_assn)\<^sup>k *\<^sub>a
                      uint32_assn\<^sup>k)
                     (trail_ref \<times>\<^sub>f unat_lit_rel) \<rightarrow> hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF get_level_code.refine 1, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
        intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed

declare get_level_code_get_level[sepref_fr_rules]

lemma in_literals_are_in_N\<^sub>0_in_D\<^sub>0:
  assumes \<open>literals_are_in_N\<^sub>0 D\<close> and \<open>L \<in># D\<close>
  shows \<open>L \<in> snd ` D\<^sub>0\<close>
  using assms
  by (cases L) (auto simp: image_image literals_are_in_N\<^sub>0_def lits_of_atms_of_m_def)

definition (in -)
  \<open>zero_uint32 = (0 :: nat)\<close>

lemma (in -) uint32_nat_assn_zero_uint32:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012 zero_uint32_def)

lemma (in -) nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012)

lemma (in -)nat_of_uint32_le_iff:
  \<open>nat_of_uint32 ai \<le> nat_of_uint32 bi \<longleftrightarrow> ai \<le> bi\<close>
  by transfer (auto simp add: word_le_nat_alt)

lemma (in -)nat_of_uint32_less_iff:
  \<open>nat_of_uint32 ai < nat_of_uint32 bi \<longleftrightarrow> ai < bi\<close>
  by transfer(auto simp add: word_less_nat_alt)

lemma (in -)max_uint32[sepref_fr_rules]:
  \<open>(uncurry (return oo max), uncurry (RETURN oo max)) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def max_def
      nat_of_uint32_le_iff)

lemma (in -)uint32_nat_assn_less[sepref_fr_rules]:
  \<open>(uncurry (return oo op <), uncurry (RETURN oo op <)) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def max_def
      nat_of_uint32_less_iff)

sepref_thm maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo maximum_level_remove)\<close>
  :: \<open>[\<lambda>((M, D), L). literals_are_in_N\<^sub>0 (mset D)]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding maximum_level_remove_def[abs_def]
  supply in_literals_are_in_N\<^sub>0_in_D\<^sub>0[intro]
  supply uint32_nat_assn_zero_uint32[sepref_fr_rules]
  supply [[goals_limit = 1]]
  apply (rewrite in "(False, \<hole>)" zero_uint32_def[symmetric])
  apply (rewrite in "[\<hole>..<_]" annotate_assn[where A=nat_assn])
  by sepref

concrete_definition (in -) maximum_level_remove_code
   uses twl_array_code.maximum_level_remove_code.refine_raw
   is "(uncurry2 ?f,_)\<in>_"

prepare_code_thms maximum_level_remove_code_def

lemmas select_and_remove_from_literals_to_update_wl''_code_[sepref_fr_rules] =
   maximum_level_remove_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]

lemma maximum_level_remove_code_get_maximum_level_remove[sepref_fr_rules]:
  \<open>(uncurry2 (maximum_level_remove_code),
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    [\<lambda>((M, D), L). literals_are_in_N\<^sub>0 D]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have 1:
  \<open>(uncurry2 (RETURN ooo maximum_level_remove),
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    ((Id \<times>\<^sub>r list_mset_rel) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
    by (auto intro!: nres_relI frefI simp: list_mset_rel_def br_def maximum_level_remove
        get_maximum_level_remove_def)
  have H: \<open>(uncurry2 maximum_level_remove_code,
   uncurry2 (RETURN \<circ>\<circ>\<circ> get_maximum_level_remove))
  \<in> [comp_PRE (Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id) (\<lambda>_. True) (\<lambda>_ ((M, D), L). literals_are_in_N\<^sub>0 (mset D))
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k) (Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id) \<rightarrow>
        hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux [OF maximum_level_remove_code.refine 1, OF twl_array_code_axioms] .
  have 1: \<open>?pre' = ?pre\<close> -- \<open>TODO tune proof\<close>
    apply (auto simp: comp_PRE_def
        list_mset_rel_def br_def
        simp del: literal_of_nat.simps intro!: ext)
    by (metis mset_sorted_list_of_multiset)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

lemma count_decided_trail_ref:
  \<open>(RETURN o (\<lambda>(_, _, _, k). k), RETURN o count_decided) \<in> trail_ref \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: trail_ref_def)

lemma count_decided_trail:
   \<open>(return o (\<lambda>(_, _, _, k). k), RETURN o (\<lambda>(_, _, _, k). k)) \<in> trail_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  by sepref_to_hoare sep_auto

lemmas count_decided_trail_code[sepref_fr_rules] =
   count_decided_trail[FCOMP count_decided_trail_ref, unfolded trail_assn_def[symmetric]]

sepref_register skip_and_resolve_loop_wl_D
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>If _ \<hole> _\<close> op_mset_arl_empty_def[symmetric])
  unfolding twl_st_l_trail_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    get_conflict_wl.simps get_trail_wl.simps get_conflict_wl_get_conflict_wl_is_Nil
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    maximum_level_remove[symmetric]
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
  by sepref

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
   uses twl_array_code.skip_and_resolve_loop_wl_D.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_l_trail_assn_def]


sepref_thm find_lit_of_max_level_wl_imp_code
  is \<open>uncurry8 find_lit_of_max_level_wl_imp'\<close>
  :: \<open>[\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L). literals_are_in_N\<^sub>0 (mset D)]\<^sub>a
       (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a
          unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding find_lit_of_max_level_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_lit_of_max_level_wl_imp'_def
  supply in_literals_are_in_N\<^sub>0_in_D\<^sub>0[intro]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) find_lit_of_max_level_wl_imp_code
   uses twl_array_code.find_lit_of_max_level_wl_imp_code.refine_raw
   is "(uncurry8 ?f,_)\<in>_"

prepare_code_thms (in -) find_lit_of_max_level_wl_imp_code_def

lemmas find_lit_of_max_level_wl_imp_code[sepref_fr_rules] =
   find_lit_of_max_level_wl_imp_code.refine[of N\<^sub>0, OF twl_array_code_axioms]


lemma find_lit_of_max_level_wl_imp_code_find_lit_of_max_level_wl'[sepref_fr_rules]:
  \<open>(uncurry8 find_lit_of_max_level_wl_imp_code, uncurry8 find_lit_of_max_level_wl') \<in>
   [\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L). distinct_mset D \<and>
     (\<exists>K\<in>#remove1_mset (-L) D. get_level M K = get_maximum_level M (remove1_mset (- L) D)) \<and>
     literals_are_in_N\<^sub>0 D]\<^sub>a
   (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k
    \<rightarrow> unat_lit_assn\<close>
    (is \<open>_ \<in> [?P]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have \<open>K \<in># remove1_mset (-L) (mset D) \<Longrightarrow> distinct D \<Longrightarrow>
    get_level M K = get_maximum_level M (remove1_mset (- L) (mset D)) \<Longrightarrow>
    find_lit_of_max_level_wl_imp M D L
    \<le> find_lit_of_max_level_wl' M N U (mset D) NP UP Q W L\<close>
    for D' :: \<open>nat clause\<close> and K :: \<open>nat literal\<close> and M :: \<open>(nat, nat) ann_lits\<close> and L and
    D :: \<open>nat clause_l\<close> and N and U :: nat and NP UP and Q and W
    unfolding find_lit_of_max_level_wl_imp_def maximum_level_remove find_lit_of_max_level_wl'_def
        find_lit_of_max_level_wl_def
    apply (refine_vcg WHILEIT_rule[where R =\<open>measure (\<lambda>i. Suc (length D) - i)\<close>])
    subgoal by auto
    subgoal by (auto simp: list_mset_rel_def br_def)
    subgoal by auto
    subgoal apply (auto simp add: list_mset_rel_def br_def in_set_conv_nth distinct_mset_remove1_All
          dest!: in_diffD)
      by (metis Suc_lessI less_SucE)+
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def less_Suc_eq)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def distinct_mset_remove1_All
intro!: in_remove1_msetI)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def distinct_mset_remove1_All)
    done
  then have 1: \<open>(uncurry8 find_lit_of_max_level_wl_imp',
    uncurry8 find_lit_of_max_level_wl') \<in>
     [?P]\<^sub>f
     Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    unfolding find_lit_of_max_level_wl_imp'_def
    by (intro frefI nres_relI) (auto simp add: uncurry_def list_mset_rel_def br_def)
  have H: \<open>(uncurry8 find_lit_of_max_level_wl_imp_code, uncurry8 find_lit_of_max_level_wl')
    \<in> [comp_PRE
       (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id)
       (\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L).
           distinct_mset D \<and>
           (\<exists>K\<in>#remove1_mset (- L) D.
               get_level M K = get_maximum_level M (remove1_mset (- L) D)) \<and>
           literals_are_in_N\<^sub>0 D)
       (\<lambda>_ ((((((((M, N), U), D), NP), UP), WS), Q), L).
           literals_are_in_N\<^sub>0 (mset D))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
                        (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a
                        clauses_l_assn\<^sup>k *\<^sub>a
                        clauses_l_assn\<^sup>k *\<^sub>a
                        clause_l_assn\<^sup>k *\<^sub>a
                        (hr_comp (arrayO_assn (arl_assn nat_assn))
                          (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k *\<^sub>a
                        unat_lit_assn\<^sup>k)
                       (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f
                        Id \<times>\<^sub>f
                        Id \<times>\<^sub>f
                        Id) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux [OF find_lit_of_max_level_wl_imp_code.refine 1, OF twl_array_code_axioms] .
  have 1: \<open>?pre' = ?P\<close>
    by (auto simp: comp_PRE_def list_mset_rel_def br_def simp del: literal_of_nat.simps intro!: ext)
  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry2 (find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, D), L). M \<noteq> [] \<and> literals_are_in_N\<^sub>0 D]\<^sub>a
         trail_assn\<^sup>d *\<^sub>a conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k
    \<rightarrow> trail_assn\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
  supply [[goals_limit=1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses twl_array_code.find_decomp_wl_imp_code.refine_raw
   is "(uncurry2 ?f,_)\<in>_"

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry8 (PR_CONST find_decomp_wl_imp')\<close>
  :: \<open>[\<lambda>((((((((M::(nat, nat) ann_lits, N), U::nat), D::nat clause), NP::nat clauses), UP:: nat clauses),
        Q), W), L). D \<noteq> {#} \<and> M \<noteq> [] \<and> literals_are_in_N\<^sub>0 D]\<^sub>a
      (trail_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
         unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
      unat_lit_assn\<^sup>k \<rightarrow> trail_assn\<close>
  unfolding find_decomp_wl_imp'_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses twl_array_code.find_decomp_wl_imp'_code.refine_raw
   is "(uncurry8 ?f,_)\<in>_"

prepare_code_thms (in -) find_decomp_wl_imp'_code_def
thm find_decomp_wl_imp'_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
    unfolded twl_st_l_trail_assn_def]


lemma find_decomp_wl_code[sepref_fr_rules]:
  \<open>(uncurry8 find_decomp_wl_imp'_code,
      uncurry8 find_decomp_wl')
  \<in> [\<lambda>((((((((M::(nat, nat) ann_lits, N), U::nat), D::nat clause), NP::nat clauses), UP:: nat clauses),
        Q), W), L). \<exists>D\<^sub>0. D \<noteq> {#} \<and> M \<noteq> [] \<and> ex_decomp_of_max_lvl M (Some D) L \<and> L = lit_of (hd M) \<and>
       (twl_struct_invs (twl_st_of_wl None (M, N, U, D\<^sub>0, NP, UP, Q, W)) \<and>
       literals_are_in_N\<^sub>0 D \<and> D \<subseteq># the D\<^sub>0 \<and> D\<^sub>0 \<noteq> None)]\<^sub>a
    (trail_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k
    \<rightarrow> trail_assn\<close>
  (is \<open> _ \<in> [?P]\<^sub>a _ \<rightarrow> _\<close>)
proof -
  have H: \<open>(uncurry8 find_decomp_wl_imp'_code, uncurry8 find_decomp_wl')
    \<in> [\<lambda>((((((((a, b), ba), bb), bc), bd), be), bf), bg).
        bb \<noteq> {#} \<and>
        a \<noteq> []\<and>
        ex_decomp_of_max_lvl a (Some bb) bg \<and>
        bg = lit_of (hd a) \<and>
        (\<exists>D\<^sub>0. twl_struct_invs
                (convert_lits_l b a,
                 {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
                 . x \<in># mset (take ba (tl b))#},
                 {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
                 . x \<in># mset (drop (Suc ba) b)#},
                 D\<^sub>0, bc, bd, {#}, be) \<and>
               bb \<subseteq># the D\<^sub>0 \<and> (\<exists>y. D\<^sub>0 = Some y)) \<and>
        literals_are_in_N\<^sub>0
         bb]\<^sub>a
     (trail_assn)\<^sup>d *\<^sub>a (arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
        clauses_l_assn\<^sup>k *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a
     (hr_comp (arrayO_assn (arl_assn nat_assn))
         (\<langle>Id\<rangle>map_fun_rel ((\<lambda>L. (nat_of_lit L, L)) ` set_mset N\<^sub>1)))\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
     trail_assn\<close>
    (is \<open> _ \<in> [?Q]\<^sub>a _ \<rightarrow> _\<close>)
    using find_decomp_wl_imp'_code.refine[unfolded find_decomp_wl_imp'_def PR_CONST_def, FCOMP
        find_decomp_wl_imp_find_decomp_wl'[unfolded find_decomp_wl_imp'_def], OF twl_array_code_axioms]
      .

  have QP: \<open>?Q = ?P\<close>
    by (auto intro!: ext)
  show ?thesis
    using H unfolding QP .
qed

definition (in -) extract_shorter_conflict_l_trivial :: \<open>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow> 'v clause nres\<close> where
\<open>extract_shorter_conflict_l_trivial M N U D NP UP W Q == RETURN (the D)\<close>

abbreviation (in -) uncurry_swap3 where
\<open>uncurry_swap3 f \<equiv> \<lambda> ((a, b), c). f (a, b, c)\<close>

abbreviation (in -) uncurried_swap8 where
\<open>uncurried_swap8 f \<equiv> \<lambda> (((((((M, N), U), D), NP), UP), Q), W). f (M, N, U, D, NP, UP, Q, W)\<close>

thm twl_st_l_trail_assn_def
sepref_register (in -) extract_shorter_conflict_l_trivial
sepref_thm extract_shorter_conflict_l_trivial'
  is \<open>uncurry7 extract_shorter_conflict_l_trivial\<close>
  :: \<open>[\<lambda>S. uncurried_swap8 get_conflict_wl S ~= None]\<^sub>a
   trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
        *\<^sub>a conflict_option_assn\<^sup>d *\<^sub>a unit_lits_assn\<^sup>k
        *\<^sub>a unit_lits_assn\<^sup>k
        *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k \<rightarrow> conflict_assn\<close>
  unfolding extract_shorter_conflict_l_trivial_def PR_CONST_def twl_st_l_trail_assn_def
  by sepref

(*TODO Move*)
lemma (in -) fr_refl': \<open>A \<Longrightarrow>\<^sub>A B \<Longrightarrow> C * A \<Longrightarrow>\<^sub>A C * B\<close>
  unfolding assn_times_comm[of C]
  by (rule Automation.fr_refl)

abbreviation (in -) "curry8' fc \<equiv> (\<lambda> (a, b, c, d, e, f, g, h). fc a b c d e f g)"

abbreviation (in -) comp5 (infixl "ooooo" 55) where "f ooooo g \<equiv> \<lambda>x. f oooo (g x)"
abbreviation (in -) comp6 (infixl "oooooo" 55) where "f oooooo g \<equiv> \<lambda>x. f oooo (g x)"
abbreviation (in -) comp7 (infixl "ooooooo" 55) where "f ooooooo g \<equiv> \<lambda>x. f oooo (g x)"
abbreviation (in -) comp8 (infixl "oooooooo" 55) where "f oooooooo g \<equiv> \<lambda>x. f oooo (g x)"

notation (in -)
  comp5 (infixl "\<circ>\<circ>\<circ>\<circ>" 55) and
  comp6 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
  comp7 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>" 55) and
  comp8 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>\<circ>" 55)
(*End Move*)

thm extract_shorter_conflict_l_trivial'.refine_raw[]

concrete_definition (in -) extract_shorter_conflict_l_trivial_code
   uses twl_array_code.extract_shorter_conflict_l_trivial'.refine_raw
   is "(uncurry7 ?f,_)\<in>_"

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_def

lemmas extract_shorter_conflict_l_trivial_code_wl_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code.refine[of N\<^sub>0, unfolded PR_CONST_def,
      OF twl_array_code_axioms]

definition (in -) extract_shorter_conflict_wl' where
\<open>extract_shorter_conflict_wl' M N U D NP UP W Q =
  extract_shorter_conflict_wl (M, N, U, D, NP, UP, W, Q)\<close>

lemma extract_shorter_conflict_l_trivial_code_wl':
  \<open>(uncurry7 extract_shorter_conflict_l_trivial_code, uncurry7 extract_shorter_conflict_wl')
    \<in> [\<lambda>(((((((M, N), U), D), NP), UP), Q), W).
         twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
          get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None \<and>
          - lit_of (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)))
            \<in># the (get_conflict_wl (M, N, U, D, NP, UP, Q, W))]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
      *\<^sub>a conflict_option_assn\<^sup>d *\<^sub>a unit_lits_assn\<^sup>k
      *\<^sub>a unit_lits_assn\<^sup>k
      *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k \<rightarrow>
      conflict_assn\<close>
    (is \<open> _ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?post\<close>)
proof -
   have H: \<open>uncurry7 extract_shorter_conflict_l_trivial x <= \<Down> Id
       (uncurry7 extract_shorter_conflict_wl' y)\<close>
    if
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))\<close>
      \<open>-lit_of (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))) \<in># the (get_conflict_wl (M, N, U, D, NP, UP, Q, W))\<close>
      \<open>get_conflict_wl (M, N, U, D, NP, UP, Q, W) ~= None\<close> and
      \<open>x = (((((((M, N), U), D), NP), UP), Q), W)\<close> and
      \<open>y = (((((((M, N), U), D), NP), UP), Q), W)\<close>
  for N NP UP D L M U Q W x y
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause
        (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
      then have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) \<Turnstile>p the D\<close>
      using that(2-)
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    moreover have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) =
          mset ` set (tl N) \<union> set_mset NP \<union> set_mset UP\<close>
          apply (subst (2) append_take_drop_id[of U \<open>tl N\<close>, symmetric])
          unfolding set_append drop_Suc
          by auto
    ultimately show ?thesis
      using that(2-)
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
        extract_shorter_conflict_l_trivial_def extract_shorter_conflict_wl_def
        extract_shorter_conflict_wl'_def)
  qed

  have R: \<open>(uncurry7 extract_shorter_conflict_l_trivial, uncurry7 extract_shorter_conflict_wl') \<in>
     [uncurried_swap8 (\<lambda>S::'v twl_st_wl. twl_struct_invs (twl_st_of_wl None S) \<and>
        get_conflict_wl S ~= None \<and> -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S))]\<^sub>f
      (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    apply (intro nres_relI frefI)
    apply clarify
    apply (rule H)
    apply assumption+
    apply auto
    done

  have H: \<open>(uncurry7 extract_shorter_conflict_l_trivial_code, uncurry7 extract_shorter_conflict_wl')
    \<in> [comp_PRE (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id)
    (\<lambda>(((((((M, N), U), D), NP), UP), Q), W).
        twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
        get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None \<and>
        - lit_of (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)))
        \<in># the (get_conflict_wl (M, N, U, D, NP, UP, Q, W)))
    (\<lambda>_ S. uncurried_swap8 get_conflict_wl S \<noteq> None)
    (\<lambda>_. True)]\<^sub>a hrp_comp
                   (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
                    conflict_option_assn\<^sup>d *\<^sub>a
                    clauses_l_assn\<^sup>k *\<^sub>a
                    clauses_l_assn\<^sup>k *\<^sub>a
                    clause_l_assn\<^sup>k *\<^sub>a
                    (hr_comp (arrayO_assn (arl_assn nat_assn))
                      (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k)
                   (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f
                    Id) \<rightarrow> hr_comp conflict_assn Id\<close>
      (is \<open> _ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?post'\<close>)
      using hfref_compI_PRE_aux[OF extract_shorter_conflict_l_trivial_code.refine R,
      OF twl_array_code_axioms] .
  have cond: \<open>?cond' = ?cond\<close>
    unfolding comp_PRE_def by auto
  have pre: \<open>?pre' = ?pre\<close>
    unfolding prod_hrp_comp twl_st_l_trail_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have im: \<open>?post' = ?post\<close>
    by (auto simp: hrp_comp_def hr_comp_def)
   show ?thesis
     using H unfolding cond pre im .
qed

concrete_definition (in -) extract_shorter_conflict_l_trivial_code_wl'
   uses twl_array_code.extract_shorter_conflict_l_trivial_code_wl'
   is "(uncurry7 ?f,_)\<in>_"

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_wl'_def

lemmas extract_shorter_conflict_l_trivial_code_wl'_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code_wl'.refine[of N\<^sub>0, unfolded PR_CONST_def,
      OF twl_array_code_axioms]

(*TODO Move*)
lemma (in -) hn_ctxt_prod_assn_prod:
  \<open>hn_ctxt (R *assn S) (a, b) (a', b') = hn_ctxt R a a' * hn_ctxt S b b'\<close>
  unfolding hn_ctxt_def
  by auto
(*END Move*)

sepref_register backtrack_wl_D
sepref_thm backtrack_wl_D
  is \<open>PR_CONST backtrack_wl_D\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  unfolding backtrack_wl_D_def PR_CONST_def
  unfolding twl_st_l_trail_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] (* lms_fold_custom_empty *)
    extract_shorter_conflict_wl'_def[symmetric]
    cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  apply (rewrite at \<open>(_, add_mset (add_mset _ \<hole>) _, _)\<close> lms_fold_custom_empty)
  unfolding no_skip_def[symmetric] no_resolve_def[symmetric]
    find_decomp_wl'_find_decomp_wl[symmetric] option.sel add_mset_list.simps
  supply [[goals_limit=1]]
  by sepref


concrete_definition (in -) backtrack_wl_D_code
   uses twl_array_code.backtrack_wl_D.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) backtrack_wl_D_code_def

lemmas backtrack_wl_D_code_refine[sepref_fr_rules] =
   backtrack_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_l_trail_assn_def]

lemma N\<^sub>0'_eq_append_in_D\<^sub>0: \<open>N\<^sub>0' = ys @ a2'g \<Longrightarrow>a2'g \<noteq> [] \<Longrightarrow> hd a2'g \<in> snd ` D\<^sub>0\<close>
  by (auto simp: image_image N\<^sub>1_def N\<^sub>0''_def)

sepref_thm find_unassigned_lit_wl_D_code
  is \<open>PR_CONST find_unassigned_lit_wl_D\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>k \<rightarrow>\<^sub>a option_assn unat_lit_assn\<close>
  unfolding find_unassigned_lit_wl_D_def PR_CONST_def twl_st_l_trail_assn_def
    is_None_def[symmetric]
  supply [[goals_limit = 1]]
  supply N\<^sub>0'_eq_append_in_D\<^sub>0[intro]
  by sepref

concrete_definition (in -) find_unassigned_lit_wl_D_code
  uses twl_array_code.find_unassigned_lit_wl_D_code.refine_raw
  is "(?f,_)\<in>_"

prepare_code_thms (in -) find_unassigned_lit_wl_D_code_def

lemmas find_unassigned_lit_wl_D_code[sepref_fr_rules] =
   find_unassigned_lit_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_l_trail_assn_def]

lemma find_unassigned_lit_wl_D_code_find_unassigned_lit_wl[unfolded twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(find_unassigned_lit_wl_D_code N\<^sub>0, find_unassigned_lit_wl)
  \<in> [\<lambda>S. literals_are_N\<^sub>0 S \<and> twl_struct_invs (twl_st_of_wl None S) \<and> get_conflict_wl S = None]\<^sub>a
     twl_st_l_trail_assn\<^sup>k \<rightarrow> option_assn unat_lit_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(find_unassigned_lit_wl_D_code N\<^sub>0, find_unassigned_lit_wl)
  \<in> [comp_PRE (Id \<times>\<^sub>f (Id \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id)))))))
      (\<lambda>S. literals_are_N\<^sub>0 S \<and> twl_struct_invs (twl_st_of_wl None S) \<and> get_conflict_wl S = None)
       (\<lambda>_ _. True)
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (twl_st_l_trail_assn\<^sup>k) (Id \<times>\<^sub>f (Id \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id))))))) \<rightarrow>
     hr_comp (option_assn unat_lit_assn) (\<langle>Id\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_unassigned_lit_wl_D_code.refine[unfolded PR_CONST_def]
       find_unassigned_lit_wl_D_find_unassigned_lit_wl, OF twl_array_code_axioms]
    unfolding op_watched_app_def .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (auto simp: comp_PRE_def simp: prod_rel_def_internal
        relAPP_def map_fun_rel_def[abs_def] p2rel_def lit_of_natP_def
        literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp
    by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

sepref_register decide_wl_or_skip_D
sepref_thm decide_wl_or_skip_D_code
  is \<open>PR_CONST decide_wl_or_skip_D\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_l_trail_assn\<close>
  unfolding decide_wl_or_skip_D_def PR_CONST_def twl_st_l_trail_assn_def
    cons_trail_Decided.simps[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) decide_wl_or_skip_D_code
   uses twl_array_code.decide_wl_or_skip_D_code.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) decide_wl_or_skip_D_code_def

lemmas decide_wl_or_skip_D_code_def_refine[sepref_fr_rules] =
   decide_wl_or_skip_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_l_trail_assn_def]


subsubsection \<open>Combining Together: the Other Rules\<close>
term get_conflict_wl_is_None
sepref_register get_conflict_wl_is_None
sepref_thm (in twl_array_code_ops) get_conflict_wl_is_None_code
  is \<open>RETURN o get_conflict_wl_is_None\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_def twl_st_l_trail_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_code
   uses twl_array_code_ops.get_conflict_wl_is_None_code.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) get_conflict_wl_is_None_code_def

lemmas (in twl_array_code_ops)get_conflict_wl_is_None_code_refine[sepref_fr_rules] =
   get_conflict_wl_is_None_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]


sepref_register cdcl_twl_o_prog_wl_D
sepref_thm cdcl_twl_o_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_l_trail_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_def PR_CONST_def twl_st_l_trail_assn_def
  unfolding get_conflict_wl_is_None get_conflict_wl_get_conflict_wl_is_Nil
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_code
   uses twl_array_code.cdcl_twl_o_prog_wl_D_code.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_code_def

lemmas cdcl_twl_o_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_l_trail_assn_def]


subsubsection \<open>Combining Together: Full Strategy\<close>

sepref_register cdcl_twl_stgy_prog_wl_D
sepref_thm cdcl_twl_stgy_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_wl_D\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_def PR_CONST_def twl_st_l_trail_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_stgy_prog_wl_D_code
   uses twl_array_code.cdcl_twl_stgy_prog_wl_D_code.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) cdcl_twl_stgy_prog_wl_D_code_def

lemmas cdcl_twl_stgy_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_stgy_prog_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]

concrete_definition (in -) select_and_remove_from_literals_to_update_wl''_code
   uses twl_array_code.hd_select_and_remove_from_literals_to_update_wl''_refine
   is "(?f,_)\<in>_"

prepare_code_thms select_and_remove_from_literals_to_update_wl''_code_def

lemmas select_and_remove_from_literals_to_update_wl''_code_2[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl''_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]

end

export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.ML"

end