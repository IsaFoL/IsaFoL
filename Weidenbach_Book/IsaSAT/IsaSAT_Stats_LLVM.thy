theory IsaSAT_Stats_LLVM
imports IsaSAT_Stats IsaSAT_EMA_LLVM IsaSAT_Rephase_LLVM IsaSAT_Reluctant_LLVM Tuple16_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
hide_const (open) NEMonad.RETURN NEMonad.ASSERT


lemma Exists_eq_simp_sym: \<open>(\<exists>x. (P x \<and>* \<up> (b = x)) s) \<longleftrightarrow> P b s\<close>
  by (subst eq_commute[of b])
     (rule Exists_eq_simp)

definition code_hider_assn where
  \<open>code_hider_assn R S = hr_comp R (\<langle>S\<rangle>code_hider_rel)\<close>


lemma get_content_destroyed_kept[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow> (Mreturn o id, RETURN o get_content) \<in>  (code_hider_assn R S)\<^sup>k \<rightarrow>\<^sub>a hr_comp R S\<close>
  unfolding code_hider_assn_def code_hider_rel_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: br_def ENTAILS_def Exists_eq_simp Exists_eq_simp_sym hr_comp_def pure_true_conv)
  by (smt (z3) Sep_Algebra_Add.pure_part_pure entails_def is_pure_conv pure_app_eq pure_partI sep.mult_assoc sep_conj_def split_conj_is_pure)

lemma Constructor_assn_destroyed:
  \<open>(Mreturn o id, RETURN o Constructor) \<in> (hr_comp R S)\<^sup>d \<rightarrow>\<^sub>a code_hider_assn R S\<close>
  unfolding code_hider_assn_def code_hider_rel_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: br_def ENTAILS_def Exists_eq_simp Exists_eq_simp_sym hr_comp_def pure_true_conv)

lemma get_content_destroyed:
  \<open>(Mreturn o id, RETURN o get_content) \<in>  (code_hider_assn R S)\<^sup>d \<rightarrow>\<^sub>a hr_comp R S\<close>
  unfolding code_hider_assn_def code_hider_rel_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: br_def ENTAILS_def Exists_eq_simp Exists_eq_simp_sym hr_comp_def pure_true_conv)

lemma get_content_hnr[sepref_fr_rules]:
  \<open>(id, get_content) \<in>  \<langle>S\<rangle>code_hider_rel \<rightarrow>\<^sub>f S\<close>
  unfolding code_hider_rel_def
  by (auto simp: intro!: frefI)


lemma Constructor_hnr[sepref_fr_rules]:
  \<open>(id, Constructor) \<in>  S \<rightarrow>\<^sub>f \<langle>S\<rangle>code_hider_rel\<close>
  unfolding code_hider_rel_def
  by (auto simp: intro!: frefI)

definition search_stats_assn :: \<open>search_stats \<Rightarrow> search_stats \<Rightarrow> _\<close> where
  \<open>search_stats_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>aword64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>aword64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

definition subsumption_stats_assn :: \<open>inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats \<Rightarrow> _\<close> where
  \<open>subsumption_stats_assn = word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

definition binary_stats_assn :: \<open>inprocessing_binary_stats \<Rightarrow> inprocessing_binary_stats \<Rightarrow> _\<close> where
  \<open>binary_stats_assn = word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

definition pure_lits_stats_assn :: \<open>inprocessing_pure_lits_stats \<Rightarrow> inprocessing_pure_lits_stats \<Rightarrow> _\<close> where
  \<open>pure_lits_stats_assn = word64_assn \<times>\<^sub>a word64_assn\<close>

definition empty_search_stats where
  \<open>empty_search_stats = (0,0,0,0,0,0,0,0,0,0)\<close>

sepref_def empty_search_stats_impl
  is \<open>uncurry0 (RETURN empty_search_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def empty_search_stats_def
  by sepref


definition empty_binary_stats :: \<open>inprocessing_binary_stats\<close> where
  \<open>empty_binary_stats = (0,0,0)\<close>

sepref_def empty_binary_stats_impl
  is \<open>uncurry0 (RETURN empty_binary_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a binary_stats_assn\<close>
  unfolding binary_stats_assn_def empty_binary_stats_def
  by sepref

definition empty_subsumption_stats :: \<open>inprocessing_subsumption_stats\<close> where
  \<open>empty_subsumption_stats = (0,0,0,0,0)\<close>

sepref_def empty_subsumption_stats_impl
  is \<open>uncurry0 (RETURN empty_subsumption_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a subsumption_stats_assn\<close>
  unfolding subsumption_stats_assn_def empty_subsumption_stats_def
  by sepref

definition empty_pure_lits_stats :: \<open>inprocessing_pure_lits_stats\<close> where
  \<open>empty_pure_lits_stats = (0,0)\<close>

sepref_def empty_pure_lits_stats_impl
  is \<open>uncurry0 (RETURN empty_pure_lits_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a pure_lits_stats_assn\<close>
  unfolding pure_lits_stats_assn_def empty_pure_lits_stats_def
  by sepref

definition lbd_size_limit_assn where
  \<open>lbd_size_limit_assn = uint32_nat_assn \<times>\<^sub>a sint64_nat_assn\<close>

definition empty_lsize_limit_stats :: \<open>lbd_size_limit_stats\<close> where
  \<open>empty_lsize_limit_stats = (0,0)\<close>

sepref_def empty_lsize_limit_stats_impl
  is \<open>uncurry0 (RETURN empty_lsize_limit_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_size_limit_assn\<close>
  unfolding lbd_size_limit_assn_def empty_lsize_limit_stats_def
  apply (rewrite at \<open>(_, \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(\<hole>, _)\<close> unat_const_fold[where 'a=32])
  by sepref

definition ema_init_bottom :: \<open>ema\<close> where
  \<open>ema_init_bottom = ema_init 0\<close>

sepref_def ema_init_bottom_impl
  is \<open>uncurry0 (RETURN ema_init_bottom)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_init_bottom_def by sepref

lemma stats_bottom:
  \<open>(uncurry0 (return\<^sub>M 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  \<open>(uncurry0 (return\<^sub>M 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a word32_assn\<close>
  by (sepref_to_hoare; vcg; fail)+

schematic_goal mk_free_search_stats_assn[sepref_frame_free_rules]: \<open>MK_FREE search_stats_assn ?fr\<close> and
  mk_free_binary_stats_assn[sepref_frame_free_rules]: \<open>MK_FREE binary_stats_assn ?fr2\<close> and
  mk_free_subsumption_stats_assn[sepref_frame_free_rules]: \<open>MK_FREE subsumption_stats_assn ?fr3\<close> and
  mk_free_ema_assn[sepref_frame_free_rules]: \<open>MK_FREE ema_assn ?fr4\<close>and
  mk_free_pure_lits_stats_assn[sepref_frame_free_rules]: \<open>MK_FREE pure_lits_stats_assn ?fr5\<close>
  unfolding search_stats_assn_def binary_stats_assn_def subsumption_stats_assn_def
    pure_lits_stats_assn_def
  by synthesize_free+

sepref_def free_search_stats_assn
  is \<open>mop_free\<close>
  :: \<open>search_stats_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def free_binary_stats_assn
  is \<open>mop_free\<close>
  :: \<open>binary_stats_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def free_subsumption_stats_assn
  is \<open>mop_free\<close>
  :: \<open>subsumption_stats_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def free_pure_lits_stats_assn
  is \<open>mop_free\<close>
  :: \<open>pure_lits_stats_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def free_ema_assn
  is \<open>mop_free\<close>
  :: \<open>ema_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def free_word64_assn
  is \<open>mop_free\<close>
  :: \<open>word64_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def free_word32_assn
  is \<open>mop_free\<close>
  :: \<open>word32_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref


sepref_def free_lbd_size_limit_assn
  is \<open>mop_free\<close>
  :: \<open>lbd_size_limit_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding lbd_size_limit_assn_def
  by sepref

lemma mop_free_hnr': \<open>(f, mop_free) \<in> R\<^sup>d \<rightarrow>\<^sub>a unit_assn \<Longrightarrow> MK_FREE R f\<close>
  unfolding mop_free_def
  apply (rule MK_FREEI)
  apply simp
  subgoal for a c
    apply (drule hfrefD[of _ _ _ _ _ _ _ a c])
    apply (rule TrueI)
    apply (rule TrueI)
    apply (drule hn_refineD)
    apply simp
    apply (rule htriple_pure_preI[of ])
    unfolding fst_conv snd_conv hf_pres.simps
    apply (clarsimp 
      simp: hn_ctxt_def pure_def sep_algebra_simps invalid_assn_def)
    done
  done


type_synonym isasat_stats_assn = \<open>(search_stats, inprocessing_binary_stats, inprocessing_subsumption_stats, ema,
  inprocessing_pure_lits_stats, 32 word \<times> 64 word, 64 word, 64 word,
  64 word, 64 word,64 word, 64 word,
  64 word, 64 word, 32 word, 64 word) tuple16\<close>

definition isasat_stats_assn :: \<open>isasat_stats \<Rightarrow> isasat_stats_assn \<Rightarrow> _ \<Rightarrow> bool\<close> where
  \<open>isasat_stats_assn = tuple16_assn search_stats_assn binary_stats_assn subsumption_stats_assn ema_assn
 pure_lits_stats_assn lbd_size_limit_assn word64_assn word64_assn word64_assn word64_assn
 word64_assn word64_assn word64_assn word64_assn word32_assn word64_assn\<close>

definition extract_search_strategy_stats :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>extract_search_strategy_stats = tuple16_ops.remove_a empty_search_stats\<close>

definition extract_binary_stats :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>extract_binary_stats = tuple16_ops.remove_b empty_binary_stats\<close>

definition extract_subsumption_stats :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>extract_subsumption_stats = tuple16_ops.remove_c empty_subsumption_stats\<close>

definition extract_avg_lbd :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>extract_avg_lbd = tuple16_ops.remove_d ema_init_bottom\<close>

definition extract_pure_lits_stats :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>extract_pure_lits_stats = tuple16_ops.remove_e empty_pure_lits_stats\<close>

definition extract_lbd_size_limit_stats :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>extract_lbd_size_limit_stats = tuple16_ops.remove_f empty_lsize_limit_stats\<close>

global_interpretation tuple16 where
  a_assn = search_stats_assn and
  b_assn = binary_stats_assn and
  c_assn = subsumption_stats_assn and
  d_assn = ema_assn and
  e_assn = pure_lits_stats_assn and
  f_assn = lbd_size_limit_assn and
  g_assn = word64_assn and
  h_assn = word64_assn and
  i_assn = word64_assn and
  j_assn = word64_assn and
  k_assn = word64_assn and
  l_assn = word64_assn and
  m_assn = word64_assn and
  n_assn = word64_assn and
  o_assn = word32_assn and
  p_assn = word64_assn and
  a_default = empty_search_stats and
  a = empty_search_stats_impl and
  b_default = empty_binary_stats and
  b = empty_binary_stats_impl and
  c_default = empty_subsumption_stats and
  c = empty_subsumption_stats_impl and
  d_default = ema_init_bottom and
  d = ema_init_bottom_impl and
  e_default = empty_pure_lits_stats and
  e = empty_pure_lits_stats_impl and
  f_default = \<open>empty_lsize_limit_stats\<close> and
  f = \<open>empty_lsize_limit_stats_impl\<close> and
  g_default = \<open>0\<close> and
  g = \<open>Mreturn 0\<close> and
  h_default = \<open>0\<close> and
  h = \<open>Mreturn 0\<close> and
  i_default = \<open>0\<close> and
  i = \<open>Mreturn 0\<close> and
  j_default = \<open>0\<close> and
  j = \<open>Mreturn 0\<close> and
  k_default = \<open>0\<close> and
  k = \<open>Mreturn 0\<close> and
  l_default = \<open>0\<close> and
  l = \<open>Mreturn 0\<close> and
  m_default = \<open>0\<close> and
  m = \<open>Mreturn 0\<close> and
  n_default = \<open>0\<close> and
  n = \<open>Mreturn 0\<close> and
  ko_default = \<open>0\<close> and
  ko = \<open>Mreturn 0\<close> and
  p_default = \<open>0\<close> and
  p = \<open>Mreturn 0\<close> and
  a_free = free_search_stats_assn and
  b_free = free_binary_stats_assn and
  c_free = free_subsumption_stats_assn and
  d_free = free_ema_assn and
  e_free = free_pure_lits_stats_assn and
  f_free = free_lbd_size_limit_assn and
  g_free = free_word64_assn and
  h_free = free_word64_assn and
  i_free = free_word64_assn and
  j_free = free_word64_assn and
  k_free = free_word64_assn and
  l_free = free_word64_assn and
  m_free = free_word64_assn and
  n_free = free_word64_assn and
  o_free = free_word32_assn and
  p_free = free_word64_assn
  rewrites \<open>isasat_assn = isasat_stats_assn\<close> and
    \<open>remove_a = extract_search_strategy_stats\<close> and
    \<open>remove_b = extract_binary_stats\<close> and
    \<open>remove_c = extract_subsumption_stats\<close> and
    \<open>remove_d = extract_avg_lbd\<close> and
    \<open>remove_e = extract_pure_lits_stats\<close> and
    \<open>remove_f = extract_lbd_size_limit_stats\<close>
  apply unfold_locales
  apply (rule empty_search_stats_impl.refine empty_binary_stats_impl.refine
    empty_subsumption_stats_impl.refine ema_init_bottom_impl.refine empty_pure_lits_stats_impl.refine
    stats_bottom  free_search_stats_assn.refine[THEN mop_free_hnr']
    free_binary_stats_assn.refine[THEN mop_free_hnr']
    free_subsumption_stats_assn.refine[THEN mop_free_hnr']
    free_ema_assn.refine[THEN mop_free_hnr']
    free_pure_lits_stats_assn.refine[THEN mop_free_hnr']
    empty_lsize_limit_stats_impl.refine
    free_pure_lits_stats_assn.refine[THEN mop_free_hnr', unfolded lbd_size_limit_assn_def[symmetric] pure_lits_stats_assn_def]
    free_word64_assn.refine[THEN mop_free_hnr']
    free_word32_assn.refine[THEN mop_free_hnr']
    free_lbd_size_limit_assn.refine[THEN mop_free_hnr']
    )+
  subgoal unfolding isasat_stats_assn_def tuple16_ops.isasat_assn_def ..
  subgoal unfolding extract_search_strategy_stats_def ..
  subgoal unfolding extract_binary_stats_def ..
  subgoal unfolding extract_subsumption_stats_def ..
  subgoal unfolding extract_avg_lbd_def ..
  subgoal unfolding extract_pure_lits_stats_def ..
  subgoal unfolding extract_lbd_size_limit_stats_def ..
  done

sepref_register
  remove_a remove_b remove_c remove_d
  remove_e remove_f remove_g remove_h
  remove_i remove_j remove_k remove_l
  remove_m remove_n remove_o remove_p


fun tuple16_rel :: \<open>
  ('a \<times> _ ) set \<Rightarrow>
  ('b \<times> _ ) set \<Rightarrow>
  ('c \<times> _ ) set \<Rightarrow>
  ('d \<times> _ ) set \<Rightarrow>
  ('e \<times> _ ) set \<Rightarrow>
  ('f \<times> _ ) set \<Rightarrow>
  ('g \<times> _ ) set \<Rightarrow>
  ('h \<times> _ ) set \<Rightarrow>
  ('i \<times> _ ) set \<Rightarrow>
  ('j \<times> _ ) set \<Rightarrow>
  ('k \<times> _ ) set \<Rightarrow>
  ('l \<times> _ ) set \<Rightarrow>
  ('m \<times> _ ) set \<Rightarrow>
  ('n \<times> _ ) set \<Rightarrow>
  ('o \<times> _ ) set \<Rightarrow>
  ('p \<times> _ ) set \<Rightarrow>
  (('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) tuple16 \<times> _)set\<close> where
  \<open>tuple16_rel a_assn b_assn' c_assn d_assn e_assn f_assn g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn p_assn =
   {(S, T). case (S, T) of
  (Tuple16 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena,
   Tuple16 M' N' D' i' W' ivmtf' icount' ccach' lbd' outl' heur' stats' aivdom' clss' opts' arena')
     \<Rightarrow>
 ((M, M')\<in>a_assn \<and> (N, N')\<in>b_assn' \<and>  (D, D')\<in>c_assn  \<and>  (i,i')\<in>d_assn \<and>
  (W, W')\<in>e_assn \<and>   (ivmtf, ivmtf')\<in>f_assn \<and>  (icount, icount')\<in> g_assn \<and>  (ccach,ccach')\<in> h_assn\<and>
  (lbd,lbd')\<in>i_assn \<and>   (outl,outl')\<in> j_assn\<and>   (heur,heur')\<in>k_assn  \<and>   (stats,stats')\<in> l_assn\<and>
     (aivdom,aivdom')\<in> m_assn\<and>  (clss,clss')\<in> n_assn\<and>   (opts,opts')\<in>o_assn  \<and>  (arena,arena')\<in>p_assn)
  }\<close>

lemma tuple16_assn_tuple16_rel:
  \<open>tuple16_assn (pure A) (pure B)(pure C)(pure D)(pure E)(pure F)(pure G)(pure H)(pure I)(pure J)(pure K)(pure L)(pure M)(pure N)(pure KO)(pure P) =
  pure (tuple16_rel A B C D E F G H I J K L M N KO P)\<close>
  by (auto intro!: ext simp: pure_def import_param_3(1) split: tuple16.splits)

lemma pure_keep_detroy: "(pure R)\<^sup>k = (pure R)\<^sup>d"
  by (auto intro!: ext simp: invalid_pure_recover)
lemma "is_pure R \<Longrightarrow> R\<^sup>k = R\<^sup>d"
  by (metis is_pure_conv pure_keep_detroy)

lemma isasat_stats_assn_pure_keep:
  \<open>isasat_stats_assn\<^sup>d = isasat_stats_assn\<^sup>k\<close>
  unfolding isasat_stats_assn_def tuple16_assn_tuple16_rel search_stats_assn_def lbd_size_limit_assn_def
    prod_assn_pure_conv pure_lits_stats_assn_def subsumption_stats_assn_def
    binary_stats_assn_def pure_lits_stats_assn_def pure_keep_detroy ..

lemmas [unfolded isasat_stats_assn_pure_keep, sepref_fr_rules] =
  remove_a_code.refine
  remove_b_code.refine
  remove_c_code.refine
  remove_d_code.refine
  remove_e_code.refine
  remove_f_code.refine

named_theorems stats_extractors \<open>Definition of all functions modifying the state\<close>

lemmas [stats_extractors] =
  extract_search_strategy_stats_def
  extract_binary_stats_def
  extract_subsumption_stats_def
  extract_avg_lbd_def
  extract_pure_lits_stats_def
  tuple16_ops.remove_a_def
  tuple16_ops.remove_b_def
  tuple16_ops.remove_c_def
  tuple16_ops.remove_d_def
  tuple16_ops.remove_e_def
  tuple16_ops.remove_f_def
  tuple16_ops.update_a_def
  tuple16_ops.update_b_def
  tuple16_ops.update_c_def
  tuple16_ops.update_d_def
  tuple16_ops.update_e_def
  tuple16_ops.update_f_def


text \<open>We do some cheating to simplify code generation, instead of using our alternative definitions
  as for the states.\<close>
lemma stats_code_unfold:
  \<open>get_search_stats x = fst (extract_search_strategy_stats x)\<close>
  \<open>get_binary_stats x = fst (extract_binary_stats x)\<close>
  \<open>get_subsumption_stats x = fst (extract_subsumption_stats x)\<close>
  \<open>get_pure_lits_stats x = fst (extract_pure_lits_stats x)\<close>
  \<open>get_avg_lbd_stats x = fst (extract_avg_lbd x)\<close>
  \<open>get_lsize_limit_stats x = fst (extract_lbd_size_limit_stats x)\<close>
  \<open>set_propagation_stats a x = update_a a x\<close>
  \<open>set_binary_stats b x = update_b b x\<close>
  \<open>set_subsumption_stats c x = update_c c x\<close>
  \<open>set_avg_lbd_stats lbd x = update_d lbd x\<close>
  \<open>set_pure_lits_stats e x = update_e e x\<close>
  \<open>set_lsize_limit_stats f x = update_f f x\<close>
  by (cases x; auto simp: get_search_stats_def get_avg_lbd_stats_def
    set_avg_lbd_stats_def set_propagation_stats_def set_binary_stats_def
    set_subsumption_stats_def set_pure_lits_stats_def get_lsize_limit_stats_def
    extract_lbd_size_limit_stats_def
    get_subsumption_stats_def get_pure_lits_stats_def set_lsize_limit_stats_def
    get_binary_stats_def stats_extractors; fail)+

lemma Mreturn_comp_Tuple16:
  \<open>(Mreturn o\<^sub>1\<^sub>6 Tuple16) a b c d e f g h i j k l m n ko p =
  Mreturn (Tuple16 a b c d e f g h i j k l m n ko p)\<close>
  by auto

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  remove_a_code_alt_def[unfolded tuple16.remove_a_code_alt_def Mreturn_comp_Tuple16]
  remove_b_code_alt_def[unfolded tuple16.remove_b_code_alt_def Mreturn_comp_Tuple16]
  remove_c_code_alt_def[unfolded tuple16.remove_c_code_alt_def Mreturn_comp_Tuple16]
  remove_d_code_alt_def[unfolded tuple16.remove_d_code_alt_def Mreturn_comp_Tuple16]
  remove_e_code_alt_def[unfolded tuple16.remove_e_code_alt_def Mreturn_comp_Tuple16]
  remove_f_code_alt_def[unfolded tuple16.remove_f_code_alt_def Mreturn_comp_Tuple16]

lemma [safe_constraint_rules]: \<open>CONSTRAINT is_pure isasat_stats_assn\<close>
  unfolding isasat_stats_assn_def tuple16_assn_tuple16_rel search_stats_assn_def
    prod_assn_pure_conv pure_lits_stats_assn_def subsumption_stats_assn_def lbd_size_limit_assn_def
    binary_stats_assn_def pure_lits_stats_assn_def pure_keep_detroy by auto

lemma id_unat[sepref_fr_rules]:
  \<open>(Mreturn o id, RETURN o unat) \<in> word32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  apply vcg
  by (auto simp: ENTAILS_def unat_rel_def unat.rel_def br_def pred_lift_merge_simps
    pred_lift_def pure_true_conv)

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure B \<Longrightarrow> (Mreturn o (\<lambda>(a,b). a), RETURN o fst) \<in> (A \<times>\<^sub>a B)\<^sup>d \<rightarrow>\<^sub>a A\<close>
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: ENTAILS_def)
  by (smt (verit, best) entails_def fri_startI_extended(3) is_pure_iff_pure_assn pure_part_pure_eq pure_part_split_conj pure_true_conv sep_conj_aci(5))

sepref_def Search_Stats_conflicts_impl
  is \<open>RETURN o Search_Stats_conflicts\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_conflicts_def
  by sepref

sepref_def Search_Stats_units_since_gcs_impl
  is \<open>RETURN o Search_Stats_units_since_gcs\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_units_since_gcs_def
  by sepref

sepref_def Search_Stats_reset_units_since_gc_impl
  is \<open>RETURN o Search_Stats_reset_units_since_gc\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_reset_units_since_gc_def
  by sepref

sepref_def Search_Stats_fixed_impl
  is \<open>RETURN o Search_Stats_fixed\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_fixed_def
  by sepref

sepref_def add_lbd_stats_impl
  is \<open>uncurry (RETURN oo add_lbd)\<close>
  :: \<open>word32_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding add_lbd_def stats_code_unfold
  by sepref

sepref_def get_conflict_count_stats_impl
  is \<open>(RETURN o get_conflict_count)\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_conflicts_def stats_code_unfold
  by sepref


sepref_def units_since_last_GC_stats_impl
  is \<open>(RETURN o units_since_last_GC)\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding units_since_last_GC_def stats_code_unfold
  by sepref

sepref_def reset_units_since_last_GC_stats_impl
  is \<open>(RETURN o reset_units_since_last_GC)\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding reset_units_since_last_GC_def stats_code_unfold
  by sepref

sepref_def Search_Stats_incr_irred_impl
  is \<open>RETURN o Search_Stats_incr_irred\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_irred_def
  by sepref

sepref_def Search_Stats_decr_irred_impl
  is \<open>RETURN o Search_Stats_decr_irred\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_decr_irred_def
  by sepref

sepref_def Search_Stats_incr_propagation_impl
  is \<open>RETURN o Search_Stats_incr_propagation\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_propagation_def
  by sepref

sepref_def Search_Stats_incr_propagation_by_impl
  is \<open>uncurry (RETURN oo Search_Stats_incr_propagation_by)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_propagation_by_def
  by sepref

sepref_def Search_Stats_set_not_conflict_until_impl
  is \<open>uncurry (RETURN oo Search_Stats_set_no_conflict_until)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_set_no_conflict_until_def
  by sepref

sepref_def Search_Stats_no_conflict_until_impl
  is \<open>RETURN o Search_Stats_no_conflict_until\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_no_conflict_until_def
  by sepref

sepref_def Search_Stats_incr_conflicts_impl
  is \<open>RETURN o Search_Stats_incr_conflicts\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_conflicts_def
  by sepref

sepref_def Search_Stats_incr_decisions_impl
  is \<open>RETURN o Search_Stats_incr_decisions\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_decisions_def
  by sepref

sepref_def Search_Stats_incr_restarts_impl
  is \<open>RETURN o Search_Stats_incr_restarts\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_restarts_def
  by sepref

sepref_def Search_Stats_incr_reductions_impl
  is \<open>RETURN o Search_Stats_incr_reductions\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_reductions_def
  by sepref

sepref_def Search_Stats_incr_fixed_impl
  is \<open>RETURN o Search_Stats_incr_fixed\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_fixed_def
  by sepref

sepref_def Search_Stats_incr_fixed_by_impl
  is \<open>uncurry (RETURN oo Search_Stats_incr_fixed_by)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_fixed_by_def
  by sepref

sepref_def Search_Stats_incr_gcs_impl
  is \<open>RETURN o Search_Stats_incr_gcs\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_gcs_def
  by sepref

sepref_def Search_Stats_incr_gcs_by_impl
  is \<open>uncurry (RETURN oo Search_Stats_incr_units_since_gc_by)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_units_since_gc_by_def
  by sepref

sepref_def Search_Stats_incr_units_since_gc_impl
  is \<open>RETURN o Search_Stats_incr_units_since_gc\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def Search_Stats_incr_units_since_gc_def
  by sepref

sepref_def Pure_lits_Stats_incr_rounds_impl
  is \<open>RETURN o Pure_lits_Stats_incr_rounds\<close>
  :: \<open>pure_lits_stats_assn\<^sup>k \<rightarrow>\<^sub>a pure_lits_stats_assn\<close>
  unfolding pure_lits_stats_assn_def Pure_lits_Stats_incr_rounds_def
  by sepref

sepref_def Pure_lits_Stats_incr_removed_impl
  is \<open>RETURN o Pure_lits_Stats_incr_removed\<close>
  :: \<open>pure_lits_stats_assn\<^sup>k \<rightarrow>\<^sub>a pure_lits_stats_assn\<close>
  unfolding pure_lits_stats_assn_def Pure_lits_Stats_incr_removed_def
  by sepref

sepref_def Binary_Stats_incr_units_impl
  is \<open>RETURN o Binary_Stats_incr_units\<close>
  :: \<open>binary_stats_assn\<^sup>k \<rightarrow>\<^sub>a binary_stats_assn\<close>
  unfolding binary_stats_assn_def Binary_Stats_incr_units_def
  by sepref

sepref_def Binary_Stats_incr_removed_def
  is \<open>RETURN o Binary_Stats_incr_removed\<close>
  :: \<open>binary_stats_assn\<^sup>k \<rightarrow>\<^sub>a binary_stats_assn\<close>
  unfolding Binary_Stats_incr_removed_def binary_stats_assn_def
  by sepref

sepref_def Search_Stats_restarts_impl
  is \<open>RETURN o Search_Stats_restarts\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_restarts_def
  by sepref

sepref_def Search_Stats_reductions_impl
  is \<open>RETURN o Search_Stats_reductions\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_reductions_def
  by sepref

sepref_def Search_Stats_irred_impl
  is \<open>RETURN o Search_Stats_irred\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_irred_def
  by sepref

sepref_def Search_Stats_propagations_impl
  is \<open>RETURN o Search_Stats_propagations\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_propagations_def
  by sepref

sepref_def Search_Stats_gcs_impl
  is \<open>RETURN o Search_Stats_gcs\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_gcs_def
  by sepref

sepref_register Search_Stats_fixed Search_Stats_incr_irred Search_Stats_decr_irred
  Search_Stats_incr_propagation Search_Stats_incr_conflicts
  Search_Stats_incr_decisions Search_Stats_incr_restarts
  Search_Stats_incr_reductions Search_Stats_incr_fixed Search_Stats_incr_gcs
  Pure_lits_Stats_incr_rounds Pure_lits_Stats_incr_removed
  Binary_Stats_incr_removed Binary_Stats_incr_units
  Search_Stats_reductions Search_Stats_restarts
  Search_Stats_irred Search_Stats_propagations Search_Stats_gcs

sepref_def Search_Stats_decisions_impl
  is \<open>RETURN o Search_Stats_decisions\<close>
  :: \<open>search_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding search_stats_assn_def Search_Stats_decisions_def
  by sepref

sepref_def Binary_stats_rounds_impl
  is \<open>RETURN o Binary_Stats_rounds\<close>
  :: \<open>binary_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding binary_stats_assn_def Binary_Stats_rounds_def
  by sepref

sepref_def Binary_stats_units_impl
  is \<open>RETURN o Binary_Stats_units\<close>
  :: \<open>binary_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding binary_stats_assn_def Binary_Stats_units_def
  by sepref

sepref_def Binary_stats_removed_impl
  is \<open>RETURN o Binary_Stats_removed\<close>
  :: \<open>binary_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding binary_stats_assn_def Binary_Stats_removed_def
  by sepref

sepref_def Pure_Lits_Stats_removed_impl
  is \<open>RETURN o Pure_Lits_Stats_removed\<close>
  :: \<open>pure_lits_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding pure_lits_stats_assn_def Pure_Lits_Stats_removed_def
  by sepref

sepref_def Pure_Lits_Stats_removed_rounds_impl
  is \<open>RETURN o Pure_Lits_Stats_rounds\<close>
  :: \<open>pure_lits_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding pure_lits_stats_assn_def Pure_Lits_Stats_rounds_def
  by sepref

sepref_def LSize_Stats_lbd_impl
  is \<open>RETURN o LSize_Stats_lbd\<close>
  :: \<open>lbd_size_limit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding  LSize_Stats_lbd_def lbd_size_limit_assn_def
  by sepref

sepref_def LSize_Stats_size_impl
  is \<open>RETURN o LSize_Stats_size\<close>
  :: \<open>lbd_size_limit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding  LSize_Stats_size_def lbd_size_limit_assn_def
  by sepref

sepref_def LSize_Stats_impl
  is \<open>uncurry (RETURN oo LSize_Stats)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a lbd_size_limit_assn\<close>
  unfolding  LSize_Stats_def lbd_size_limit_assn_def
  by sepref


sepref_register Search_Stats_decisions Pure_Lits_Stats_rounds Pure_Lits_Stats_removed
  Binary_Stats_removed Binary_Stats_rounds Binary_Stats_units
sepref_def stats_decisions_impl
  is \<open>RETURN o stats_decisions\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_decisions_def stats_code_unfold by sepref

sepref_def stats_irred_impl
  is \<open>RETURN o stats_irred\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_irred_def stats_code_unfold by sepref

sepref_def stats_binary_units_impl
  is \<open>RETURN o stats_binary_units\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_binary_units_def stats_code_unfold by sepref

sepref_def stats_binary_removed_impl
  is \<open>RETURN o stats_binary_removed\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_binary_removed_def stats_code_unfold by sepref
sepref_def stats_binary_rounds_impl
  is \<open>RETURN o stats_binary_rounds\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_binary_rounds_def stats_code_unfold by sepref

sepref_def stats_pure_lits_rounds_impl
  is \<open>RETURN o stats_pure_lits_rounds\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_pure_lits_rounds_def stats_code_unfold by sepref

sepref_def stats_pure_lits_removed_impl
  is \<open>RETURN o stats_pure_lits_removed\<close> :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
 unfolding stats_pure_lits_removed_def stats_code_unfold by sepref

sepref_def units_since_beginning_stats_impl
  is \<open>(RETURN o units_since_beginning)\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding units_since_beginning_def stats_code_unfold
  by sepref

sepref_def incr_irred_clss_stats_impl
  is \<open>RETURN o incr_irred_clss\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_irred_clss_def stats_code_unfold
  by sepref

sepref_def decr_irred_clss_stats_impl
  is \<open>RETURN o decr_irred_clss\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding decr_irred_clss_def stats_code_unfold
  by sepref

sepref_def incr_propagation_stats_impl
  is \<open>RETURN o incr_propagation\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_propagation_def stats_code_unfold
  by sepref

sepref_def incr_propagation_by_stats_impl
  is \<open>uncurry (RETURN oo incr_propagation_by)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_propagation_by_def stats_code_unfold
  by sepref

sepref_def set_not_conflict_until_stats_impl
  is \<open>uncurry (RETURN oo set_no_conflict_until)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding set_no_conflict_until_def stats_code_unfold
  by sepref

sepref_def no_conflict_until_stats_impl
  is \<open>RETURN o no_conflict_until\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding no_conflict_until_def stats_code_unfold
  by sepref

sepref_def incr_conflict_stats_impl
  is \<open>RETURN o incr_conflict\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_conflict_def stats_code_unfold
  by sepref

sepref_def incr_decision_stats_impl
  is \<open>RETURN o incr_decision\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_decision_def stats_code_unfold
  by sepref

sepref_def incr_restart_stats_impl
  is \<open>RETURN o incr_restart\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_restart_def stats_code_unfold
  by sepref

sepref_def incr_reduction_stats_impl
  is \<open>RETURN o incr_reduction\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_reduction_def stats_code_unfold
  by sepref

sepref_def incr_uset_stats_impl
  is \<open>RETURN o incr_uset\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_uset_def stats_code_unfold
  by sepref

sepref_def incr_uset_by_stats_impl
  is \<open>uncurry (RETURN oo incr_uset_by)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_uset_by_def stats_code_unfold
  by sepref

sepref_def incr_GC_stats_impl
  is \<open>RETURN o incr_GC\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_GC_def stats_code_unfold
  by sepref

sepref_def stats_conflicts_impl
  is \<open>RETURN o stats_conflicts\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_conflicts_def stats_code_unfold
    by sepref

sepref_def incr_units_since_last_GC_impl
  is \<open>RETURN o incr_units_since_last_GC\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_units_since_last_GC_def stats_code_unfold
  by sepref

sepref_def incr_units_since_last_GC_by_impl
  is \<open>uncurry (RETURN oo incr_units_since_last_GC_by)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_units_since_last_GC_by_def stats_code_unfold
  by sepref

sepref_def incr_purelit_rounds_impl
  is \<open>RETURN o incr_purelit_rounds\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_purelit_rounds_def stats_code_unfold
  by sepref

sepref_def incr_purelit_elim_stats_impl
  is \<open>RETURN o incr_purelit_elim\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_purelit_elim_def stats_code_unfold
  by sepref

sepref_def incr_binary_red_removed_impl
  is \<open>RETURN o incr_binary_red_removed\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_binary_red_removed_def stats_code_unfold
  by sepref

sepref_def incr_binary_unit_derived_impl
  is \<open>RETURN o incr_binary_unit_derived\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_binary_unit_derived_def stats_code_unfold
  by sepref

sepref_def get_reduction_count_impl
  is \<open>RETURN o get_reduction_count\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_reduction_count_def stats_code_unfold
  by sepref

sepref_def get_restart_count_impl
  is \<open>RETURN o get_restart_count\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_restart_count_def stats_code_unfold
  by sepref


sepref_def get_irredundant_count_impl
  is \<open>RETURN o irredundant_clss\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding irredundant_clss_def stats_code_unfold
  by sepref

sepref_def stats_propagations_impl
  is \<open>RETURN o stats_propagations\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_propagations_def stats_code_unfold
  by sepref

sepref_def stats_restarts_impl
  is \<open>RETURN o stats_restarts\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_restarts_def stats_code_unfold
  by sepref

sepref_def stats_reductions_impl
  is \<open>RETURN o stats_reductions\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_reductions_def stats_code_unfold
  by sepref

sepref_def stats_fixed_impl
  is \<open>RETURN o stats_fixed\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_fixed_def stats_code_unfold
  by sepref

sepref_def stats_gcs_impl
  is \<open>RETURN o stats_gcs\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_gcs_def stats_code_unfold
  by sepref

sepref_def stats_avg_lbd_mpl
  is \<open>RETURN o stats_avg_lbd\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding stats_avg_lbd_def stats_code_unfold
  by sepref

sepref_register LSize_Stats_lbd LSize_Stats_size LSize_Stats
sepref_def stats_lbd_limit_impl
  is \<open>RETURN o stats_lbd_limit\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding stats_lbd_limit_def stats_code_unfold
  by sepref

sepref_def stats_size_limit_impl
  is \<open>RETURN o stats_size_limit\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding stats_size_limit_def stats_code_unfold
  by sepref

sepref_def Subsumption_Stats_incr_strengthening_impl
  is \<open>RETURN o Subsumption_Stats_incr_strengthening\<close>
  :: \<open>subsumption_stats_assn\<^sup>d \<rightarrow>\<^sub>a subsumption_stats_assn\<close>
  unfolding Subsumption_Stats_incr_strengthening_def subsumption_stats_assn_def
  by sepref

sepref_def incr_forward_strengethening_impl
  is \<open>RETURN o incr_forward_strengethening\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_forward_strengethening_def stats_code_unfold
  by sepref

sepref_def Subsumption_Stats_incr_subsumed_impl
  is \<open>RETURN o Subsumption_Stats_incr_subsumed\<close>
  :: \<open>subsumption_stats_assn\<^sup>d \<rightarrow>\<^sub>a subsumption_stats_assn\<close>
  unfolding Subsumption_Stats_incr_subsumed_def subsumption_stats_assn_def
  by sepref

sepref_def Subsumption_Stats_incr_tried_impl
  is \<open>RETURN o Subsumption_Stats_incr_tried\<close>
  :: \<open>subsumption_stats_assn\<^sup>d \<rightarrow>\<^sub>a subsumption_stats_assn\<close>
  unfolding Subsumption_Stats_incr_tried_def subsumption_stats_assn_def
  by sepref

sepref_def Subsumption_Stats_incr_rounds_impl
  is \<open>RETURN o Subsumption_Stats_incr_rounds\<close>
  :: \<open>subsumption_stats_assn\<^sup>d \<rightarrow>\<^sub>a subsumption_stats_assn\<close>
  unfolding Subsumption_Stats_incr_rounds_def subsumption_stats_assn_def
  by sepref

sepref_def incr_forward_subsumed_impl
  is \<open>RETURN o incr_forward_subsumed\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_forward_subsumed_def stats_code_unfold
  by sepref

sepref_def incr_forward_rounds_impl
  is \<open>RETURN o incr_forward_rounds\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_forward_rounds_def stats_code_unfold
  by sepref

sepref_def incr_forward_tried_impl
  is \<open>RETURN o incr_forward_tried\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding incr_forward_tried_def stats_code_unfold
  by sepref

sepref_def Subsumption_Stats_rounds_impl
  is \<open>RETURN o Subsumption_Stats_rounds\<close>
  :: \<open>subsumption_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding subsumption_stats_assn_def Subsumption_Stats_rounds_def
  by sepref
sepref_def Subsumption_Stats_strengthened_impl
  is \<open>RETURN o Subsumption_Stats_strengthened\<close>
  :: \<open>subsumption_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding subsumption_stats_assn_def Subsumption_Stats_strengthened_def
  by sepref
sepref_def Subsumption_Stats_subsumed_impl
  is \<open>RETURN o Subsumption_Stats_subsumed\<close>
  :: \<open>subsumption_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding subsumption_stats_assn_def Subsumption_Stats_subsumed_def
  by sepref
sepref_def Subsumption_Stats_tried_impl
  is \<open>RETURN o Subsumption_Stats_tried\<close>
  :: \<open>subsumption_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding subsumption_stats_assn_def Subsumption_Stats_tried_def
  by sepref

sepref_def stats_forward_rounds_impl
  is \<open>RETURN o stats_forward_rounds\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding stats_forward_rounds_def stats_code_unfold
  by sepref

sepref_register stats_forward_tried stats_forward_subsumed stats_forward_strengthened

sepref_def stats_forward_subsumed_impl
  is \<open>RETURN o stats_forward_subsumed\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding stats_forward_subsumed_def stats_code_unfold
  by sepref

sepref_def stats_forward_tried_impl
  is \<open>RETURN o stats_forward_tried\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding stats_forward_tried_def stats_code_unfold
  by sepref

sepref_def stats_forward_strengthened_impl
  is \<open>RETURN o stats_forward_strengthened\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding stats_forward_strengthened_def stats_code_unfold
  by sepref

lemmas [llvm_inline] = Mreturn_comp_Tuple16

sepref_register empty_stats
sepref_def empty_stats_impl
  is \<open>uncurry0 (RETURN empty_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding empty_stats_def empty_search_stats_def[symmetric]
  unfolding empty_subsumption_stats_def[symmetric]
  unfolding empty_binary_stats_def[symmetric]
  apply (subst empty_pure_lits_stats_def[symmetric])
  apply (subst empty_lsize_limit_stats_def[symmetric])
  by sepref

definition empty_search_stats_clss where
  \<open>empty_search_stats_clss n = (0,0,0,0,0,0,0,0,n,0)\<close>

sepref_def empty_search_stats_clss_impl
  is \<open>(RETURN o empty_search_stats_clss)\<close>
  :: \<open>word64_assn\<^sup>k \<rightarrow>\<^sub>a search_stats_assn\<close>
  unfolding search_stats_assn_def empty_search_stats_clss_def
  by sepref

sepref_def empty_stats_clss_impl
  is \<open>(RETURN o empty_stats_clss)\<close>
  :: \<open>word64_assn\<^sup>k \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding empty_stats_clss_def empty_search_stats_clss_def[symmetric]
  unfolding empty_subsumption_stats_def[symmetric]
  unfolding empty_binary_stats_def[symmetric]
  apply (subst empty_pure_lits_stats_def[symmetric])
  apply (subst empty_lsize_limit_stats_def[symmetric])
  by sepref

export_llvm empty_stats_impl

sepref_register unset_fully_propagated_heur is_fully_propagated_heur set_fully_propagated_heur


abbreviation (input) \<open>restart_info_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel\<close>
abbreviation (input) restart_info_assn where
  \<open>restart_info_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

lemma restart_info_params[sepref_import_param]:
  "(incr_conflict_count_since_last_restart,incr_conflict_count_since_last_restart) \<in>
    restart_info_rel \<rightarrow> restart_info_rel"
  "(restart_info_update_lvl_avg,restart_info_update_lvl_avg) \<in>
    word32_rel \<rightarrow> restart_info_rel \<rightarrow> restart_info_rel"
  \<open>(restart_info_init,restart_info_init) \<in> restart_info_rel\<close>
  \<open>(restart_info_restart_done,restart_info_restart_done) \<in> restart_info_rel \<rightarrow> restart_info_rel\<close>
  by auto

lemmas [llvm_inline] =
  incr_conflict_count_since_last_restart_def
  restart_info_update_lvl_avg_def
  restart_info_init_def
  restart_info_restart_done_def

abbreviation (input) \<open>schedule_info_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel\<close>
abbreviation (input) schedule_info_assn where
  \<open>schedule_info_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

lemma schedule_info_params[sepref_import_param]:
  "(next_pure_lits_schedule_info, next_pure_lits_schedule_info) \<in>
    schedule_info_rel \<rightarrow> word64_rel"
  "(schedule_next_pure_lits_info, schedule_next_pure_lits_info) \<in>
    schedule_info_rel \<rightarrow> schedule_info_rel"
  "(next_reduce_schedule_info, next_reduce_schedule_info) \<in> schedule_info_rel \<rightarrow> word64_rel"
  "(schedule_next_reduce_info, schedule_next_reduce_info) \<in>
    word64_rel \<rightarrow> schedule_info_rel \<rightarrow> schedule_info_rel"
  by (auto)

sepref_register FOCUSED_MODE STABLE_MODE DEFAULT_INIT_PHASE

sepref_def FOCUSED_MODE_impl
  is \<open>uncurry0 (RETURN FOCUSED_MODE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FOCUSED_MODE_def
  by sepref

sepref_def STABLE_MODE_impl
  is \<open>uncurry0 (RETURN STABLE_MODE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding STABLE_MODE_def
  by sepref

definition lcount_assn :: \<open>clss_size \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>lcount_assn \<equiv> uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn\<close>

lemma [safe_constraint_rules]:
  \<open>CONSTRAINT Sepref_Basic.is_pure lcount_assn\<close>
  unfolding lcount_assn_def
  by auto

sepref_def clss_size_lcount_fast_code
  is \<open>RETURN o clss_size_lcount\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding clss_size_lcount_def lcount_assn_def
  by sepref

sepref_register clss_size_resetUS

lemma clss_size_resetUS_alt_def:
  \<open>RETURN o clss_size_resetUS =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, 0, lcountU0))\<close>
  by (auto simp: clss_size_resetUS_def)

sepref_def clss_size_resetUS_fast_code
  is \<open>RETURN o clss_size_resetUS\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetUS_alt_def lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountUS_alt_def:
  \<open>RETURN o clss_size_incr_lcountUS =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, lcountUS + 1, lcountU0))\<close>
  by (auto simp: clss_size_incr_lcountUS_def)

sepref_def clss_size_incr_lcountUS_fast_code
  is \<open>RETURN o clss_size_incr_lcountUS\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUS S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUS_alt_def lcount_assn_def clss_size_lcountUS_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_resetU0_alt_def:
  \<open>RETURN o clss_size_resetU0 =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, lcountUS, 0))\<close>
  by (auto simp: clss_size_resetU0_def)

sepref_def clss_size_resetU0_fast_code
  is \<open>RETURN o clss_size_resetU0\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetU0_alt_def lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountU0_alt_def:
  \<open>RETURN o clss_size_incr_lcountU0 =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, lcountUS, lcountU0+1))\<close>
  by (auto simp: clss_size_incr_lcountU0_def)

sepref_def clss_size_incr_lcountU0_fast_code
  is \<open>RETURN o clss_size_incr_lcountU0\<close>
  :: \<open>[\<lambda>S. clss_size_lcountU0 S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountU0_alt_def lcount_assn_def clss_size_lcountU0_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_resetUE_alt_def:
  \<open>RETURN o clss_size_resetUE =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, 0, lcountUEk, lcountUS, lcountU0))\<close>
  by (auto simp: clss_size_resetUE_def)

sepref_def clss_size_resetUE_fast_code
  is \<open>RETURN o clss_size_resetUE\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetUE_alt_def lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountUE_alt_def:
  \<open>RETURN o clss_size_incr_lcountUE =
  (\<lambda>(lcount, lcountUE, lcountUS). RETURN (lcount, lcountUE + 1, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcountUE_def)

sepref_def clss_size_incr_lcountUE_fast_code
  is \<open>RETURN o clss_size_incr_lcountUE\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUE S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUE_alt_def lcount_assn_def clss_size_lcountUE_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountUEk_alt_def:
  \<open>RETURN o clss_size_incr_lcountUEk =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). RETURN (lcount, lcountUE, lcountUEk + 1, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcountUEk_def)

sepref_def clss_size_incr_lcountUEk_fast_code
  is \<open>RETURN o clss_size_incr_lcountUEk\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUEk S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUEk_alt_def lcount_assn_def clss_size_lcountUEk_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal mk_free_lookup_clause_rel_assn[sepref_frame_free_rules]: \<open>MK_FREE lcount_assn ?fr\<close>
  unfolding lcount_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

lemma clss_size_lcountUE_alt_def:
  \<open>RETURN o clss_size_lcountUE = (\<lambda>(lcount, lcountUE, lcountUS). RETURN lcountUE)\<close>
  by (auto simp: clss_size_lcountUE_def)

sepref_def clss_size_lcountUE_fast_code
  is \<open>RETURN o clss_size_lcountUE\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUE_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_lcountUS_alt_def:
  \<open>RETURN o clss_size_lcountUS = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN lcountUS)\<close>
  by (auto simp: clss_size_lcountUS_def)

sepref_def clss_size_lcountUSt_fast_code
  is \<open>RETURN o clss_size_lcountUS\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUS_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_lcountU0_alt_def:
  \<open>RETURN o clss_size_lcountU0 = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN lcountU0)\<close>
  by (auto simp: clss_size_lcountU0_def)

sepref_def clss_size_lcountU0_fast_code
  is \<open>RETURN o clss_size_lcountU0\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountU0_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_incr_allcount_alt_def:
  \<open>RETURN o clss_size_allcount =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount + lcountUE + lcountUEk + lcountUS + lcountU0))\<close>
  by (auto simp: clss_size_allcount_def)

sepref_def clss_size_allcount_fast_code
  is \<open>RETURN o clss_size_allcount\<close>
  :: \<open>[\<lambda>S. clss_size_allcount S < max_snat 64]\<^sub>a lcount_assn\<^sup>d \<rightarrow> uint64_nat_assn\<close>
  unfolding clss_size_incr_allcount_alt_def lcount_assn_def clss_size_allcount_def
  by sepref


lemma clss_size_decr_lcount_alt_def:
  \<open>RETURN o clss_size_decr_lcount =
  (\<lambda>(lcount, lcountUE, lcountUS). RETURN (lcount - 1, lcountUE, lcountUS))\<close>
  by (auto simp: clss_size_decr_lcount_def)

sepref_def clss_size_decr_lcount_fast_code
  is \<open>RETURN o clss_size_decr_lcount\<close>
  :: \<open>[\<lambda>S. clss_size_lcount S \<ge> 1]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding lcount_assn_def clss_size_decr_lcount_alt_def clss_size_lcount_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


lemma emag_get_value_alt_def:
  \<open>ema_get_value = (\<lambda>(a, b, c, d). a)\<close>
  by auto

sepref_def ema_get_value_impl
  is \<open>RETURN o ema_get_value\<close>
  :: \<open>ema_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding emag_get_value_alt_def
  by sepref

lemma emag_extract_value_alt_def:
  \<open>ema_extract_value = (\<lambda>(a, b, c, d). a >> EMA_FIXPOINT_SIZE)\<close>
  by auto

sepref_def ema_extract_value_impl
  is \<open>RETURN o ema_extract_value\<close>
  :: \<open>ema_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding emag_extract_value_alt_def EMA_FIXPOINT_SIZE_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def schedule_next_pure_lits_info_impl
  is \<open>RETURN o schedule_next_pure_lits_info\<close>
  :: \<open>schedule_info_assn\<^sup>k \<rightarrow>\<^sub>a schedule_info_assn\<close>
  unfolding schedule_next_pure_lits_info_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def next_pure_lits_schedule_info_impl
  is \<open>RETURN o next_pure_lits_schedule_info\<close>
  :: \<open>schedule_info_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding next_pure_lits_schedule_info_def
  by sepref

sepref_def schedule_next_reduce_info_impl
  is \<open>uncurry (RETURN oo schedule_next_reduce_info)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a schedule_info_assn\<^sup>k \<rightarrow>\<^sub>a schedule_info_assn\<close>
  unfolding schedule_next_reduce_info_def
  by sepref

sepref_def next_reduce_schedule_info_impl
  is \<open>RETURN o next_reduce_schedule_info\<close>
  :: \<open>schedule_info_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding next_reduce_schedule_info_def
  by sepref

sepref_def schedule_next_subsume_info_impl
  is \<open>uncurry (RETURN oo schedule_next_subsume_info)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a schedule_info_assn\<^sup>k \<rightarrow>\<^sub>a schedule_info_assn\<close>
  unfolding schedule_next_subsume_info_def
  by sepref

sepref_def next_subsume_schedule_info_impl
  is \<open>RETURN o next_subsume_schedule_info\<close>
  :: \<open>schedule_info_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding next_subsume_schedule_info_def
  by sepref


type_synonym heur_assn = \<open>(ema \<times> ema \<times> restart_info \<times> 64 word \<times>
  (phase_saver_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> 64 word \<times> 64 word) \<times>
  reluctant_rel_assn \<times> 1 word \<times> phase_saver_assn \<times> (64 word \<times> 64 word \<times> 64 word))\<close>

definition heuristic_int_assn :: \<open>restart_heuristics \<Rightarrow> heur_assn \<Rightarrow> assn\<close> where
  \<open>heuristic_int_assn = ema_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  restart_info_assn \<times>\<^sub>a
  word64_assn \<times>\<^sub>a phase_heur_assn \<times>\<^sub>a reluctant_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a phase_saver_assn \<times>\<^sub>a
  schedule_info_assn\<close>

abbreviation heur_int_rel :: \<open>(restart_heuristics \<times> restart_heuristics) set\<close> where
  \<open>heur_int_rel \<equiv> Id\<close>

abbreviation heur_rel :: \<open>(restart_heuristics \<times> isasat_restart_heuristics) set\<close> where
  \<open>heur_rel \<equiv> \<langle>heur_int_rel\<rangle>code_hider_rel\<close>

definition heuristic_assn :: \<open>isasat_restart_heuristics \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>heuristic_assn = code_hider_assn heuristic_int_assn heur_int_rel\<close>

lemma heuristic_assn_alt_def:
  \<open>heuristic_assn = hr_comp heuristic_int_assn heur_rel\<close>
  unfolding heuristic_assn_def code_hider_assn_def by auto

context
  notes [fcomp_norm_unfold] = heuristic_assn_def[symmetric] heuristic_assn_alt_def[symmetric]
begin

lemma set_zero_wasted_stats_set_zero_wasted_stats:
  \<open>(set_zero_wasted_stats, set_zero_wasted) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_tick_stats_heuristic_reluctant_tick:
  \<open>(heuristic_reluctant_tick_stats, heuristic_reluctant_tick) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_enable_stats_heuristic_reluctant_enable:
  \<open>(heuristic_reluctant_enable_stats,heuristic_reluctant_enable) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_disable_stats_heuristic_reluctant_disable:
  \<open>(heuristic_reluctant_disable_stats,heuristic_reluctant_disable) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_triggered_stats_heuristic_reluctant_triggered:
  \<open>(heuristic_reluctant_triggered_stats,heuristic_reluctant_triggered) \<in> heur_rel \<rightarrow> heur_rel \<times>\<^sub>f bool_rel\<close> and
  heuristic_reluctant_triggered2_stats_heuristic_reluctant_triggered2:
  \<open>(heuristic_reluctant_triggered2_stats,heuristic_reluctant_triggered2) \<in> heur_rel \<rightarrow> bool_rel\<close> and
  heuristic_reluctant_untrigger_stats_heuristic_reluctant_untrigger:
  \<open>(heuristic_reluctant_untrigger_stats, heuristic_reluctant_untrigger) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  end_of_rephasing_phase_heur_stats_end_of_rephasing_phase_heur:
  \<open>(end_of_rephasing_phase_heur_stats, end_of_rephasing_phase_heur) \<in> heur_rel \<rightarrow> word64_rel\<close> and
  is_fully_propagated_heur_stats_is_fully_propagated_heur:
  \<open>(is_fully_propagated_heur_stats, is_fully_propagated_heur) \<in> heur_rel \<rightarrow> bool_rel\<close> and
  set_fully_propagated_heur_stats_set_fully_propagated_heur:
    \<open>(set_fully_propagated_heur_stats, set_fully_propagated_heur) \<in> heur_rel \<rightarrow> heur_rel\<close>and
  unset_fully_propagated_heur_stats_unset_fully_propagated_heur:
  \<open>(unset_fully_propagated_heur_stats, unset_fully_propagated_heur) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  restart_info_restart_done_heur_stats_restart_info_restart_done_heur:
  \<open>(restart_info_restart_done_heur_stats, restart_info_restart_done_heur) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  set_zero_wasted_stats_set_zero_wasted:
  \<open>(set_zero_wasted_stats, set_zero_wasted) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  wasted_of_stats_wasted_of:
  \<open>(wasted_of_stats, wasted_of) \<in> heur_rel \<rightarrow> word64_rel\<close> and
  slow_ema_of_stats_slow_ema_of:
  \<open>(slow_ema_of_stats, slow_ema_of) \<in> heur_rel \<rightarrow> ema_rel\<close> and
  fast_ema_of_stats_fast_ema_of:
  \<open>(fast_ema_of_stats, fast_ema_of) \<in> heur_rel \<rightarrow> ema_rel\<close> and
  current_restart_phase_stats_current_restart_phase:
  \<open>(current_restart_phase_stats, current_restart_phase) \<in> heur_rel \<rightarrow> word_rel\<close> and
  incr_wasted_stats_incr_wasted:
  \<open>(incr_wasted_stats, incr_wasted) \<in> word_rel \<rightarrow> heur_rel \<rightarrow> heur_rel\<close> and
  current_rephasing_phase_stats_current_rephasing_phase:
  \<open>(current_rephasing_phase_stats, current_rephasing_phase) \<in> heur_rel \<rightarrow> word_rel\<close> and
  get_next_phase_heur_stats_get_next_phase_heur:
  \<open>(uncurry2 (get_next_phase_heur_stats), uncurry2 (get_next_phase_heur))
  \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f heur_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close> and
  get_conflict_count_since_last_restart_stats_get_conflict_count_since_last_restart_stats:
  \<open>(get_conflict_count_since_last_restart_stats, get_conflict_count_since_last_restart)
  \<in> heur_rel \<rightarrow> word_rel\<close> and
  schedule_next_pure_lits_stats_schedule_next_pure_lits:
    \<open>(schedule_next_pure_lits_stats, schedule_next_pure_lits) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  next_pure_lits_schedule_next_pure_lits_schedule_stats:
    \<open>(next_pure_lits_schedule_info_stats, next_pure_lits_schedule) \<in> heur_rel \<rightarrow> word64_rel\<close> and
  schedule_next_reduce_stats_schedule_next_reduce:
    \<open>(schedule_next_reduce_stats, schedule_next_reduce) \<in> word64_rel \<rightarrow> heur_rel \<rightarrow> heur_rel\<close> and
  next_reduce_schedule_next_reduce_schedule_stats:
    \<open>(next_reduce_schedule_info_stats, next_reduce_schedule) \<in> heur_rel \<rightarrow> word64_rel\<close> and
  schedule_next_subsume_stats_schedule_next_subsume:
    \<open>(schedule_next_subsume_stats, schedule_next_subsume) \<in> word64_rel \<rightarrow> heur_rel \<rightarrow> heur_rel\<close> and
  next_subsume_schedule_next_subsume_schedule_stats:
    \<open>(next_subsume_schedule_info_stats, next_subsume_schedule) \<in> heur_rel \<rightarrow> word64_rel\<close>
  by (auto simp: set_zero_wasted_def code_hider_rel_def heuristic_reluctant_tick_def
    heuristic_reluctant_enable_def heuristic_reluctant_triggered_def apfst_def map_prod_def
    heuristic_reluctant_disable_def heuristic_reluctant_triggered2_def is_fully_propagated_heur_def
    end_of_rephasing_phase_heur_def unset_fully_propagated_heur_def restart_info_restart_done_heur_def
    heuristic_reluctant_untrigger_def set_fully_propagated_heur_def wasted_of_def get_next_phase_heur_def
    slow_ema_of_def fast_ema_of_def current_restart_phase_def incr_wasted_def current_rephasing_phase_def
    get_conflict_count_since_last_restart_def next_pure_lits_schedule_def
    schedule_next_pure_lits_def schedule_next_pure_lits_stats_def next_reduce_schedule_def
    schedule_next_reduce_def schedule_next_reduce_stats_def next_subsume_schedule_def
    schedule_next_subsume_def schedule_next_subsume_stats_def
    intro!: frefI nres_relI
    split: prod.splits)

(*heuristic_reluctant_triggered*)
lemma set_zero_wasted_stats_alt_def:
   \<open>set_zero_wasted_stats= (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>).
    (fast_ema, slow_ema, res_info, 0, \<phi>))\<close>
 by auto

sepref_def set_zero_wasted_stats_impl
  is \<open>RETURN o set_zero_wasted_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def set_zero_wasted_stats_alt_def
  by sepref

sepref_def heuristic_reluctant_tick_stats_impl
  is \<open>RETURN o heuristic_reluctant_tick_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_tick_stats_def
  by sepref

sepref_def heuristic_reluctant_enable_stats_impl
  is \<open>RETURN o heuristic_reluctant_enable_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_enable_stats_def
  by sepref

sepref_def heuristic_reluctant_disable_stats_impl
  is \<open>RETURN o heuristic_reluctant_disable_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_disable_stats_def
  by sepref

sepref_def heuristic_reluctant_triggered_stats_impl
  is \<open>RETURN o heuristic_reluctant_triggered_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn \<times>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered_stats_def heuristic_int_assn_def
  by sepref

sepref_def heuristic_reluctant_triggered2_stats_impl
  is \<open>RETURN o heuristic_reluctant_triggered2_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered2_stats_def heuristic_int_assn_def
  by sepref


sepref_def heuristic_reluctant_untrigger_stats_impl
  is \<open>RETURN o heuristic_reluctant_untrigger_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_untrigger_stats_def
  by sepref


sepref_def end_of_rephasing_phase_impl [llvm_inline]
  is \<open>RETURN o end_of_rephasing_phase\<close>
  :: \<open>phase_heur_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding end_of_rephasing_phase_def phase_heur_assn_def
  by sepref

sepref_def end_of_rephasing_phase_heur_stats_impl
  is \<open>RETURN o end_of_rephasing_phase_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding heuristic_int_assn_def end_of_rephasing_phase_heur_stats_def
  by sepref

sepref_def is_fully_propagated_heur_stats_impl
  is \<open>RETURN o is_fully_propagated_heur_stats\<close>
  ::  \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_int_assn_def is_fully_propagated_heur_stats_def
  by sepref

sepref_def set_fully_propagated_heur_stats_impl
  is \<open>RETURN o set_fully_propagated_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def set_fully_propagated_heur_stats_def
  by sepref

sepref_def unset_fully_propagated_heur_stats_impl
  is \<open>RETURN o unset_fully_propagated_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def unset_fully_propagated_heur_stats_def
  by sepref

sepref_def restart_info_restart_done_heur_stats_impl
  is \<open>RETURN o restart_info_restart_done_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def restart_info_restart_done_heur_stats_def
  by sepref

sepref_def set_zero_wasted_impl
  is \<open>RETURN o set_zero_wasted_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def set_zero_wasted_stats_alt_def
  by sepref

lemma wasted_of_stats_alt_def:
  \<open>RETURN o wasted_of_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN wasted)\<close>
  by auto

sepref_def wasted_of_stats_impl
  is \<open>RETURN o wasted_of_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding heuristic_int_assn_def wasted_of_stats_alt_def
  by sepref

lemma slow_ema_of_stats_alt_def:
  \<open>RETURN o slow_ema_of_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN slow_ema)\<close> and
  fast_ema_of_stats_alt_def:
  \<open>RETURN o fast_ema_of_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN fast_ema)\<close>
  by auto

sepref_def slow_ema_of_stats_impl
  is \<open>RETURN o slow_ema_of_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding heuristic_int_assn_def slow_ema_of_stats_alt_def
  by sepref

sepref_def fast_ema_of_stats_impl
  is \<open>RETURN o fast_ema_of_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding heuristic_int_assn_def fast_ema_of_stats_alt_def
  by sepref

lemma current_restart_phase_stats_alt_def:
  \<open>RETURN o current_restart_phase_stats =
  (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>). RETURN restart_phase)\<close>
  by auto

sepref_def current_restart_phase_impl
  is \<open>RETURN o current_restart_phase_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding heuristic_int_assn_def current_restart_phase_stats_alt_def
  by sepref

lemma incr_wasted_stats_stats_alt_def:
  \<open>RETURN oo incr_wasted_stats =
  (\<lambda>waste (fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN (fast_ema, slow_ema, res_info, wasted + waste, \<phi>))\<close>
  by (auto intro!: ext)

sepref_def incr_wasted_stats_impl
  is \<open>uncurry (RETURN oo incr_wasted_stats)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def incr_wasted_stats_stats_alt_def
  by sepref

sepref_def current_rephasing_phase_stats_impl
  is \<open>RETURN o current_rephasing_phase_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding heuristic_int_assn_def current_rephasing_phase_stats_def
    phase_current_rephasing_phase_def phase_heur_assn_def
  by sepref

sepref_def get_next_phase_heur_stats_impl
  is \<open>uncurry2 get_next_phase_heur_stats\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_next_phase_heur_stats_def heuristic_int_assn_def
  by sepref

lemma get_conflict_count_since_last_restart_stats_alt_def:
  \<open>get_conflict_count_since_last_restart_stats =
  (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>). ccount)\<close>
  by auto

sepref_def get_conflict_count_since_last_restart_stats_impl
  is \<open>RETURN o get_conflict_count_since_last_restart_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_conflict_count_since_last_restart_stats_alt_def heuristic_int_assn_def
  by sepref

lemma next_pure_lits_schedule_info_stats_alt_def:
  \<open>next_pure_lits_schedule_info_stats =
  (\<lambda>(fast_ema, slow_ema, _, wasted, \<phi>, _,_,lits, (inprocess_schedule, _)). inprocess_schedule)\<close>
  unfolding next_pure_lits_schedule_info_stats_def next_pure_lits_schedule_info_def
  by auto

sepref_def next_pure_lits_schedule_info_stats_impl
  is \<open>RETURN o next_pure_lits_schedule_info_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding next_pure_lits_schedule_info_stats_alt_def heuristic_int_assn_def
  by sepref

sepref_def schedule_next_pure_lits_stats_impl
  is \<open>RETURN o schedule_next_pure_lits_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding schedule_next_pure_lits_stats_def heuristic_int_assn_def
  by sepref


lemma next_reduce_schedule_info_stats_alt_def:
  \<open>next_reduce_schedule_info_stats =
  (\<lambda>(fast_ema, slow_ema, _, wasted, \<phi>, _,_,lits, (inprocess_schedule, reduce_schedule, _)). reduce_schedule)\<close>
  unfolding next_reduce_schedule_info_stats_def next_reduce_schedule_info_def
  by (auto intro!: ext)

sepref_def next_reduce_schedule_info_stats_impl
  is \<open>RETURN o next_reduce_schedule_info_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding next_reduce_schedule_info_stats_alt_def heuristic_int_assn_def
  by sepref

sepref_def schedule_next_reduce_stats_impl
  is \<open>uncurry (RETURN oo schedule_next_reduce_stats)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding schedule_next_reduce_stats_def heuristic_int_assn_def
  by sepref


lemma next_subsume_schedule_info_stats_alt_def:
  \<open>next_subsume_schedule_info_stats =
  (\<lambda>(fast_ema, slow_ema, _, wasted, \<phi>, _,_,lits, (inprocess_schedule, reduce_schedule, subsume_schedule)). subsume_schedule)\<close>
  unfolding next_subsume_schedule_info_stats_def next_subsume_schedule_info_def
  by (auto intro!: ext)

sepref_def next_subsume_schedule_info_stats_impl
  is \<open>RETURN o next_subsume_schedule_info_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding next_subsume_schedule_info_stats_alt_def heuristic_int_assn_def
  by sepref

sepref_def schedule_next_subsume_stats_impl
  is \<open>uncurry (RETURN oo schedule_next_subsume_stats)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding schedule_next_subsume_stats_def heuristic_int_assn_def
  by sepref

lemma hn_id_pure:
  \<open>CONSTRAINT is_pure A \<Longrightarrow> (Mreturn, RETURN o id) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: ENTAILS_def is_pure_conv pure_def)
  by (smt (z3) entails_def entails_lift_extract_simps(1) pure_true_conv sep_conj_empty')

lemmas heur_refine[sepref_fr_rules] =
  set_zero_wasted_stats_impl.refine[FCOMP set_zero_wasted_stats_set_zero_wasted_stats]
  heuristic_reluctant_tick_stats_impl.refine[FCOMP heuristic_reluctant_tick_stats_heuristic_reluctant_tick]
  heuristic_reluctant_enable_stats_impl.refine[FCOMP heuristic_reluctant_enable_stats_heuristic_reluctant_enable]
  heuristic_reluctant_disable_stats_impl.refine[FCOMP heuristic_reluctant_disable_stats_heuristic_reluctant_disable]
  heuristic_reluctant_triggered_stats_impl.refine[FCOMP heuristic_reluctant_triggered_stats_heuristic_reluctant_triggered]
  heuristic_reluctant_triggered2_stats_impl.refine[FCOMP heuristic_reluctant_triggered2_stats_heuristic_reluctant_triggered2]
  heuristic_reluctant_untrigger_stats_impl.refine[FCOMP heuristic_reluctant_untrigger_stats_heuristic_reluctant_untrigger]
  end_of_rephasing_phase_heur_stats_impl.refine[FCOMP end_of_rephasing_phase_heur_stats_end_of_rephasing_phase_heur]
  is_fully_propagated_heur_stats_impl.refine[FCOMP is_fully_propagated_heur_stats_is_fully_propagated_heur]
  set_fully_propagated_heur_stats_impl.refine[FCOMP set_fully_propagated_heur_stats_set_fully_propagated_heur]
  unset_fully_propagated_heur_stats_impl.refine[FCOMP unset_fully_propagated_heur_stats_unset_fully_propagated_heur]
  restart_info_restart_done_heur_stats_impl.refine[FCOMP restart_info_restart_done_heur_stats_restart_info_restart_done_heur]
  set_zero_wasted_impl.refine[FCOMP set_zero_wasted_stats_set_zero_wasted]
  wasted_of_stats_impl.refine[FCOMP wasted_of_stats_wasted_of]
  current_restart_phase_impl.refine[FCOMP current_restart_phase_stats_current_restart_phase]
  slow_ema_of_stats_impl.refine[FCOMP slow_ema_of_stats_slow_ema_of]
  fast_ema_of_stats_impl.refine[FCOMP fast_ema_of_stats_fast_ema_of]
  incr_wasted_stats_impl.refine[FCOMP incr_wasted_stats_incr_wasted]
  current_rephasing_phase_stats_impl.refine[FCOMP current_rephasing_phase_stats_current_rephasing_phase]
  get_next_phase_heur_stats_impl.refine[FCOMP get_next_phase_heur_stats_get_next_phase_heur]
  get_conflict_count_since_last_restart_stats_impl.refine[FCOMP get_conflict_count_since_last_restart_stats_get_conflict_count_since_last_restart_stats]
  schedule_next_pure_lits_stats_impl.refine[FCOMP schedule_next_pure_lits_stats_schedule_next_pure_lits]
  next_pure_lits_schedule_info_stats_impl.refine[FCOMP next_pure_lits_schedule_next_pure_lits_schedule_stats]
  schedule_next_reduce_stats_impl.refine[FCOMP schedule_next_reduce_stats_schedule_next_reduce]
  next_reduce_schedule_info_stats_impl.refine[FCOMP next_reduce_schedule_next_reduce_schedule_stats]
  schedule_next_subsume_stats_impl.refine[FCOMP schedule_next_subsume_stats_schedule_next_subsume]
  next_subsume_schedule_info_stats_impl.refine[FCOMP next_subsume_schedule_next_subsume_schedule_stats]
  hn_id[of heuristic_int_assn, FCOMP get_content_hnr[of heur_int_rel]]
  hn_id[of heuristic_int_assn, FCOMP Constructor_hnr[of heur_int_rel]]

lemmas get_restart_heuristics_pure_rule =
  hn_id_pure[of heuristic_int_assn, FCOMP get_content_hnr[of heur_int_rel]]

end


sepref_register set_zero_wasted_stats save_phase_heur_stats heuristic_reluctant_tick_stats
  heuristic_reluctant_tick is_fully_propagated_heur_stats get_content next_pure_lits_schedule_info_stats
  schedule_next_pure_lits_stats

lemma mop_save_phase_heur_stats_alt_def:
  \<open>mop_save_phase_heur_stats = (\<lambda> L b (fast_ema, slow_ema, res_info, wasted, (\<phi>, target, best), rel). do {
    ASSERT(L < length \<phi>);
    RETURN (fast_ema, slow_ema, res_info, wasted, (\<phi>[L := b], target,
                 best), rel)})\<close>
  unfolding mop_save_phase_heur_stats_def save_phase_heur_def save_phase_heur_pre_stats_def save_phase_heur_stats_def
  by (auto intro!: ext)

sepref_def mop_save_phase_heur_stats_impl
  is \<open>uncurry2 (mop_save_phase_heur_stats)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_stats_alt_def save_phase_heur_stats_def save_phase_heur_pre_stats_def
    phase_heur_assn_def mop_save_phase_heur_def heuristic_int_assn_def
  apply annot_all_atm_idxs
  by sepref

lemma mop_save_phase_heur_alt_def:
  \<open>mop_save_phase_heur L b S = do {
  let S = get_restart_heuristics S;
  S \<leftarrow> mop_save_phase_heur_stats L b S;
  RETURN (Restart_Heuristics S)
    }\<close>
    unfolding Let_def mop_save_phase_heur_def mop_save_phase_heur_def save_phase_heur_def
      mop_save_phase_heur_stats_def save_phase_heur_pre_def
  by auto

sepref_def mop_save_phase_heur_impl
  is \<open>uncurry2 (mop_save_phase_heur)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_alt_def save_phase_heur_def save_phase_heur_pre_def
    phase_heur_assn_def mop_save_phase_heur_def
  apply annot_all_atm_idxs
  by sepref

schematic_goal mk_free_heuristic_int_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_int_assn ?fr\<close>
  unfolding heuristic_int_assn_def code_hider_assn_def
  by synthesize_free

schematic_goal mk_free_heuristic_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_assn ?fr\<close>
  unfolding heuristic_assn_def code_hider_assn_def
  by synthesize_free

lemma [safe_constraint_rules]: \<open>CONSTRAINT is_pure A \<Longrightarrow> CONSTRAINT is_pure (code_hider_assn A B)\<close>
  unfolding code_hider_assn_def by (auto simp: hr_comp_is_pure)


lemma clss_size_incr_lcount_alt_def:
  \<open>RETURN o clss_size_incr_lcount =
  (\<lambda>(lcount,  lcountUE, lcountUS). RETURN (lcount + 1, lcountUE, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcount_def)

lemma clss_size_lcountUEk_alt_def:
  \<open>RETURN o clss_size_lcountUEk = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). RETURN lcountUEk)\<close>
  by (auto simp: clss_size_lcountUEk_def)

sepref_def clss_size_lcountUEk_fast_code
  is \<open>RETURN o clss_size_lcountUEk\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUEk_alt_def clss_size_lcount_def
  by sepref

sepref_register clss_size_incr_lcount
sepref_def clss_size_incr_lcount_fast_code
  is \<open>RETURN o clss_size_incr_lcount\<close>
  :: \<open>[\<lambda>S. clss_size_lcount S \<le> max_snat 64]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcount_alt_def lcount_assn_def clss_size_lcount_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_def end_of_restart_phase_impl
  is \<open>RETURN o end_of_restart_phase_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_restart_phase_stats_def heuristic_int_assn_def
  by sepref

lemma end_of_restart_phase_stats_end_of_restart_phase:
  \<open>(end_of_restart_phase_stats, end_of_restart_phase) \<in> heur_rel \<rightarrow> word_rel\<close>
  by (auto simp: end_of_restart_phase_def code_hider_rel_def)

lemmas end_of_restart_phase_impl_refine[sepref_fr_rules] =
  end_of_restart_phase_impl.refine[FCOMP end_of_restart_phase_stats_end_of_restart_phase,
    unfolded heuristic_assn_alt_def[symmetric]]

lemma incr_restart_phase_end_stats_alt_def:
  \<open>incr_restart_phase_end_stats = (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, length_phase), wasted).
  (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase + length_phase, (length_phase * 3) >> 1), wasted))\<close>
  by auto

sepref_def incr_restart_phase_end_stats_impl [llvm_inline]
  is \<open>RETURN o incr_restart_phase_end_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply[[goals_limit=1]]
  unfolding heuristic_int_assn_def incr_restart_phase_end_stats_alt_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def incr_restart_phase_end_impl
  is \<open>RETURN o incr_restart_phase_end\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply[[goals_limit=1]]
  unfolding incr_restart_phase_end_def
  by sepref

lemma incr_restart_phase_stats_alt_def:
  \<open>incr_restart_phase_stats =
  (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>).
  (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase XOR 1, end_of_phase), wasted, \<phi>))\<close>
  by (auto)

sepref_def incr_restart_phase_stats_impl
  is \<open>RETURN o incr_restart_phase_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def incr_restart_phase_stats_alt_def
  by sepref

sepref_def incr_restart_phase_impl
  is \<open>RETURN o incr_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding incr_restart_phase_def
  by sepref

sepref_def reset_added_heur_stats2_impl
  is reset_added_heur_stats2
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding reset_added_heur_stats2_def heuristic_int_assn_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref



lemma reset_added_heur_stats2_reset_added_heur_stats:
  \<open>(reset_added_heur_stats2, RETURN o (reset_added_heur_stats)) \<in> heur_int_rel \<rightarrow> \<langle>heur_int_rel\<rangle>nres_rel\<close>
  unfolding fref_param1
  apply (intro frefI fref_param1 nres_relI)
  apply (subst comp_def)
  apply (rule reset_added_heur_stats2_reset_added_heur_stats[THEN order_trans])
  by simp

lemmas reset_added_heur_stats_impl_refine[sepref_fr_rules] =
  reset_added_heur_stats2_impl.refine[FCOMP reset_added_heur_stats2_reset_added_heur_stats]

sepref_register reset_added_heur mop_reset_added_heur is_marked_added_heur

sepref_def is_marked_added_heur_stats_impl
  is \<open>uncurry (mop_is_marked_added_heur_stats)\<close>
  :: \<open>heuristic_int_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k  \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[eta_contract=false]]
  unfolding is_marked_added_heur_stats_def is_marked_added_heur_pre_stats_def
    heuristic_int_assn_def mop_is_marked_added_heur_stats_def case_prod_app
  apply (rewrite at \<open>_ ! _\<close> annot_index_of_atm)
  by sepref

lemma mop_mark_added_heur_stats_alt_def:
\<open>mop_mark_added_heur_stats L b =(\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st). do {
   ASSERT(mark_added_heur_pre_stats L b (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st));
   RETURN (mark_added_heur_stats L b (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st))
  })\<close>
  by (auto simp: mop_mark_added_heur_stats_def)

sepref_def mop_mark_added_heur_stats_impl
  is \<open>uncurry2 mop_mark_added_heur_stats\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def mop_mark_added_heur_stats_alt_def
    mark_added_heur_stats_def prod.simps mark_added_heur_pre_stats_def
  apply (rewrite at \<open>_[_ := _]\<close> annot_index_of_atm)
  by sepref

lemma mop_is_marked_added_heur_stats_alt_def:
\<open>mop_is_marked_added_heur_stats =(\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule) L. do {
   ASSERT(is_marked_added_heur_pre_stats (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule) L);
   RETURN (is_marked_added_heur_stats (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule) L)
  })\<close>
  by (auto simp: mop_is_marked_added_heur_stats_def intro!: ext)

sepref_def mop_is_marked_added_heur_stats_impl
  is \<open>uncurry mop_is_marked_added_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_int_assn_def mop_is_marked_added_heur_stats_alt_def
    is_marked_added_heur_stats_def prod.simps is_marked_added_heur_pre_stats_def
  apply (rewrite at \<open>_ ! _\<close> annot_index_of_atm)
  by sepref


context
  notes [fcomp_norm_unfold] = heuristic_assn_def[symmetric] heuristic_assn_alt_def[symmetric]
begin

lemma reset_added_heur_stats_reset_added_heur:
  \<open>(reset_added_heur_stats, reset_added_heur) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  is_marked_added_heur_stats_is_marked_added_heur:
  \<open>(is_marked_added_heur_stats, is_marked_added_heur) \<in> heur_rel \<rightarrow> nat_rel \<rightarrow> bool_rel\<close>
  by (auto simp: reset_added_heur_def code_hider_rel_def is_marked_added_heur_def
    mop_is_marked_added_heur_stats_def)

lemmas reset_added_heur_refine[sepref_fr_rules] =
  reset_added_heur_stats_impl_refine[FCOMP reset_added_heur_stats_reset_added_heur]

lemma mop_is_marked_added_heur_stats_is_marked_added_heur:
  \<open>(uncurry mop_is_marked_added_heur_stats, uncurry (RETURN oo is_marked_added_heur)) \<in>
  [\<lambda>(S, l). is_marked_added_heur_pre_stats (get_restart_heuristics S) l]\<^sub>f
  heur_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close> and
  mop_mark_added_heur_stats_mop_mark_added_heur:
  \<open>(uncurry2 mop_mark_added_heur_stats, uncurry2 (RETURN ooo mark_added_heur)) \<in>
  [\<lambda>((l,b), S). mark_added_heur_pre l b S]\<^sub>f
  nat_rel \<times>\<^sub>fbool_rel \<times>\<^sub>f heur_rel \<rightarrow> \<langle>heur_rel\<rangle>nres_rel\<close> and
  mop_is_marked_added_heur_stats_mop_is_marked_added_heur:
  \<open>(uncurry mop_is_marked_added_heur_stats, uncurry (RETURN oo is_marked_added_heur)) \<in>
  [\<lambda>(l, S). is_marked_added_heur_pre l S]\<^sub>f
   heur_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI
    simp: reset_added_heur_def code_hider_rel_def is_marked_added_heur_def
    mop_mark_added_heur_stats_def mop_is_marked_added_heur_stats_def
    mop_is_marked_added_heur_stats_def is_marked_added_heur_pre_def
    mark_added_heur_pre_def
    mop_mark_added_heur_stats_def mark_added_heur_def)

lemmas is_marked_added_heur_stats_impl_refine[refine] =
  is_marked_added_heur_stats_impl.refine[FCOMP mop_is_marked_added_heur_stats_is_marked_added_heur]

lemmas mark_added_heur_impl_refine[refine] =
  mop_mark_added_heur_stats_impl.refine[FCOMP mop_mark_added_heur_stats_mop_mark_added_heur]

lemmas is_marked_added_heur_refine[refine] =
  mop_is_marked_added_heur_stats_impl.refine[FCOMP mop_is_marked_added_heur_stats_mop_is_marked_added_heur]
end


sepref_def mop_reset_added_heur_impl
  is \<open>mop_reset_added_heur\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding mop_reset_added_heur_def
  by sepref

end