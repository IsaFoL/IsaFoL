theory IsaSAT_Trail
imports Watched_Literals_Watch_List_Code_Common
begin

(* TODO Move *)
definition nat_of_uint32_conv :: \<open>nat \<Rightarrow> nat\<close> where
\<open>nat_of_uint32_conv = id\<close>

lemma nat_of_uint32_conv_hnr[sepref_fr_rules]:
  \<open>(return o nat_of_uint32, RETURN o nat_of_uint32_conv) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_conv_def)

definition option_nat_of_uint32_conv :: \<open>nat option \<Rightarrow> nat option\<close> where
\<open>option_nat_of_uint32_conv = id\<close>

definition option_nat_of_uint32 :: \<open>uint32 option \<Rightarrow> nat option\<close> where
\<open>option_nat_of_uint32 = map_option nat_of_uint32\<close>

lemma option_nat_of_uint32_conv_hnr[sepref_fr_rules]:
  \<open>(return o option_nat_of_uint32, RETURN o option_nat_of_uint32_conv) \<in>
    (option_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def
     option_nat_of_uint32_conv_def option_assn_alt_def option_nat_of_uint32_def
    split: option.splits)

lemma option_nat_of_uint32[sepref_fr_rules]:
  \<open>(return o option_nat_of_uint32, RETURN o option_nat_of_uint32) \<in>
    (option_assn uint32_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def
     option_nat_of_uint32_conv_def option_assn_alt_def option_nat_of_uint32_def
    split: option.splits)

definition op_map :: "('b \<Rightarrow> 'a::default) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list nres" where
  \<open>op_map R e xs = do {
    let zs = replicate (length xs) e;
    (_, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i,zs). i \<le> length xs \<and> take i zs = map R (take i xs) \<and>
        length zs = length xs \<and> (\<forall>k\<ge>i. k < length xs \<longrightarrow> zs ! k = e)\<^esup>
      (\<lambda>(i, zs). i < length zs)
      (\<lambda>(i, zs). do {ASSERT(i < length zs); RETURN (i+1, zs[i := R (xs!i)])})
      (0, zs);
    RETURN zs
     }\<close>

lemma fucck_it: \<open>(\<forall>k\<ge>i. P k) \<Longrightarrow> k\<ge>i \<Longrightarrow> P k\<close>
  by auto

lemma op_map_map: \<open>op_map R e xs \<le> RETURN (map R xs)\<close>
  unfolding op_map_def Let_def
  by (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(i,_). length xs - i)\<close>])
    (auto simp: hd_conv_nth take_Suc_conv_app_nth list_update_append split: nat.splits)

lemma op_map_map_rel:
  \<open>(op_map R e, RETURN o (map R)) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: op_map_map)

definition array_option_nat_of_uint32_conv :: \<open>nat option list \<Rightarrow> nat option list\<close> where
\<open>array_option_nat_of_uint32_conv = id\<close>

definition array_option_nat_of_uint32 :: "nat option list \<Rightarrow> nat option list nres" where
\<open>array_option_nat_of_uint32 xs = op_map option_nat_of_uint32_conv None xs\<close>

sepref_definition array_option_nat_of_uint32_code
  is array_option_nat_of_uint32
  :: \<open>(array_assn (option_assn uint32_nat_assn))\<^sup>k \<rightarrow>\<^sub>a array_assn (option_assn nat_assn)\<close>
  unfolding op_map_def array_option_nat_of_uint32_def array_fold_custom_replicate
  apply (rewrite at \<open>do {let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>array_assn (option_assn nat_assn)\<close>])
  by sepref

lemma array_option_nat_of_uint32_conv_alt_def:
  \<open>array_option_nat_of_uint32_conv = map option_nat_of_uint32_conv\<close>
  unfolding option_nat_of_uint32_conv_def array_option_nat_of_uint32_conv_def by auto

lemma array_option_nat_of_uint32_conv_hnr[sepref_fr_rules]:
  \<open>(array_option_nat_of_uint32_code, (RETURN \<circ> array_option_nat_of_uint32_conv))
    \<in> (array_assn (option_assn uint32_nat_assn))\<^sup>k \<rightarrow>\<^sub>a array_assn (option_assn nat_assn)\<close>
  using array_option_nat_of_uint32_code.refine[unfolded array_option_nat_of_uint32_def,
    FCOMP op_map_map_rel] unfolding array_option_nat_of_uint32_conv_alt_def
  by simp
(* End Move *)

type_synonym tri_bool = \<open>bool option\<close>
type_synonym tri_bool_assn = \<open>uint32\<close>

text \<open>
  We define set/non set not as the trivial \<^term>\<open>None\<close>, \<^term>\<open>Some True\<close>, and
  \<^term>\<open>Some False\<close>, because it is not clear whether the compiler can represent the values
  without pointers. Therefore, we use \<^typ>\<open>uint32\<close>.
\<close>
definition UNSET_code :: \<open>tri_bool_assn\<close> where
  [simp]: \<open>UNSET_code = 0\<close>

definition SET_TRUE_code :: \<open>tri_bool_assn\<close> where
  [simp]: \<open>SET_TRUE_code = 2\<close>

definition SET_FALSE_code :: \<open>tri_bool_assn\<close> where
  [simp]: \<open>SET_FALSE_code = 3\<close>

definition UNSET :: \<open>tri_bool\<close> where
  [simp]: \<open>UNSET = None\<close>

definition SET_FALSE :: \<open>tri_bool\<close> where
  [simp]: \<open>SET_FALSE = Some False\<close>

definition SET_TRUE :: \<open>tri_bool\<close> where
  [simp]: \<open>SET_TRUE = Some True\<close>

definition tri_bool_ref :: \<open>(tri_bool_assn \<times> tri_bool) set\<close> where
  \<open>tri_bool_ref = {(SET_TRUE_code, SET_TRUE), (UNSET_code, UNSET), (SET_FALSE_code, SET_FALSE)}\<close>

definition tri_bool_assn :: \<open>tri_bool \<Rightarrow> tri_bool_assn \<Rightarrow> assn\<close> where
  \<open>tri_bool_assn = hr_comp uint32_assn tri_bool_ref\<close>

lemma UNSET_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return UNSET_code), uncurry0 (RETURN UNSET)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: tri_bool_assn_def tri_bool_ref_def pure_def hr_comp_def)

lemma equality_tri_bool_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry(RETURN oo (op =))) \<in>
      tri_bool_assn\<^sup>k *\<^sub>a tri_bool_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  using nat_of_uint32_012 nat_of_uint32_3
  by (sep_auto simp: tri_bool_assn_def tri_bool_ref_def pure_def hr_comp_def)+


definition (in -) tri_bool_eq :: \<open>tri_bool \<Rightarrow> tri_bool \<Rightarrow> bool\<close> where
  \<open>tri_bool_eq = (op =)\<close>

lemma equality_tri_bool_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry(RETURN oo (tri_bool_eq))) \<in>
      tri_bool_assn\<^sup>k *\<^sub>a tri_bool_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  using nat_of_uint32_012 nat_of_uint32_3 unfolding tri_bool_eq_def
  by (sep_auto simp: tri_bool_assn_def tri_bool_ref_def pure_def hr_comp_def)+


lemma SET_TRUE_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return SET_TRUE_code), uncurry0 (RETURN SET_TRUE)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: tri_bool_assn_def tri_bool_ref_def pure_def hr_comp_def)

lemma SET_FALSE_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return SET_FALSE_code), uncurry0 (RETURN SET_FALSE)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  using nat_of_uint32_012 nat_of_uint32_3
  by sepref_to_hoare (sep_auto simp: tri_bool_assn_def tri_bool_ref_def pure_def hr_comp_def)+

lemma [safe_constraint_rules]:
  \<open>is_pure tri_bool_assn\<close>
  unfolding tri_bool_assn_def
  by auto

type_synonym trail_pol =
   \<open>nat literal list \<times> tri_bool list \<times> nat list \<times> nat option list \<times> nat\<close>

type_synonym trail_pol_assn =
   \<open>uint32 list \<times> tri_bool_assn array \<times> uint32 array \<times> nat option array \<times> uint32\<close>

type_synonym trail_pol_fast_assn =
   \<open>uint32 list \<times> tri_bool_assn array \<times> uint32 array \<times> uint32 option array \<times> uint32\<close>

definition get_level_atm where
  \<open>get_level_atm M L = get_level M (Pos L)\<close>

definition polarity_atm where
  \<open>polarity_atm M L =
    (if Pos L \<in> lits_of_l M then Some True
    else if Neg L \<in> lits_of_l M then Some False
    else None)\<close>

definition defined_atm :: \<open>('v, nat) ann_lits \<Rightarrow> 'v \<Rightarrow> bool\<close> where
\<open>defined_atm M L = defined_lit M (Pos L)\<close>

abbreviation undefined_atm where
  \<open>undefined_atm M L \<equiv> \<not>defined_atm M L\<close>

context isasat_input_ops
begin

definition ann_lits_split_reasons where
  \<open>ann_lits_split_reasons = {((M, reasons), M'). M = map lit_of M' \<and>
    (\<forall>L \<in> set M'. is_proped L \<longrightarrow> reasons ! (atm_of (lit_of L)) = Some (mark_of L)) \<and>
    (\<forall>L \<in> set M'. is_decided L \<longrightarrow> reasons ! (atm_of (lit_of L)) = None) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length reasons)
  }\<close>

definition trail_pol :: \<open>(trail_pol \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trail_pol = {((M', xs, lvls, reasons, k), M). ((M', reasons), M) \<in> ann_lits_split_reasons \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)}\<close>

end

abbreviation trail_pol_assn :: \<open>trail_pol \<Rightarrow> trail_pol_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_assn \<equiv>
      list_assn unat_lit_assn *a array_assn (tri_bool_assn) *a
      array_assn uint32_nat_assn *a
      array_assn (option_assn nat_assn) *a uint32_nat_assn\<close>


abbreviation trail_pol_fast_assn :: \<open>trail_pol \<Rightarrow> trail_pol_fast_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_fast_assn \<equiv>
      list_assn unat_lit_assn *a array_assn (tri_bool_assn) *a
      array_assn uint32_nat_assn *a
      array_assn (option_assn uint32_nat_assn) *a uint32_nat_assn\<close>

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>

definition trail_fast_of_slow :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_fast_of_slow = id\<close>

definition trail_pol_fast_of_slow :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>trail_pol_fast_of_slow =
    (\<lambda>(M, val, lvls, reason, k). (M, val, lvls, array_option_nat_of_uint32_conv reason, k))\<close>

sepref_definition trail_pol_slow_of_fast_code
  is \<open>RETURN o trail_pol_fast_of_slow\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d \<rightarrow>\<^sub>a trail_pol_assn\<close>
  unfolding trail_pol_fast_of_slow_def
  by sepref

context isasat_input_ops
begin

abbreviation trail_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> trail_pol_assn \<Rightarrow> assn\<close> where
  \<open>trail_assn \<equiv> hr_comp trail_pol_assn trail_pol\<close>

abbreviation trail_fast_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> trail_pol_fast_assn \<Rightarrow> assn\<close> where
  \<open>trail_fast_assn \<equiv> hr_comp trail_pol_fast_assn trail_pol\<close>

lemma trail_pol_fast_of_slow_trail_fast_of_slow:
  \<open>(RETURN o trail_pol_fast_of_slow, RETURN o trail_fast_of_slow)
    \<in> trail_pol \<rightarrow>\<^sub>f \<langle>trail_pol\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: trail_pol_def trail_pol_fast_of_slow_def array_option_nat_of_uint32_conv_def
    trail_fast_of_slow_def)

lemma trail_fast_of_slow_hnr[sepref_fr_rules]:
  \<open>(trail_pol_slow_of_fast_code, RETURN \<circ> trail_fast_of_slow) \<in> trail_fast_assn\<^sup>d \<rightarrow>\<^sub>a trail_assn\<close>
  using trail_pol_slow_of_fast_code.refine[FCOMP trail_pol_fast_of_slow_trail_fast_of_slow]
  .

end

definition counts_maximum_level where
  \<open>counts_maximum_level M C = {i. C \<noteq> None \<longrightarrow> i = card_max_lvl M (the C)}\<close>

lemma counts_maximum_level_None[simp]: \<open>counts_maximum_level M None = Collect (\<lambda>_. True)\<close>
  by (auto simp: counts_maximum_level_def)


context isasat_input_bounded
begin

definition get_level_atm_pol :: \<open>trail_pol \<Rightarrow> uint32 \<Rightarrow> nat\<close> where
  \<open>get_level_atm_pol = (\<lambda>(M, xs, lvls, k) L. lvls ! (nat_of_uint32 L))\<close>

sepref_thm get_level_atm_code
  is \<open>uncurry (RETURN oo get_level_atm_pol)\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), L). nat_of_uint32 L < length lvls]\<^sub>a
  trail_pol_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_atm_pol_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_level_atm_code
   uses isasat_input_bounded.get_level_atm_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_atm_code_def

lemmas get_level_atm_code_hnr[sepref_fr_rules] =
   get_level_atm_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm get_level_atm_fast_code
  is \<open>uncurry (RETURN oo get_level_atm_pol)\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), L). nat_of_uint32 L < length lvls]\<^sub>a
  trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_atm_pol_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_level_atm_fast_code
   uses isasat_input_bounded.get_level_atm_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_atm_fast_code_def

lemmas get_level_atm_fast_code_hnr[sepref_fr_rules] =
   get_level_atm_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma
  get_level_atm_hnr[sepref_fr_rules]:
    \<open>(uncurry get_level_atm_code, uncurry (RETURN oo get_level_atm)) \<in>
     [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close> 
  (is ?Slow is \<open>_ \<in> [?pre]\<^sub>a ?imslow \<rightarrow> ?f\<close>) and
  get_level_atm_fast_hnr[sepref_fr_rules]:
    \<open>(uncurry get_level_atm_fast_code, uncurry (RETURN oo get_level_atm)) \<in>
   [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
    (is ?Fast is \<open>_ \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?f\<close>)
proof -
  have [simp]: \<open>(ba, bb) \<in> nat_lit_rel \<Longrightarrow> ba div 2 = atm_of bb\<close> for ba bb
    by (auto simp: p2rel_def lit_of_natP_def atm_of_lit_of_nat nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 1: \<open>(uncurry (RETURN oo get_level_atm_pol), uncurry (RETURN oo get_level_atm)) \<in>
     [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>f trail_pol \<times>\<^sub>f uint32_nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI, rename_tac x y, case_tac x)
      (auto 5 5 simp: image_image trail_pol_def get_level_atm_pol_def get_level_atm_def
        nat_shiftr_div2 shiftr1_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
        nat_of_uint32_shiftr get_level_def)

  have H: \<open>(uncurry get_level_atm_code, uncurry (RETURN \<circ>\<circ> get_level_atm))
  \<in> [comp_PRE (trail_pol \<times>\<^sub>f uint32_nat_rel)
       (\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0)
       (\<lambda>_ ((M, xs, lvls, k), L). nat_of_uint32 L < length lvls)
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k)
                      (trail_pol \<times>\<^sub>f
                       uint32_nat_rel) \<rightarrow> hr_comp uint32_nat_assn
          nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF get_level_atm_code.refine 1, OF isasat_input_bounded_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto 5 5 simp: comp_PRE_def trail_pol_def unat_lit_rel_def nat_lit_rel_def
        uint32_nat_rel_def br_def intro!: ext)
  have im: \<open>?im' = ?imslow\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?Slow
    using H unfolding im pre f by simp

  have H: \<open>(uncurry get_level_atm_fast_code, uncurry (RETURN \<circ>\<circ> get_level_atm))
  \<in> [comp_PRE (trail_pol \<times>\<^sub>f uint32_nat_rel)
       (\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0)
       (\<lambda>_ ((M, xs, lvls, k), L). nat_of_uint32 L < length lvls)
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k)
                      (trail_pol \<times>\<^sub>f uint32_nat_rel) \<rightarrow> hr_comp uint32_nat_assn
          nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF get_level_atm_fast_code.refine 1, OF isasat_input_bounded_axioms] .    
  
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?Fast
    using H unfolding im pre f by simp
qed

lemma (in -) get_level_get_level_atm: \<open>get_level M L = get_level_atm M (atm_of L)\<close>
  unfolding get_level_atm_def
  by (cases L) (auto simp: get_level_Neg_Pos)

sepref_thm get_level_code
  is \<open>uncurry (RETURN oo get_level)\<close>
  :: \<open>[\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_get_level_atm nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric]
  supply [[goals_limit = 1]] image_image[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
  by sepref

concrete_definition (in -) get_level_code
   uses isasat_input_bounded.get_level_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_code_def

lemmas get_level_code_get_level_code[sepref_fr_rules] =
   get_level_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


sepref_thm get_level_fast_code
  is \<open>uncurry (RETURN oo get_level)\<close>
  :: \<open>[\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a
      trail_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_get_level_atm nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric]
  supply [[goals_limit = 1]] image_image[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
  by sepref

concrete_definition (in -) get_level_fast_code
   uses isasat_input_bounded.get_level_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_fast_code_def

lemmas get_level_fast_code_get_level_code[sepref_fr_rules] =
   get_level_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

definition (in -) count_decided_pol where
  \<open>count_decided_pol = (\<lambda>(_, _, _, _, k). k)\<close>

lemma count_decided_trail_ref:
  \<open>(RETURN o count_decided_pol, RETURN o count_decided) \<in> trail_pol \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: trail_pol_def count_decided_pol_def)

lemma count_decided_trail:
   \<open>(return o count_decided_pol, RETURN o count_decided_pol) \<in> trail_pol_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  by sepref_to_hoare (sep_auto simp: count_decided_pol_def)

lemmas count_decided_trail_code[sepref_fr_rules] =
   count_decided_trail[FCOMP count_decided_trail_ref]

lemma count_decided_trail_fast:
   \<open>(return o count_decided_pol, RETURN o count_decided_pol) \<in> trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  by sepref_to_hoare (sep_auto simp: count_decided_pol_def)

lemmas count_decided_trail_fast_code[sepref_fr_rules] =
   count_decided_trail_fast[FCOMP count_decided_trail_ref]


paragraph \<open>Value of a literal\<close>

definition (in -) invert_pol where
  \<open>invert_pol b L =
    (case b of
       None \<Rightarrow> UNSET
     | Some v \<Rightarrow> if is_pos L then (Some v)
       else (Some (\<not>v)))\<close>

definition (in -) polarity_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
  \<open>polarity_pol = (\<lambda>(M, xs, lvls, k) L. do {
     ASSERT(nat_of_lit L < length xs);
     RETURN (xs ! (nat_of_lit L))
  })\<close>

sepref_thm polarity_pol_code
  is \<open>uncurry polarity_pol\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  unfolding polarity_pol_def option.case_eq_if
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_pol_code
   uses isasat_input_bounded.polarity_pol_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_pol_code_def

lemmas polarity_pol_code_polarity_refine_code[sepref_fr_rules] =
   polarity_pol_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


sepref_thm polarity_pol_fast_code
  is \<open>uncurry polarity_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  unfolding polarity_pol_def option.case_eq_if
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_pol_fast_code
   uses isasat_input_bounded.polarity_pol_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_pol_fast_code_def

lemmas polarity_pol_fast_code_polarity_refine_code[sepref_fr_rules] =
   polarity_pol_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]
  
lemma 
  polarity_pol_code_polarity_refine[sepref_fr_rules]:
    \<open>(uncurry polarity_pol_code, uncurry (RETURN oo polarity)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  (is ?slow) and
  polarity_pol_fast_code_polarity_refine[sepref_fr_rules]:
    \<open>(uncurry polarity_pol_fast_code, uncurry (RETURN oo polarity)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  (is ?fast)
proof -
  have [simp]: \<open>polarity_atm M (atm_of L) = (if is_pos L then polarity M L else map_option uminus (polarity M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: polarity_atm_def polarity_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry polarity_pol, uncurry (RETURN oo polarity)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trail_pol \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
      (auto simp: trail_pol_def polarity_def polarity_pol_def invert_pol_def
        dest!: multi_member_split)
  show ?slow
    using polarity_pol_code.refine[FCOMP 2, OF isasat_input_bounded_axioms] by simp
  show ?fast
    using polarity_pol_fast_code.refine[FCOMP 2, OF isasat_input_bounded_axioms] by simp
qed

end


context isasat_input_bounded
begin

definition cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', xs, lvls, reasons, k).
     (L # M', let xs = xs[nat_of_lit L := Some True] in xs[nat_of_lit (-L) := Some False],
      lvls[atm_of L := k], reasons[atm_of L:= Some C], k))\<close>

lemma in_list_pos_neg_notD: \<open>Pos (atm_of (lit_of La)) \<notin> lits_of_l bc \<Longrightarrow>
       Neg (atm_of (lit_of La)) \<notin> lits_of_l bc \<Longrightarrow>
       La \<in> set bc \<Longrightarrow> False\<close>
  by (metis Neg_atm_of_iff Pos_atm_of_iff lits_of_def rev_image_eqI)


lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_pol \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst (fst x)\<close>)
     (auto simp add: trail_pol_def polarity_def cons_trail_Propagated_def uminus_lit_swap
        cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update'
        ann_lits_split_reasons_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        dest!: in_list_pos_neg_notD multi_member_split dest: pos_lit_in_atms_of neg_lit_in_atms_of
         simp del: nat_of_lit.simps)

lemma undefined_lit_count_decided_uint_max:
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close>
  shows \<open>Suc (count_decided M) \<le> uint_max\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have \<open>atm_of `# lit_of `# mset (Decided L # M) \<subseteq># remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  from size_mset_mono[OF this] have 1: \<open>count_decided M + 1 \<le> size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l))\<close>
    using length_filter_le[of is_decided M] unfolding uint_max_def count_decided_def
    by (auto simp del: length_filter_le)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> atm_of xa \<le> uint_max div 2\<close> for xa
    using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max
    by (cases xa) (auto simp: uint_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l) \<subseteq># mset [0..< 1 + (uint_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l) = size (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l)) \<le> 1 + uint_max div 2\<close>
    by auto

  show ?thesis
    using 1 2 by (auto simp: uint_max_def)
qed

definition (in -) get_pol where
  \<open>get_pol L = Some (is_pos L)\<close>

definition (in -) get_pol_code where
  \<open>get_pol_code L = 2 XOR (L AND 1)\<close>

lemma (in -) get_pol_hnr[sepref_fr_rules]:
  \<open>(return o get_pol_code, RETURN o get_pol) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
proof -
  have [simp]: \<open>even (nat_of_uint32 bi) \<Longrightarrow> (bi AND 1) = 0\<close> for bi :: uint32
    unfolding bitAND_1_mod_2_uint32 even_iff_mod_2_eq_zero
    apply (cases \<open>bi mod 2 = 0\<close>; cases \<open>bi mod 2 = 1\<close>)
       apply (auto simp: nat_of_uint32_mod_2)
    using word_nat_of_uint32_Rep_inject by fastforce
  have [simp]: \<open>odd (nat_of_uint32 bi) \<Longrightarrow> (bi AND 1) = 1\<close> for bi :: uint32
    unfolding bitAND_1_mod_2_uint32 even_iff_mod_2_eq_zero
    by (cases \<open>bi mod 2 = 0\<close>; cases \<open>bi mod 2 = 1\<close>)
        (auto simp: nat_of_uint32_mod_2[symmetric]
        simp del: word_nat_of_uint32_Rep_inject
        simp: word_nat_of_uint32_Rep_inject[symmetric])

  have [simp]: \<open>0 = (2 :: uint32) \<longleftrightarrow> False\<close> \<open>0 = (3 :: uint32) \<longleftrightarrow> False\<close>
    using nat_of_uint32_012(2) nat_of_uint32_3 by fastforce+

  have [simp]: \<open>2 XOR 0 = (2 :: uint32)\<close> \<open>3 XOR 0 = (3 :: uint32)\<close> \<open>2 XOR 1 = (3 :: uint32)\<close>
    \<open>3 XOR 1 = (2 :: uint32)\<close>
    by (auto simp: bitXOR_uint32_def zero_uint32.rep_eq Abs_uint32_numeral
        one_uint32.rep_eq)

  show ?thesis
    unfolding get_pol_code_def get_pol_def
    by sepref_to_hoare
     (sep_auto simp: invert_pol_def
        tri_bool_ref_def unat_lit_rel_def uint32_nat_rel_def
        br_def nat_lit_rel_def lit_of_natP_def
        tri_bool_assn_def pure_app_eq
        Collect_eq_comp
        split: option.splits if_splits)
qed

sepref_thm cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), (M, xs, lvls, reasons, k)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
        atm_of L < length lvls \<and> atm_of L < length reasons]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
    get_pol_def[symmetric] SET_TRUE_def[symmetric] SET_FALSE_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Propagated_tr_code
  uses isasat_input_bounded.cons_trail_Propagated_tr_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Propagated_tr_code_def

lemmas cons_trail_Propagated_tr_code[sepref_fr_rules] =
  cons_trail_Propagated_tr_code.refine[OF isasat_input_bounded_axioms]


sepref_thm cons_trail_Propagated_tr_fast_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), (M, xs, lvls, reasons, k)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
        atm_of L < length lvls \<and> atm_of L < length reasons]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
    get_pol_def[symmetric] SET_TRUE_def[symmetric] SET_FALSE_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Propagated_tr_fast_code
  uses isasat_input_bounded.cons_trail_Propagated_tr_fast_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Propagated_tr_fast_code_def

lemmas cons_trail_Propagated_tr_fast_code[sepref_fr_rules] =
  cons_trail_Propagated_tr_fast_code.refine[OF isasat_input_bounded_axioms]

lemma
  cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]:
    \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is ?slow is \<open>_ \<in> [?pre]\<^sub>a ?imslow \<rightarrow> ?fslow\<close>) and
  cons_trail_Propagated_tr_fast_code_cons_trail_Propagated_tr[sepref_fr_rules]:
    \<open>(uncurry2 cons_trail_Propagated_tr_fast_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a trail_fast_assn\<^sup>d \<rightarrow> trail_fast_assn\<close>
    (is ?fast is \<open>_ \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_pol)
     (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((L, C), (M, xs, lvls, reasons, k)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
        atm_of L < length lvls \<and> atm_of L < length reasons)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d)
                     (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      trail_pol) \<rightarrow> hr_comp trail_pol_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_code.refine cons_trail_Propagated_tr,
        OF isasat_input_bounded_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_pol_def ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
        intro!: ext)
  have im: \<open>?im' = ?imslow\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?fslow\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    using H unfolding im pre .

  have H: \<open>(uncurry2 cons_trail_Propagated_tr_fast_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_pol)
     (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((L, C), (M, xs, lvls, reasons, k)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
        atm_of L < length lvls \<and> atm_of L < length reasons)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d)
                     (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      trail_pol) \<rightarrow> hr_comp trail_pol_fast_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_fast_code.refine cons_trail_Propagated_tr,
        OF isasat_input_bounded_axioms] .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    using H unfolding im pre .       
qed

definition (in -) hd_trail_pol :: \<open>trail_pol \<Rightarrow> (nat literal \<times> nat option) nres\<close> where
  \<open>hd_trail_pol = (\<lambda>(M, xs, lvls, reasons, k). do {
      ASSERT(atm_of (hd M) < length reasons);
      RETURN (hd M, reasons ! (atm_of (hd M)))})\<close>

sepref_definition (in -)hd_trail_code
  is \<open>hd_trail_pol\<close>
  :: \<open>[\<lambda>(M, xs, lvls, reasons, k). M \<noteq> []]\<^sub>a
       trail_pol_assn\<^sup>k \<rightarrow> unat_lit_assn *a (option_assn nat_assn)\<close>
  unfolding hd_trail_pol_def nth_u_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition (in -)hd_trail_fast_code
  is \<open>hd_trail_pol\<close>
  :: \<open>[\<lambda>(M, xs, lvls, reasons, k). M \<noteq> []]\<^sub>a
       trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn *a (option_assn uint32_nat_assn)\<close>
  unfolding hd_trail_pol_def nth_u_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref


lemma (in -)is_propedE: \<open>is_proped L \<Longrightarrow> (\<And>K C. L = Propagated K C \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases L) auto

lemma hd_trail_pol_op_list_hd:
  \<open>(hd_trail_pol, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>f trail_pol \<rightarrow>
     \<langle>{((L, C), L'). (C = None \<longrightarrow> L' = Decided L) \<and> (C \<noteq> None \<longrightarrow> L' = Propagated L (the C))}\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: trail_pol_def hd_trail_pol_def ann_lits_split_reasons_def hd_map
      elim!: neq_NilE is_decided_ex_Decided not_is_decidedE
      simp: is_decided_no_proped_iff[symmetric])

lemma (in -) nat_ann_lit_rel_alt_def: \<open>nat_ann_lit_rel = (unat_lit_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel) O
     {((L, C), L').
      (C = None \<longrightarrow> L' = Decided L) \<and>
      (C \<noteq> None \<longrightarrow> L' = Propagated L (the C))}\<close>
  apply (rule; rule)
  subgoal for x
    by (cases x; cases \<open>fst x\<close>)
      (auto simp: nat_ann_lit_rel_def pure_def ann_lit_of_pair_alt_def hr_comp_def
        ex_assn_pair_split unat_lit_rel_def uint32_nat_rel_def br_def nat_lit_rel_def
        Collect_eq_comp lit_of_natP_def case_prod_beta relcomp.simps
        split: if_splits)
  subgoal for x
    by (cases x; cases \<open>fst x\<close>)
      (auto simp: nat_ann_lit_rel_def pure_def ann_lit_of_pair_alt_def hr_comp_def
        ex_assn_pair_split unat_lit_rel_def uint32_nat_rel_def br_def nat_lit_rel_def
        Collect_eq_comp lit_of_natP_def case_prod_beta relcomp.simps
        split: if_splits)
  done

type_synonym (in -) ann_lit_wl_uint32 = \<open>uint32 \<times> uint32 option\<close>

abbreviation (in -) pair_nat_ann_lit_uint32_assn :: \<open>(nat, nat) ann_lit \<Rightarrow> ann_lit_wl_uint32 \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lit_uint32_assn \<equiv> 
    hr_comp (uint32_assn \<times>\<^sub>a option_assn uint32_nat_assn) nat_ann_lit_rel\<close>

lemma
 hd_trail_code_hd[sepref_fr_rules]:
    \<open>(hd_trail_code, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>k \<rightarrow> pair_nat_ann_lit_assn\<close>
    (is ?slow is \<open>?c \<in> [?pre]\<^sub>a ?imslow \<rightarrow> ?fslow\<close>) and
 hd_trail_fast_code_hd[sepref_fr_rules]:
    \<open>(hd_trail_fast_code, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>a trail_fast_assn\<^sup>k \<rightarrow>
       pair_nat_ann_lit_uint32_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?c \<in>  [comp_PRE trail_pol (\<lambda>M. M \<noteq> [])
       (\<lambda>_ (M, xs, lvls, reasons, k). M \<noteq> [])
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>k)
                      trail_pol \<rightarrow> hr_comp
  (unat_lit_assn *a option_assn nat_assn)
  {((L, C), L').
   (C = None \<longrightarrow> L' = Decided L) \<and>
   (C \<noteq> None \<longrightarrow> L' = Propagated L (the C))}\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF hd_trail_code.refine hd_trail_pol_op_list_hd] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_pol_def trail_pol_def ann_lits_split_reasons_def intro!: ext)
  have im: \<open>?im' = ?imslow\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?fslow\<close>
    unfolding nat_ann_lit_rel_alt_def hr_comp_pure[symmetric] prod_assn_pure_conv[symmetric]
      option_assn_pure_conv[symmetric] ..
  show ?slow
    using H unfolding im pre f .

  have H: \<open>?cfast \<in>  [comp_PRE trail_pol (\<lambda>M. M \<noteq> [])
       (\<lambda>_ (M, xs, lvls, reasons, k). M \<noteq> [])
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_fast_assn\<^sup>k)
                      trail_pol \<rightarrow> hr_comp
  (unat_lit_assn *a option_assn uint32_nat_assn)
  {((L, C), L'). (C = None \<longrightarrow> L' = Decided L) \<and> (C \<noteq> None \<longrightarrow> L' = Propagated L (the C))}\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF hd_trail_fast_code.refine hd_trail_pol_op_list_hd] .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    unfolding nat_ann_lit_rel_alt_def hr_comp_pure[symmetric] prod_assn_pure_conv[symmetric]
      option_assn_pure_conv[symmetric] hr_comp_assoc[symmetric] by simp
  show ?fast
    using H unfolding im pre f .
qed

definition (in isasat_input_ops) tl_trailt_tr :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>tl_trailt_tr = (\<lambda>(M', xs, lvls, reasons, k). (tl M',
    let xs = xs[nat_of_lit (hd M') := None] in xs[nat_of_lit (- hd M') := None],
    lvls[atm_of (hd M') := zero_uint32_nat],
    reasons, if reasons ! atm_of (hd M') = None then k-one_uint32_nat else k))\<close>

sepref_thm tl_trail_tr_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[\<lambda>(M, xs, lvls, reason, k). M \<noteq> [] \<and> nat_of_lit(hd M) < length xs \<and>
        nat_of_lit(-hd M) < length xs  \<and> atm_of (hd M) < length lvls \<and>
        atm_of (hd M) < length reason \<and>
    (reason ! atm_of (hd M) = None \<longrightarrow> k \<ge> 1)]\<^sub>a
        trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_def UNSET_def[symmetric]
  apply (rewrite at \<open>_ - one_uint32_nat\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) tl_trail_tr_code
  uses isasat_input_bounded.tl_trail_tr_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_code_def

lemmas tl_trail_tr_coded_refine[sepref_fr_rules] =
   tl_trail_tr_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


sepref_thm tl_trail_tr_fast_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[\<lambda>(M, xs, lvls, reason, k). M \<noteq> [] \<and> nat_of_lit(hd M) < length xs \<and>
        nat_of_lit(-hd M) < length xs  \<and> atm_of (hd M) < length lvls \<and>
        atm_of (hd M) < length reason \<and>
    (reason ! atm_of (hd M) = None \<longrightarrow> k \<ge> 1)]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_def UNSET_def[symmetric]
  apply (rewrite at \<open>_ - one_uint32_nat\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) tl_trail_tr_fast_code
  uses isasat_input_bounded.tl_trail_tr_fast_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_fast_code_def

lemmas tl_trail_tr_fast_coded_refine[sepref_fr_rules] =
   tl_trail_tr_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma (in isasat_input_ops) ann_lits_split_reasons_map_lit_of:
  \<open>((M, reasons), M') \<in> ann_lits_split_reasons \<Longrightarrow> M = map lit_of M'\<close>
  by (auto simp: ann_lits_split_reasons_def)

lemma tl_trail_tr:
  \<open>((RETURN o tl_trailt_tr), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_pol \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
proof -
  show ?thesis
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def
            ann_lits_split_reasons_def)
      subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def)
      subgoal by (auto simp: polarity_atm_def tl_trailt_tr_def)
      subgoal
        by (cases \<open>lit_of L\<close>)
          (auto simp: polarity_def tl_trailt_tr_def Decided_Propagated_in_iff_in_lits_of_l
            uminus_lit_swap
            dest!: ann_lits_split_reasons_map_lit_of)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if
            dest!: ann_lits_split_reasons_map_lit_of)
      subgoal
        by (cases \<open>L\<close>)
          (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
            dest: no_dup_consistentD)
      subgoal
        by (auto simp: tl_trailt_tr_def)
      done
    done
qed

lemma
  tl_trail_tr_code_op_list_tl[sepref_fr_rules]:
    \<open>(tl_trail_tr_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is ?slow is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  tl_trail_tr_fast_code_op_list_tl[sepref_fr_rules]:
    \<open>(tl_trail_tr_fast_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_fast_assn\<^sup>d \<rightarrow> trail_fast_assn\<close>
    (is ?fast is \<open>_?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have [dest]: \<open>((a, aa, ab, r, b), x) \<in> trail_pol \<Longrightarrow> a = map lit_of x\<close> for a aa ab b x r
    by (auto simp: trail_pol_def ann_lits_split_reasons_def)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x) auto
  have H: \<open>?c
      \<in>  [comp_PRE trail_pol (\<lambda>M. M \<noteq> [])
     (\<lambda>_ (M, xs, lvls, reason, k).
         M \<noteq> [] \<and>
         nat_of_lit (hd M) < length xs \<and>
         nat_of_lit (-hd M) < length xs \<and>
         atm_of (hd M) < length lvls \<and>
         atm_of (hd M) < length reason \<and>
         (reason ! atm_of (hd M) = None \<longrightarrow> 1 \<le> k))
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>d)
                    trail_pol \<rightarrow> hr_comp trail_pol_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_code.refine tl_trail_tr, OF isasat_input_bounded_axioms]
    unfolding op_list_tl_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    apply (cases x; cases \<open>hd x\<close>)
    by (auto simp: comp_PRE_def trail_pol_def ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im apply assumption
    using pre ..
  have H: \<open>?cfast
      \<in>  [comp_PRE trail_pol (\<lambda>M. M \<noteq> [])
     (\<lambda>_ (M, xs, lvls, reason, k).
         M \<noteq> [] \<and>
         nat_of_lit (hd M) < length xs \<and>
         nat_of_lit (-hd M) < length xs \<and>
         atm_of (hd M) < length lvls \<and>
         atm_of (hd M) < length reason \<and>
         (reason ! atm_of (hd M) = None \<longrightarrow> 1 \<le> k))
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_fast_assn\<^sup>d)
                    trail_pol \<rightarrow> hr_comp trail_pol_fast_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_fast_code.refine tl_trail_tr,
     OF isasat_input_bounded_axioms]
    unfolding op_list_tl_def
    .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im apply assumption
    using pre ..
qed


definition (in -) lit_of_hd_trail where
  \<open>lit_of_hd_trail M = lit_of (hd M)\<close>

definition (in -) lit_of_hd_trail_pol where
  \<open>lit_of_hd_trail_pol = (\<lambda>(M, _). hd M)\<close>

lemma lit_of_hd_trail_pol_lit_of_hd_trail:
   \<open>(RETURN o lit_of_hd_trail_pol, RETURN o lit_of_hd_trail) \<in>
         [\<lambda>S. S \<noteq> []]\<^sub>f trail_pol \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: lit_of_hd_trail_def trail_pol_def lit_of_hd_trail_pol_def
     ann_lits_split_reasons_def hd_map
      intro!: frefI nres_relI)

sepref_definition (in -) lit_of_hd_trail_code
  is \<open>RETURN o lit_of_hd_trail_pol\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trail_pol_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_pol_def
  by sepref

sepref_definition (in -) lit_of_hd_trail_fast_code
  is \<open>RETURN o lit_of_hd_trail_pol\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_pol_def
  by sepref

theorem
  lit_of_hd_trail_code_lit_of_hd_trail[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_code, RETURN o lit_of_hd_trail)
    \<in> [\<lambda>S. S \<noteq> []]\<^sub>a trail_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is ?slow is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  lit_of_hd_trail_fast_code_lit_of_hd_trail[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_fast_code, RETURN o lit_of_hd_trail)
    \<in> [\<lambda>S. S \<noteq> []]\<^sub>a trail_fast_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE trail_pol (\<lambda>S. S \<noteq> []) (\<lambda>_ (M, _). M \<noteq> [])
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>k)
                     trail_pol \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_code.refine
      lit_of_hd_trail_pol_lit_of_hd_trail] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def trail_pol_def
       ann_lits_split_reasons_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
  have H: \<open>?cfast
    \<in> [comp_PRE trail_pol (\<lambda>S. S \<noteq> []) (\<lambda>_ (M, _). M \<noteq> [])
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_fast_assn\<^sup>k) trail_pol \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_fast_code.refine
      lit_of_hd_trail_pol_lit_of_hd_trail] .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep ..
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

definition cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>cons_trail_Decided_tr = (\<lambda>L (M', xs, lvls, reasons, k).
     (L # M', let xs = xs[nat_of_lit L := Some True] in xs[nat_of_lit (-L) := Some False],
      lvls[atm_of L := k+1], reasons[atm_of L := None], k+1))\<close>

lemma cons_trail_Decided_tr:
  \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
  [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f trail_pol \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst x\<close>)
    (auto simp: trail_pol_def polarity_def cons_trail_Decided_def uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l
        cons_trail_Decided_tr_def nth_list_update' ann_lits_split_reasons_def
      dest!: in_list_pos_neg_notD multi_member_split
      simp del: nat_of_lit.simps)

sepref_thm cons_trail_Decided_tr_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[\<lambda>(L, (M, xs, lvls, reason, k)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
      atm_of L < length lvls \<and> atm_of L < length reason \<and> L \<in> snd ` D\<^sub>0 \<and>
      Suc k \<le> uint_max]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  unfolding cons_trail_Decided_tr_def cons_trail_Decided_tr_def one_uint32_nat_def[symmetric]
    get_pol_def[symmetric] SET_TRUE_def[symmetric] SET_FALSE_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Decided_tr_code
  uses isasat_input_bounded.cons_trail_Decided_tr_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Decided_tr_code_def

lemmas cons_trail_Decided_tr_code[sepref_fr_rules] =
  cons_trail_Decided_tr_code.refine[OF isasat_input_bounded_axioms]


sepref_thm cons_trail_Decided_tr_fast_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[\<lambda>(L, (M, xs, lvls, reason, k)). nat_of_lit L < length xs \<and> nat_of_lit (-L) < length xs \<and>
      atm_of L < length lvls \<and> atm_of L < length reason \<and> L \<in> snd ` D\<^sub>0 \<and>
      Suc k \<le> uint_max]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding cons_trail_Decided_tr_def cons_trail_Decided_tr_def one_uint32_nat_def[symmetric]
    get_pol_def[symmetric] SET_TRUE_def[symmetric] SET_FALSE_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Decided_tr_fast_code
  uses isasat_input_bounded.cons_trail_Decided_tr_fast_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Decided_tr_fast_code_def

lemmas cons_trail_Decided_tr_fast_code[sepref_fr_rules] =
  cons_trail_Decided_tr_fast_code.refine[OF isasat_input_bounded_axioms]

lemma
  cons_trail_Decided_tr_code_cons_trail_Decided_tr[sepref_fr_rules]:
    \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is ?slow is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and 
  cons_trail_Decided_tr_fast_code_cons_trail_Decided_tr[sepref_fr_rules]:
    \<open>(uncurry cons_trail_Decided_tr_fast_code, uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a trail_fast_assn\<^sup>d \<rightarrow>
    trail_fast_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?c \<in>  [comp_PRE (Id \<times>\<^sub>f trail_pol)
     (\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, M, xs, lvls, reason, k).
         nat_of_lit L < length xs \<and>
         nat_of_lit (-L) < length xs \<and>
         atm_of L < length lvls \<and>
         atm_of L < length reason \<and> L \<in> snd ` D\<^sub>0 \<and> Suc k \<le> uint_max)
     (\<lambda>_. True)]\<^sub>a hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d)
                    (Id \<times>\<^sub>f
                     trail_pol) \<rightarrow> hr_comp trail_pol_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Decided_tr_code.refine cons_trail_Decided_tr,
        OF isasat_input_bounded_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_pol_def image_image ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
        intro!: ext undefined_lit_count_decided_uint_max)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    using H unfolding im pre .
  have H: \<open>?cfast \<in>  [comp_PRE (Id \<times>\<^sub>f trail_pol)
     (\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, M, xs, lvls, reason, k).
         nat_of_lit L < length xs \<and>
         nat_of_lit (-L) < length xs \<and>
         atm_of L < length lvls \<and>
         atm_of L < length reason \<and> L \<in> snd ` D\<^sub>0 \<and> Suc k \<le> uint_max)
     (\<lambda>_. True)]\<^sub>a hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d)
                    (Id \<times>\<^sub>f
                     trail_pol) \<rightarrow> hr_comp trail_pol_fast_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Decided_tr_fast_code.refine cons_trail_Decided_tr,
        OF isasat_input_bounded_axioms] .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    using H unfolding im pre .
qed

lemma (in -) nat_of_uint32_mult_le:
   \<open>nat_of_uint32 ai * nat_of_uint32 bi \<le> uint_max \<Longrightarrow>
       (a, b) \<Turnstile> emp \<Longrightarrow>
       nat_of_uint32 (ai * bi) = nat_of_uint32 ai * nat_of_uint32 bi\<close>
  apply transfer
  by (auto simp: unat_word_ariths uint_max_def)

lemma (in -) uint32_nat_assn_mult:
  \<open>(uncurry (return oo (op *)), uncurry (RETURN oo (op *))) \<in> [\<lambda>(a, b). a * b \<le> uint_max]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_mult_le)

definition (in -) defined_atm_pol where
  \<open>defined_atm_pol = (\<lambda>(M, xs, lvls, k) L. do {
      ASSERT(2*L < length xs);
      ASSERT(2*L \<le> uint_max);
      RETURN (\<not>((xs!(two_uint32_nat*L)) = None))
    })\<close>

sepref_thm defined_atm_code
  is \<open>uncurry defined_atm_pol\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding defined_atm_pol_def UNSET_def[symmetric] tri_bool_eq_def[symmetric]
  supply UNSET_def[simp del] uint32_nat_assn_mult[sepref_fr_rules]
  by sepref

concrete_definition (in -) defined_atm_code
   uses isasat_input_bounded.defined_atm_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) defined_atm_code_def

lemmas undefined_atm_code_refine[sepref_fr_rules] =
   defined_atm_code.refine[OF isasat_input_bounded_axioms]

sepref_thm defined_atm_fast_code
  is \<open>uncurry defined_atm_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding defined_atm_pol_def UNSET_def[symmetric] tri_bool_eq_def[symmetric]
  supply UNSET_def[simp del] uint32_nat_assn_mult[sepref_fr_rules]
  by sepref

concrete_definition (in -) defined_atm_fast_code
   uses isasat_input_bounded.defined_atm_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) defined_atm_fast_code_def

lemmas undefined_atm_fast_code_refine[sepref_fr_rules] =
   defined_atm_fast_code.refine[OF isasat_input_bounded_axioms]

lemma undefined_atm_code:
  \<open>(uncurry defined_atm_pol, uncurry (RETURN oo defined_atm)) \<in>
   [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>f trail_pol \<times>\<^sub>r Id \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
proof -
  have H: \<open>2*L < length xs\<close> (is \<open>?length\<close>) and
    none: \<open>defined_atm M L \<longleftrightarrow> xs ! (2*L) \<noteq> None\<close> (is ?undef) and
    le: \<open>2*L \<le> uint_max\<close> (is ?le)
    if L_N: \<open>Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and tr: \<open>((M', xs, lvls, k), M) \<in> trail_pol\<close>
    for M xs lvls k M' L
  proof -
    have
       \<open>M' = map lit_of M\<close> and
       \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length xs \<and> xs ! nat_of_lit L = polarity M L\<close>
      using tr unfolding trail_pol_def ann_lits_split_reasons_def by fast+
    then have L: \<open>nat_of_lit (Pos L) < length xs\<close> and xsL: \<open>xs ! (nat_of_lit (Pos L)) = polarity M (Pos L)\<close>
      using L_N by (auto dest!: multi_member_split)
    show ?length
      using L by simp
    show ?undef
      using xsL by (auto simp: polarity_def defined_atm_def
          Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
    show \<open>2*L \<le> uint_max\<close>
      using in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[OF L_N] by auto
  qed
  show ?thesis
    unfolding defined_atm_pol_def
    by (intro frefI nres_relI) (auto 5 5 simp: none H le intro!: ASSERT_leI)
qed

lemma undefined_atm_code_ref[sepref_fr_rules]:
  \<open>(uncurry defined_atm_code, uncurry (RETURN \<circ>\<circ> defined_atm)) \<in>
     [\<lambda>(a, b). Pos b \<in> snd ` D\<^sub>0]\<^sub>a (hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using undefined_atm_code_refine[FCOMP undefined_atm_code] .

lemma undefined_atm_fast_code_ref[sepref_fr_rules]:
  \<open>(uncurry defined_atm_fast_code, uncurry (RETURN \<circ>\<circ> defined_atm)) \<in>
     [\<lambda>(a, b). Pos b \<in> snd ` D\<^sub>0]\<^sub>a (hr_comp trail_pol_fast_assn trail_pol)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using undefined_atm_fast_code_refine[FCOMP undefined_atm_code] .
end

definition get_propagation_reason :: \<open>('v, 'mark) ann_lits \<Rightarrow> 'v literal \<Rightarrow> 'mark option nres\<close> where
  \<open>get_propagation_reason M L = SPEC(\<lambda>C. C \<noteq> None \<longrightarrow> Propagated L (the C) \<in> set M)\<close>

definition get_propagation_reason_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close> where
  \<open>get_propagation_reason_pol = (\<lambda>(_, _, _, reasons, _) L. do {
        ASSERT(atm_of L < length reasons);
        RETURN (reasons ! atm_of L)})\<close>

sepref_definition get_propagation_reason_code
  is \<open>uncurry get_propagation_reason_pol\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  unfolding get_propagation_reason_pol_def
  by sepref

sepref_definition get_propagation_reason_fast_code
  is \<open>uncurry get_propagation_reason_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint32_nat_assn\<close>
  unfolding get_propagation_reason_pol_def
  by sepref

context isasat_input_ops
begin

sepref_register get_propagation_reason

lemma get_propagation_reason_pol:
  \<open>(uncurry get_propagation_reason_pol, uncurry get_propagation_reason) \<in>
       [\<lambda>(M, L). L \<in> lits_of_l M]\<^sub>f trail_pol \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>nat_rel\<rangle>option_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lits_of_def
  apply clarify
  apply (rename_tac a aa ab ac b ba ad bb x, case_tac x)
  by (auto simp: get_propagation_reason_def get_propagation_reason_pol_def
      trail_pol_def ann_lits_split_reasons_def lits_of_def assert_bind_spec_conv)

lemma get_propagation_reason_hnr[sepref_fr_rules]:
   \<open>(uncurry get_propagation_reason_code, uncurry get_propagation_reason)
     \<in> [\<lambda>(a, b). b \<in> lits_of_l a]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  using get_propagation_reason_code.refine[FCOMP get_propagation_reason_pol] .

lemma get_propagation_reason_fast_hnr[sepref_fr_rules]:
   \<open>(uncurry get_propagation_reason_fast_code, uncurry get_propagation_reason)
     \<in> [\<lambda>(a, b). b \<in> lits_of_l a]\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn uint32_nat_assn\<close>
  using get_propagation_reason_fast_code.refine[FCOMP get_propagation_reason_pol] .

end

end
