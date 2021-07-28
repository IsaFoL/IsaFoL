theory IsaSAT_VDom_LLVM
  imports IsaSAT_VDom IsaSAT_Stats_LLVM IsaSAT_Clauses_LLVM IsaSAT_Arena_Sorting_LLVM
begin
no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

type_synonym aivdom2 = \<open>vdom \<times> vdom \<times> vdom\<close>
abbreviation aivdom_int_rel :: \<open>(aivdom2 \<times> aivdom) set\<close> where
  \<open>aivdom_int_rel \<equiv> {(a, (_, a')). (a,a') \<in> \<langle>nat_rel\<rangle>list_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>list_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>list_rel}\<close>

abbreviation aivdom_rel :: \<open>(aivdom2 \<times> isasat_aivdom) set\<close> where
  \<open>aivdom_rel \<equiv> \<langle>aivdom_int_rel\<rangle>code_hider_rel\<close>

abbreviation aivdom_int_assn :: \<open>aivdom2 \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>aivdom_int_assn \<equiv> LBD_it.arr_assn \<times>\<^sub>a LBD_it.arr_assn  \<times>\<^sub>a LBD_it.arr_assn\<close>
type_synonym aivdom_assn = \<open>vdom_fast_assn \<times> vdom_fast_assn \<times> vdom_fast_assn\<close>
definition aivdom_assn :: \<open>isasat_aivdom \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>aivdom_assn = code_hider_assn aivdom_int_assn aivdom_int_rel\<close>

text \<open>To keep my sanity, I use the same name, even if the function drops one component.\<close>
definition add_learned_clause_aivdom_int where
  \<open>add_learned_clause_aivdom_int = (\<lambda> C (avdom, ivdom). (avdom @ [C], ivdom))\<close>

definition remove_inactive_aivdom_int :: \<open>_ \<Rightarrow> aivdom2 \<Rightarrow> aivdom2\<close> where
  \<open>remove_inactive_aivdom_int = (\<lambda>i (avdom, ivdom). (delete_index_and_swap avdom i, ivdom))\<close>

definition avdom_aivdom_at_int :: \<open>aivdom2 \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>avdom_aivdom_at_int = (\<lambda>(b,c) C. b ! C)\<close>

definition tvdom_aivdom_at_int :: \<open>aivdom2 \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>tvdom_aivdom_at_int = (\<lambda>(b,c,d) C. d ! C)\<close>


definition length_ivdom_aivdom_int :: \<open>aivdom2 \<Rightarrow> nat\<close> where
  \<open>length_ivdom_aivdom_int = (\<lambda>(b,c,d). length c)\<close>

definition ivdom_aivdom_at_int :: \<open>aivdom2 \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>ivdom_aivdom_at_int = (\<lambda>(b,c,d) C. c ! C)\<close>

definition length_tvdom_aivdom_int :: \<open>aivdom2 \<Rightarrow> nat\<close> where
  \<open>length_tvdom_aivdom_int = (\<lambda>(b,c,d). length d)\<close>

definition length_avdom_aivdom_int :: \<open>aivdom2 \<Rightarrow> nat\<close> where
  \<open>length_avdom_aivdom_int = (\<lambda>(b,c,d). length b)\<close>

definition AIVDom_int :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> aivdom2\<close> where
  \<open>AIVDom_int _ avdom ivdom tvdom = (avdom, ivdom, tvdom)\<close>

definition swap_avdom_aivdom_int :: \<open>aivdom2 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> aivdom2\<close> where
  \<open>swap_avdom_aivdom_int = (\<lambda>(avdom, ivdom, tvdom) i j.
  (swap avdom i j, ivdom, tvdom))\<close>

lemma swap_avdom_aivdom_alt_def:
  \<open>swap_avdom_aivdom aivdom i j =
  (AIvdom (get_vdom_aivdom aivdom, swap (get_avdom_aivdom aivdom) i j, get_ivdom_aivdom aivdom, get_tvdom_aivdom aivdom))\<close>
  by (cases aivdom) auto

definition take_avdom_aivdom_int :: \<open>nat \<Rightarrow> aivdom2 \<Rightarrow> aivdom2\<close> where
  \<open>take_avdom_aivdom_int = (\<lambda>i (avdom, ivdom, tvdom).
  (take i avdom, ivdom, tvdom))\<close>

lemma take_avdom_aivdom_alt_def:
  \<open>take_avdom_aivdom i aivdom =
  (AIvdom (get_vdom_aivdom aivdom, take i (get_avdom_aivdom aivdom), get_ivdom_aivdom aivdom, get_tvdom_aivdom aivdom))\<close>
  by (cases aivdom) auto
  
lemma
  add_learned_clause_aivdom_int:
  \<open>(uncurry (RETURN oo add_learned_clause_aivdom_int), uncurry (RETURN oo add_learned_clause_aivdom)) \<in> nat_rel \<times>\<^sub>f aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close> and
  remove_inactive_aivdom_int:
  \<open>(uncurry (RETURN oo remove_inactive_aivdom_int), uncurry (RETURN oo remove_inactive_aivdom)) \<in> nat_rel \<times>\<^sub>f aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close> and
  avdom_aivdom_at_int:
  \<open>(uncurry (RETURN oo avdom_aivdom_at_int), uncurry (RETURN oo avdom_aivdom_at)) \<in> aivdom_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>and
  tvdom_aivdom_at_int:
  \<open>(uncurry (RETURN oo tvdom_aivdom_at_int), uncurry (RETURN oo tvdom_aivdom_at)) \<in> aivdom_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>and
  ivdom_aivdom_at_int:
  \<open>(uncurry (RETURN oo ivdom_aivdom_at_int), uncurry (RETURN oo ivdom_aivdom_at)) \<in> aivdom_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>and
  length_avdom_aivdom_int:
  \<open>(RETURN o length_avdom_aivdom_int, RETURN o length_avdom_aivdom) \<in> aivdom_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>and
  length_ivdom_aivdom_int:
  \<open>(RETURN o length_ivdom_aivdom_int, RETURN o length_ivdom_aivdom) \<in> aivdom_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close> and
  length_tvdom_aivdom_int:
  \<open>(RETURN o length_tvdom_aivdom_int, RETURN o length_tvdom_aivdom) \<in> aivdom_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close> and
  swap_avdom_aivdom_int:
  \<open>(uncurry2 (RETURN ooo swap_avdom_aivdom_int), uncurry2 (RETURN ooo swap_avdom_aivdom))
  \<in> aivdom_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel  \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close> and
  take_avdom_aivdom_int:
  \<open>(uncurry (RETURN oo take_avdom_aivdom_int), uncurry (RETURN oo take_avdom_aivdom))
  \<in> nat_rel \<times>\<^sub>f aivdom_rel  \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close>
  apply (auto intro!: frefI nres_relI simp: code_hider_rel_def add_learned_clause_aivdom_def remove_inactive_aivdom_def avdom_aivdom_at_alt_def
    ivdom_aivdom_at_alt_def vdom_aivdom_at_alt_def length_vdom_aivdom_alt_def length_avdom_aivdom_alt_def length_ivdom_aivdom_alt_def length_tvdom_aivdom_alt_def tvdom_aivdom_at_alt_def add_learned_clause_aivdom_int_def
    IsaSAT_VDom.add_learned_clause_aivdom_int_def
    IsaSAT_VDom.remove_inactive_aivdom_int_def remove_inactive_aivdom_int_def
    IsaSAT_VDom.avdom_aivdom_at_int_def avdom_aivdom_at_int_def
    IsaSAT_VDom.tvdom_aivdom_at_int_def tvdom_aivdom_at_int_def
    IsaSAT_VDom.ivdom_aivdom_at_int_def ivdom_aivdom_at_int_def
    IsaSAT_VDom.length_avdom_aivdom_int_def length_avdom_aivdom_int_def
    IsaSAT_VDom.length_ivdom_aivdom_int_def length_ivdom_aivdom_int_def
    IsaSAT_VDom.length_tvdom_aivdom_int_def length_tvdom_aivdom_int_def
    swap_avdom_aivdom_alt_def)
   apply (case_tac ab; auto simp: swap_avdom_aivdom_int_def take_avdom_aivdom_int_def)
   apply (case_tac ba; auto simp: swap_avdom_aivdom_int_def take_avdom_aivdom_int_def)
   done

sepref_def add_learned_clause_aivdom_impl
  is \<open>uncurry (RETURN oo add_learned_clause_aivdom_int)\<close>
  :: \<open>[\<lambda>(C,(a,b,c)). Suc (length (a)) < max_snat 64]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding add_learned_clause_aivdom_int_def
  by sepref

sepref_def remove_inactive_aivdom_impl
  is \<open>uncurry (RETURN oo remove_inactive_aivdom_int)\<close>
  :: \<open>[\<lambda>(C,(a,b,c)). C < (length a)]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding remove_inactive_aivdom_int_def
  by sepref

sepref_def ivdom_aivdom_at_impl
  is \<open>uncurry (RETURN oo ivdom_aivdom_at_int)\<close>
  :: \<open>[\<lambda>((b,c,d), C). C < (length c)]\<^sub>a aivdom_int_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  unfolding ivdom_aivdom_at_int_def
  by sepref

sepref_def avdom_aivdom_at_impl
  is \<open>uncurry (RETURN oo avdom_aivdom_at_int)\<close>
  :: \<open>[\<lambda>((b,c), C). C < (length b)]\<^sub>a aivdom_int_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  unfolding avdom_aivdom_at_int_def
  by sepref

sepref_def tvdom_aivdom_at_impl
  is \<open>uncurry (RETURN oo tvdom_aivdom_at_int)\<close>
  :: \<open>[\<lambda>((b,c,d), C). C < (length d)]\<^sub>a aivdom_int_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  unfolding tvdom_aivdom_at_int_def
  by sepref

sepref_def length_avdom_aivdom_impl
  is \<open>RETURN o length_avdom_aivdom_int\<close>
  :: \<open>aivdom_int_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_avdom_aivdom_int_def
  by sepref


definition workaround_RF where
  \<open>workaround_RF xs = length xs\<close>

sepref_def workaround_RF_code [llvm_inline]
  is \<open>RETURN o workaround_RF\<close>
  :: \<open>vdom_fast_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding workaround_RF_def
  by sepref


sepref_def length_ivdom_aivdom_impl
  is \<open>RETURN o length_ivdom_aivdom_int\<close>
  :: \<open>aivdom_int_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_ivdom_aivdom_int_def comp_def workaround_RF_def[symmetric]
  by sepref

sepref_def length_tvdom_aivdom_impl
  is \<open>RETURN o length_tvdom_aivdom_int\<close>
  :: \<open>aivdom_int_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_tvdom_aivdom_int_def comp_def workaround_RF_def[symmetric]
  by sepref

sepref_def swap_avdom_aivdom_impl
  is \<open>uncurry2 (RETURN ooo swap_avdom_aivdom_int)\<close>
  :: \<open>[\<lambda>(((b,c,d),i), j). i < length b \<and> j < length b]\<^sub>a aivdom_int_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> aivdom_int_assn\<close>
  unfolding swap_avdom_aivdom_int_def convert_swap gen_swap
  by sepref

sepref_def take_avdom_aivdom_impl
  is \<open>uncurry (RETURN oo take_avdom_aivdom_int)\<close>
  :: \<open>[\<lambda>(i, (b,c,d)). i \<le> length b]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding take_avdom_aivdom_int_def
  by sepref

lemma aivdom_assn_alt_def:
  \<open>aivdom_assn = hr_comp aivdom_int_assn (\<langle>aivdom_int_rel\<rangle>code_hider_rel)\<close>
  unfolding aivdom_assn_def code_hider_assn_def by auto

context
  notes [fcomp_norm_unfold] = aivdom_assn_alt_def[symmetric] aivdom_assn_def[symmetric]
begin

theorem [sepref_fr_rules]:
  \<open>(uncurry add_learned_clause_aivdom_impl, uncurry (RETURN \<circ>\<circ> add_learned_clause_aivdom))
\<in> [\<lambda>(C,ai). Suc (length (get_avdom_aivdom ai)) < max_snat 64]\<^sub>a snat_assn\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE (nat_rel \<times>\<^sub>f aivdom_rel) (\<lambda>_. True)
   (\<lambda>x y. case y of (C, a, b, c) \<Rightarrow> Suc (length a) < max_snat 64)
   (\<lambda>x. nofail (uncurry (RETURN \<circ>\<circ> add_learned_clause_aivdom) x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF add_learned_clause_aivdom_impl.refine
      add_learned_clause_aivdom_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by blast
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>snd x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed


theorem [sepref_fr_rules]:
  \<open>(uncurry remove_inactive_aivdom_impl, uncurry (RETURN \<circ>\<circ> remove_inactive_aivdom))
\<in> [\<lambda>(C,ai). C < (length (get_avdom_aivdom ai)) ]\<^sub>a snat_assn\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE
   (nat_rel \<times>\<^sub>f aivdom_rel)
   (\<lambda>_. True) (\<lambda>x y. case y of (C, a, b, c) \<Rightarrow> C < length a)
   (\<lambda>x. nofail (uncurry (RETURN \<circ>\<circ> remove_inactive_aivdom) x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF remove_inactive_aivdom_impl.refine
      remove_inactive_aivdom_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by blast
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>snd x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed


theorem [sepref_fr_rules]:
  \<open>(uncurry avdom_aivdom_at_impl, uncurry (RETURN \<circ>\<circ> avdom_aivdom_at))
\<in> [\<lambda>(ai, C). C < (length (get_avdom_aivdom ai)) ]\<^sub>a aivdom_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE
    (aivdom_rel \<times>\<^sub>f nat_rel)
    (\<lambda>_. True) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (b, c) \<Rightarrow> \<lambda>C. C < length b) xa)
    (\<lambda>x. nofail
    (uncurry (RETURN \<circ>\<circ> avdom_aivdom_at) x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF avdom_aivdom_at_impl.refine
      avdom_aivdom_at_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by simp
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>fst x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed


theorem [sepref_fr_rules]:
  \<open>(uncurry ivdom_aivdom_at_impl, uncurry (RETURN \<circ>\<circ> ivdom_aivdom_at))
\<in> [\<lambda>(ai, C). C < (length (get_ivdom_aivdom ai)) ]\<^sub>a aivdom_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE
    (\<langle>aivdom_int_rel\<rangle>code_hider_rel \<times>\<^sub>f nat_rel)
    (\<lambda>_. True) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (b, c, d) \<Rightarrow> \<lambda>C. C < length c) xa)
    (\<lambda>x. nofail
    (uncurry (RETURN \<circ>\<circ> ivdom_aivdom_at) x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF ivdom_aivdom_at_impl.refine
      ivdom_aivdom_at_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by simp
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>fst x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed


theorem [sepref_fr_rules]:
  \<open>(uncurry tvdom_aivdom_at_impl, uncurry (RETURN \<circ>\<circ> tvdom_aivdom_at))
\<in> [\<lambda>(ai, C). C < (length (get_tvdom_aivdom ai)) ]\<^sub>a aivdom_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE
   (aivdom_rel \<times>\<^sub>f nat_rel)
   (\<lambda>_. True) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (b, c, d) \<Rightarrow> \<lambda>C. C < length d) xa)
   (\<lambda>x. nofail
      (uncurry (RETURN \<circ>\<circ> tvdom_aivdom_at) x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF tvdom_aivdom_at_impl.refine
      tvdom_aivdom_at_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by blast
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>fst x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed


theorem [sepref_fr_rules]:
  \<open>(uncurry take_avdom_aivdom_impl, uncurry (RETURN \<circ>\<circ> take_avdom_aivdom))
\<in> [\<lambda>(C, ai). C \<le> length (get_avdom_aivdom ai)]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE (nat_rel \<times>\<^sub>f aivdom_rel) (\<lambda>_. True)
    (\<lambda>x y. case y of (i, b, c, d) \<Rightarrow> i \<le> length b)
    (\<lambda>x. nofail (uncurry (RETURN \<circ>\<circ> take_avdom_aivdom) x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF take_avdom_aivdom_impl.refine
      take_avdom_aivdom_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by blast
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>snd x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed


theorem [sepref_fr_rules]:
  \<open>(uncurry2 swap_avdom_aivdom_impl, uncurry2 (RETURN ooo swap_avdom_aivdom))
  \<in> [\<lambda>((ai, i), j). i < length (get_avdom_aivdom ai) \<and> j < length (get_avdom_aivdom ai)]\<^sub>a
  aivdom_assn\<^sup>d   *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE (aivdom_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) (\<lambda>_. True)
    (\<lambda>x y. case y of
     (x, xa) \<Rightarrow>
       (case x of
        (x, xa) \<Rightarrow>
       (case x of
        (b, c, d) \<Rightarrow> \<lambda>i j. i < length b \<and> j < length b)
        xa)
        xa)
    (\<lambda>x. nofail
    (uncurry2 (RETURN \<circ>\<circ>\<circ> swap_avdom_aivdom)
      x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a _ \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF swap_avdom_aivdom_impl.refine
      swap_avdom_aivdom_int, unfolded fcomp_norm_unfold aivdom_assn_alt_def[symmetric]] by blast
  have pre: \<open>?pre' = ?pre\<close> for x h
    by (intro ext, rename_tac x, case_tac x, case_tac \<open>fst (fst x)\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    using H
    unfolding pre
    by blast
qed

lemma aivdom_int_assn_alt_def:
  \<open>aivdom_int_assn = hr_comp aivdom_int_assn
  (\<langle>nat_rel\<rangle>list_rel \<times>\<^sub>f (\<langle>nat_rel\<rangle>list_rel \<times>\<^sub>f \<langle>nat_rel\<rangle>list_rel))\<close>
  by auto

sepref_register swap_avdom_aivdom take_avdom_aivdom
lemmas [sepref_fr_rules] =
  length_avdom_aivdom_impl.refine[FCOMP length_avdom_aivdom_int]
  length_ivdom_aivdom_impl.refine[FCOMP length_ivdom_aivdom_int]
  length_tvdom_aivdom_impl.refine[FCOMP length_tvdom_aivdom_int]
  hn_id[FCOMP Constructor_hnr[of aivdom_int_rel], of aivdom_int_assn,
  unfolded aivdom_assn_alt_def[symmetric] aivdom_assn_def[symmetric] aivdom_int_assn_alt_def[symmetric]]
    hn_id[FCOMP get_content_hnr[of aivdom_int_rel], of aivdom_int_assn,
  unfolded aivdom_assn_alt_def[symmetric] aivdom_assn_def[symmetric] aivdom_int_assn_alt_def[symmetric]]

end

end