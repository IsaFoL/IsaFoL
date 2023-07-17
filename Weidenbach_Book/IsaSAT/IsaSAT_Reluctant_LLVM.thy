theory IsaSAT_Reluctant_LLVM
imports IsaSAT_Reluctant WB_More_Word IsaSAT_Literals Watched_Literals.WB_More_IICF_LLVM
  IsaSAT_Literals_LLVM
begin

type_synonym reluctant_rel = \<open>bool \<times> bool \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>
type_synonym reluctant_rel_assn = \<open>1 word \<times> 1 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>
definition reluctant_rel_assn :: \<open>reluctant_rel \<Rightarrow>  reluctant_rel_assn\<Rightarrow> assn\<close>where
  \<open>reluctant_rel_assn = bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn\<close>

definition reluctant_rel :: \<open>(reluctant_rel \<times> reluctant) set\<close> where
  \<open>reluctant_rel = {((limited, trigger, u, v, period, wait, limit), r).
      limited = reluctant_limited r \<and>
    trigger = reluctant_trigger r \<and>
    u = reluctant_u r \<and>
    v = reluctant_v r \<and>
    period = reluctant_period r \<and>
    wait = reluctant_wait r \<and>
    limit = reluctant_limit r}\<close>

definition reluctant_assn where
  \<open>reluctant_assn = hr_comp reluctant_rel_assn reluctant_rel\<close>
schematic_goal mk_free_reluctant_rel_assn[sepref_frame_free_rules]: \<open>MK_FREE reluctant_rel_assn ?fr\<close>
  unfolding reluctant_rel_assn_def
  by synthesize_free

schematic_goal mk_free_reluctant_assn[sepref_frame_free_rules]: \<open>MK_FREE reluctant_assn ?fr\<close>
  unfolding reluctant_assn_def
  by synthesize_free

lemma [safe_constraint_rules]:
  \<open>CONSTRAINT Sepref_Basic.is_pure reluctant_rel_assn\<close>
  \<open>CONSTRAINT Sepref_Basic.is_pure reluctant_assn\<close>
  unfolding reluctant_rel_assn_def reluctant_assn_def
  by (auto intro!: hr_comp_is_pure)

definition reluctant_c :: \<open> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> reluctant_rel\<close>where
  \<open>reluctant_c limited trigger u v period wait limit = (limited, trigger, u, v, period, wait, limit)\<close>

lemma reluctant_c_Reluctant:
  \<open>(uncurry6 (RETURN ooooooo reluctant_c), uncurry6 (RETURN ooooooo Reluctant)) \<in>
    Id \<times>\<^sub>f Id  \<times>\<^sub>f Id  \<times>\<^sub>f Id  \<times>\<^sub>f Id  \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>reluctant_rel\<rangle>nres_rel\<close>
  by (auto simp: reluctant_c_def reluctant_rel_def intro!: frefI nres_relI)

sepref_register reluctant_c
sepref_def reluctant_impl
  is \<open>uncurry6 (RETURN ooooooo reluctant_c)\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_rel_assn\<close>
  unfolding reluctant_c_def reluctant_rel_assn_def
  by sepref

lemmas [sepref_fr_rules] =
  reluctant_impl.refine[FCOMP reluctant_c_Reluctant, unfolded reluctant_assn_def[symmetric]]

definition reluctant_c_limited :: \<open>reluctant_rel \<Rightarrow> bool\<close>where
  \<open>reluctant_c_limited = (\<lambda>(limited, trigger, u, v, period, wait, limit). limited)\<close>

definition reluctant_c_triggered :: \<open>reluctant_rel \<Rightarrow> bool\<close>where
  \<open>reluctant_c_triggered = (\<lambda>(triggered, trigger, u, v, period, wait, limit). trigger)\<close>

definition reluctant_c_u :: \<open>reluctant_rel \<Rightarrow> 64 word\<close>where
  \<open>reluctant_c_u = (\<lambda>(triggered, trigger, u, v, period, wait, limit). u)\<close>

definition reluctant_c_v :: \<open>reluctant_rel \<Rightarrow> 64 word\<close>where
  \<open>reluctant_c_v = (\<lambda>(triggered, trigger, u, v, period, wait, limit). v)\<close>
definition reluctant_c_period :: \<open>reluctant_rel \<Rightarrow> 64 word\<close>where
  \<open>reluctant_c_period = (\<lambda>(triggered, trigger, u, v, period, wait, limit). period)\<close>

definition reluctant_c_wait :: \<open>reluctant_rel \<Rightarrow> 64 word\<close>where
  \<open>reluctant_c_wait = (\<lambda>(triggered, trigger, u, v, period, wait, limit). wait)\<close>

definition reluctant_c_limit :: \<open>reluctant_rel \<Rightarrow> 64 word\<close>where
  \<open>reluctant_c_limit = (\<lambda>(triggered, trigger, u, v, period, wait, limit). limit)\<close>

sepref_def reluctant_limited_impl
  is \<open>RETURN o reluctant_c_limited\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding reluctant_c_limited_def reluctant_rel_assn_def
  by sepref

sepref_def reluctant_triggered_impl
  is \<open>RETURN o reluctant_c_triggered\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding reluctant_c_triggered_def reluctant_rel_assn_def
  by sepref

sepref_def reluctant_u_impl
  is \<open>RETURN o reluctant_c_u\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a  word64_assn\<close>
  unfolding reluctant_c_u_def reluctant_rel_assn_def
  by sepref

sepref_def reluctant_v_impl
  is \<open>RETURN o reluctant_c_v\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a  word64_assn\<close>
  unfolding reluctant_c_v_def reluctant_rel_assn_def
  by sepref

sepref_def reluctant_wait_impl
  is \<open>RETURN o reluctant_c_wait\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a  word64_assn\<close>
  unfolding reluctant_c_wait_def reluctant_rel_assn_def
  by sepref

sepref_def reluctant_period_impl
  is \<open>RETURN o reluctant_c_period\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a  word64_assn\<close>
  unfolding reluctant_c_period_def reluctant_rel_assn_def
  by sepref

sepref_def reluctant_limit_impl
  is \<open>RETURN o reluctant_c_limit\<close>
  :: \<open>reluctant_rel_assn\<^sup>k \<rightarrow>\<^sub>a  word64_assn\<close>
  unfolding reluctant_c_limit_def reluctant_rel_assn_def
  by sepref


lemma reluctant_c_limited: \<open>(reluctant_c_limited, reluctant_limited) \<in> reluctant_rel \<rightarrow> Id\<close> and
  reluctant_c_triggered: \<open>(reluctant_c_triggered, reluctant_trigger) \<in> reluctant_rel \<rightarrow> Id\<close> and
  reluctant_c_u: \<open>(reluctant_c_u, reluctant_u) \<in> reluctant_rel \<rightarrow> Id\<close> and
  reluctant_c_v: \<open>(reluctant_c_v, reluctant_v) \<in> reluctant_rel \<rightarrow> Id\<close> and
  reluctant_c_wait: \<open>(reluctant_c_wait, reluctant_wait) \<in> reluctant_rel \<rightarrow> Id\<close> and
  reluctant_c_period: \<open>(reluctant_c_period, reluctant_period) \<in> reluctant_rel \<rightarrow> Id\<close> and
  reluctant_c_limit: \<open>(reluctant_c_limit, reluctant_limit) \<in> reluctant_rel \<rightarrow> Id\<close>
  by (auto simp: reluctant_rel_def reluctant_c_limited_def reluctant_c_triggered_def
    reluctant_c_u_def reluctant_c_v_def reluctant_c_wait_def reluctant_c_period_def reluctant_c_limit_def
    intro!: frefI nres_relI)

lemmas [sepref_fr_rules] =
  reluctant_limited_impl.refine[FCOMP reluctant_c_limited, unfolded reluctant_assn_def[symmetric]]
  reluctant_triggered_impl.refine[FCOMP reluctant_c_triggered, unfolded reluctant_assn_def[symmetric]]
  reluctant_u_impl.refine[FCOMP reluctant_c_u, unfolded reluctant_assn_def[symmetric]]
  reluctant_v_impl.refine[FCOMP reluctant_c_v, unfolded reluctant_assn_def[symmetric]]
  reluctant_wait_impl.refine[FCOMP reluctant_c_wait, unfolded reluctant_assn_def[symmetric]]
  reluctant_period_impl.refine[FCOMP reluctant_c_period, unfolded reluctant_assn_def[symmetric]]
  reluctant_limit_impl.refine[FCOMP reluctant_c_limit, unfolded reluctant_assn_def[symmetric]]

sepref_register reluctant_impl reluctant_tick reluctant_enable reluctant_set_trigger
  reluctant_triggered reluctant_untrigger reluctant_triggered2 reluctant_init
  reluctant_disable

lemma reluctant_tick_alt_def:
  \<open>RETURN o reluctant_tick  =
  (\<lambda>r. let
    limited = reluctant_limited r;
    trigger = reluctant_trigger r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
    limit = reluctant_limit r in
  (if period = 0 \<or> trigger then RETURN (Reluctant limited trigger u v period (wait) limit)
   else if wait > 1 then RETURN (Reluctant limited trigger u v period (wait - 1) limit)
  else let  zero = u-u;
            b = u AND (zero - u);
            (u, v) = (if b = v then (u+1, 1) else (u, 2 * v));
            (u, v) = (if limited \<and> wait > limit then (1,1) else (u, v));
            wait = v * period in
  RETURN (Reluctant limited True u v period wait limit)))\<close>
  by (auto intro!: ext simp: reluctant_tick_def Let_def)

sepref_register \<open>(AND) :: 'a :: len word \<Rightarrow> _ \<Rightarrow> _\<close>
sepref_def reluctant_tick_impl
  is \<open>RETURN o reluctant_tick\<close>
  :: \<open>reluctant_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn\<close>
  unfolding reluctant_tick_alt_def
  by sepref

export_llvm reluctant_tick_impl

sepref_def reluctant_enable_impl
  is \<open>uncurry (RETURN oo reluctant_enable)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn\<close>
  unfolding reluctant_enable_def
  by sepref

sepref_def reluctant_set_trigger_impl
  is \<open>uncurry (RETURN oo reluctant_set_trigger)\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a reluctant_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn\<close>
  unfolding reluctant_set_trigger_def
  by sepref

sepref_def reluctant_triggered_ether_impl
  is \<open>(RETURN o reluctant_triggered)\<close>
  :: \<open>reluctant_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn \<times>\<^sub>a bool1_assn\<close>
  unfolding reluctant_triggered_def
  by sepref

sepref_def reluctant_triggered2_impl
  is \<open>(RETURN o reluctant_triggered2)\<close>
  :: \<open>reluctant_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding reluctant_triggered2_def
  by sepref

sepref_def reluctant_untrigger_impl
  is \<open>(RETURN o reluctant_untrigger)\<close>
  :: \<open>reluctant_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn\<close>
  unfolding reluctant_untrigger_def
  by sepref

sepref_def reluctant_disable_impl
  is \<open>RETURN o reluctant_disable\<close>
  :: \<open>reluctant_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn\<close>
  unfolding reluctant_disable_def
  by sepref

sepref_def reluctant_init_impl
  is \<open>uncurry0 (RETURN reluctant_init)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a reluctant_assn\<close>
  unfolding reluctant_init_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

experiment
begin
  export_llvm  reluctant_init_impl reluctant_enable_impl reluctant_disable_impl reluctant_triggered2_impl
    reluctant_triggered_impl reluctant_set_trigger_impl reluctant_enable_impl reluctant_triggered_ether_impl
  export_llvm reluctant_tick_impl

end

end