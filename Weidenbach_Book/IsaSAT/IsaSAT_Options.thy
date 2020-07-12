theory IsaSAT_Options
imports IsaSAT_Literals
begin

section \<open>Options\<close>

text \<open>We define the options from our SAT solver. Using options has several advantages: it is much
  easier to change the value (instead of recompiling everything from scratch the complete Isabelle
  development) and it is easier to change.

  We hide the options inside a datatype to make sure Isabelle does not split the the component to
  make goals even less readable.
\<close>

subsection \<open>Definition\<close>

type_synonym opts_target = \<open>3 word\<close>

datatype opts =
  IsaOptions (opts_restart: bool)
  (opts_reduce: bool)
  (opts_unbounded_mode: bool)
  (opts_minimum_between_restart: \<open>64 word\<close>)
  (opts_restart_coeff1: \<open>64 word\<close>)
  (opts_restart_coeff2: nat)
  (opts_target: \<open>opts_target\<close>)


definition TARGET_NEVER :: \<open>opts_target\<close> where
  \<open>TARGET_NEVER = 0\<close>

definition TARGET_QUIET_ONLY :: \<open>opts_target\<close> where
  \<open>TARGET_QUIET_ONLY = 1\<close>

definition TARGET_ALWAYS :: \<open>opts_target\<close> where
  \<open>TARGET_ALWAYS = 2\<close>


subsection \<open>Refinement\<close>

type_synonym opts_ref =
  \<open>bool \<times> bool \<times> bool \<times> 64 word \<times> 64 word \<times> nat \<times> opts_target\<close>

definition opts_rel :: \<open>(opts_ref \<times> opts) set\<close> where
  \<open>opts_rel = {(S, T). S = (opts_restart T, opts_reduce T, opts_unbounded_mode T,
      opts_minimum_between_restart T, opts_restart_coeff1 T, opts_restart_coeff2 T,
      opts_target T)}\<close>

fun opts_rel_restart :: \<open>opts_ref \<Rightarrow> bool\<close> where
  \<open>opts_rel_restart (res, red, unbd, mini, res1, res2) = res\<close>

lemma opts_rel_restart:
  \<open>(opts_rel_restart, opts_restart) \<in> opts_rel \<rightarrow> bool_rel\<close>
  by (auto simp: opts_rel_def intro!: frefI)


fun opts_rel_reduce :: \<open>opts_ref \<Rightarrow> bool\<close> where
  \<open>opts_rel_reduce (res, red, unbd, mini, res1, res2) = red\<close>

lemma opts_rel_reduce:
  \<open>(opts_rel_reduce, opts_reduce) \<in> opts_rel \<rightarrow> bool_rel\<close>
  by (auto simp: opts_rel_def intro!: frefI)

fun opts_rel_unbounded_mode :: \<open>opts_ref \<Rightarrow> bool\<close> where
  \<open>opts_rel_unbounded_mode (res, red, unbd, mini, res1, res2) = unbd\<close>

lemma opts_rel_unbounded_mode:
  \<open>(opts_rel_unbounded_mode, opts_unbounded_mode) \<in> opts_rel \<rightarrow> bool_rel\<close>
  by (auto simp: opts_rel_def intro!: frefI)

fun opts_rel_miminum_between_restart :: \<open>opts_ref \<Rightarrow> 64 word\<close> where
  \<open>opts_rel_miminum_between_restart (res, red, unbd, mini, res1, res2) = mini\<close>

lemma opts_rel_miminum_between_restart:
  \<open>(opts_rel_miminum_between_restart, opts_minimum_between_restart) \<in> opts_rel \<rightarrow> Id\<close>
  by (auto simp: opts_rel_def intro!: frefI)

fun opts_rel_restart_coeff1 :: \<open>opts_ref \<Rightarrow> 64 word\<close> where
  \<open>opts_rel_restart_coeff1 (res, red, unbd, mini, res1, res2) = res1\<close>

lemma opts_rel_restart_coeff1:
  \<open>(opts_rel_restart_coeff1, opts_restart_coeff1) \<in> opts_rel \<rightarrow> Id\<close>
  by (auto simp: opts_rel_def intro!: frefI)

fun opts_rel_restart_coeff2 :: \<open>opts_ref \<Rightarrow> nat\<close> where
  \<open>opts_rel_restart_coeff2 (res, red, unbd, mini, res1, res2, target) = res2\<close>

lemma opts_rel_restart_coeff2:
  \<open>(opts_rel_restart_coeff2, opts_restart_coeff2) \<in> opts_rel \<rightarrow> Id\<close>
  by (auto simp: opts_rel_def intro!: frefI)

fun opts_rel_target :: \<open>opts_ref \<Rightarrow> 3 word\<close> where
  \<open>opts_rel_target (res, red, unbd, mini, res1, res2, target) = target\<close>

lemma opts_rel_target:
  \<open>(opts_rel_target, opts_target) \<in> opts_rel \<rightarrow> Id\<close>
  by (auto simp: opts_rel_def intro!: frefI)

lemma opts_rel_alt_defs:
  \<open>RETURN o opts_rel_restart = (\<lambda>(res, red, unbd, mini, res1, res2). RETURN res)\<close>
  \<open>RETURN o opts_rel_reduce = (\<lambda>(res, red, unbd, mini, res1, res2). RETURN red)\<close>
  \<open>RETURN o opts_rel_unbounded_mode = (\<lambda>(res, red, unbd, mini, res1, res2). RETURN unbd)\<close>
  \<open>RETURN o opts_rel_miminum_between_restart = (\<lambda>(res, red, unbd, mini, res1, res2). RETURN mini)\<close>
  \<open>RETURN o opts_rel_restart_coeff1 = (\<lambda>(res, red, unbd, mini, res1, res2). RETURN res1)\<close>
  \<open>RETURN o opts_rel_restart_coeff2 = (\<lambda>(res, red, unbd, mini, res1, res2, _). RETURN res2)\<close>
  \<open>RETURN o opts_rel_target = (\<lambda>(res, red, unbd, mini, res1, res2, target). RETURN target)\<close>
  by (auto intro!: ext)

end