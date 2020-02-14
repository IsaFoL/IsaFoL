theory Theory_Intf
  imports CDCL.CDCL_W_Abstract_State
begin

datatype 'v theory_status = Conflict \<open>'v\<close> | Updated

section \<open>Theory as black box for CDCL\<close>

text \<open>

  This is the very abstract view on a theory as we want to use to express a formal CDCL(T).  We
  abstract over everything. In particular, we do not need to know whether there is a single theory
  or several one. A combination like Nelson-Open would appear as an instance of this locale too.

  The CDCL cares about the following properties:

  \<^item> If a total model is found, there is either a refutation or the theory is happy with it. If this
  is not possible to reach, CDCL cannot do much.

  \<^item> A conflict is a subset of the current trail (i.e., conflicts are not expressed using new
  literals) and a conflict is entailed by the set of clause.


  For correctness of CDCL(T), we need that the SAT clauses are satisfiable if the set of theory
  constraints is also satisfiable (i.e., if CDCL cannot find a model, there is none).  This is the
  correctness of the construction of the initial clauses that are given to the SAT solver. However,
  CDCL does not care about that.

  The assumption \<^text>\<open>entail_mono\<close> is an artefact from the fact that we do not care at all the notion
  of theory entailement. It might be possible to write it better (or even define entailment more
  generally) and reduce some of the mess we have.
\<close>

locale theory_problem =
  fixes
    theory_entails_set :: \<open>'a \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 90) and
    theory_entails :: \<open>'v literal set \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 90)
  assumes
    entail_mono: \<open>N \<Turnstile>\<^sub>\<T>\<^sub>s N' \<Longrightarrow> N \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> N \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N'\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N' \<Longrightarrow> I \<Turnstile>sm N' \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> N \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> N \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> atms_of C \<subseteq> atm_of ` I \<and> C \<in> simple_clss (atm_of ` I))\<close>and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N' \<Longrightarrow> N \<Turnstile>\<^sub>\<T>\<^sub>s N' \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> N \<Longrightarrow> satisfiable (set_mset N')\<close>


section \<open>Theory as black box for solving\<close>

text \<open>

  This is also a very abstract view on theories, but this time, we talk about theories as a black
  box for a SAT solver. This is rather different from the abstract view as we want to make more it
  practical.
\<close>
type_synonym ('v, 'theory) e_theory = \<open>(('v, 'v clause) ann_lits \<times> 'theory)\<close>

text \<open>We distinguish between cheap checks (inform) and expensive and complete checks
(\<^text>\<open>full_check\<close>).
Missing:
  \<^enum> properties on restore/save
  \<^enum> invariants
\<close>
locale theory_checker =
  fixes
    inform :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'theory \<Rightarrow> 'theory \<times> 'v clause theory_status\<close> and
    full_check :: \<open>'theory \<Rightarrow> 'theory \<times> 'v clause theory_status\<close> and
    save_state :: \<open>'theory \<Rightarrow> 'saved_state\<close> and
    restore_state :: \<open>'saved_state \<Rightarrow> 'theory \<Rightarrow> 'theory\<close> and
    trail :: \<open>'theory \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    checked :: \<open>'theory \<Rightarrow> bool\<close>
  assumes
    real_conflict_inform: \<open>inform L \<T> = (\<T>', Conflict C) \<Longrightarrow> trail \<T>' \<Turnstile>as CNot C\<close> and
    real_conflict_full_check: \<open>full_check \<T> = (\<T>', Conflict C) \<Longrightarrow> trail \<T>' \<Turnstile>as CNot C\<close> and
    trail_inform: \<open>trail (fst (inform L \<T>)) = trail \<T> @ [L]\<close> and
    restore_save: \<open>checked S \<Longrightarrow> checked T \<Longrightarrow> \<exists>M. trail T = trail S @ M \<Longrightarrow>
      trail (restore_state (save_state S) T) = trail S\<close> and
    inform_checked:
      \<open>inform L \<T> = (\<T>', Updated) \<Longrightarrow> checked \<T>'\<close>
begin

fun informAll :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'theory \<Rightarrow> ('v, 'theory) e_theory \<times> 'v clause theory_status\<close> where
  \<open>informAll [] \<T> = (([], \<T>), Updated)\<close> |
  \<open>informAll (L # M) \<T> =
     (case inform L \<T> of
       (\<T>', Updated) \<Rightarrow> informAll M \<T>'
     | (\<T>', Conflict C) \<Rightarrow> ((M, \<T>'), Conflict C))\<close>

lemma real_conflict_informAll:
  \<open>informAll M \<T> = ((M', \<T>'), Conflict C) \<Longrightarrow> trail \<T>' \<Turnstile>as CNot C\<close>
  by (induction M arbitrary: \<T>' C M' \<T>)
    (auto split: prod.splits theory_status.splits dest: real_conflict_inform)

lemma informAll_updated_no_leftovers:
  \<open>informAll M \<T> = ((a, b), Updated) \<Longrightarrow> a = []\<close>
  by (induction M arbitrary: a b \<T>)
    (auto split: prod.splits theory_status.splits list.splits)

lemma informAll_append: \<open>informAll (M @ M') \<T> =
  (case informAll M \<T> of
    ((_, \<T>'), Updated) \<Rightarrow>  informAll M' \<T>'
   | ((M, \<T>'), Conflict C) \<Rightarrow>  ((M @ M', \<T>'), Conflict C))\<close>
  by (induction M arbitrary: M' \<T>)
   (auto split: prod.splits theory_status.splits list.splits
    dest: informAll_updated_no_leftovers )

lemma trail_informAll: \<open>trail (snd (fst (informAll M \<T>))) @ fst (fst (informAll M \<T>)) = trail \<T> @ M\<close>
  apply (induction M arbitrary: \<T> rule: rev_induct)
  subgoal by auto
  subgoal premises p for L M \<T>
    using p[of \<T>] trail_inform[of L \<open>snd (fst (informAll M \<T>))\<close>]
      informAll_updated_no_leftovers[of M \<T> \<open>fst (fst (informAll M \<T>))\<close> \<open>snd (fst (informAll M \<T>))\<close>]
    by (auto split: prod.splits theory_status.splits
      simp: informAll_append dest:  dest: real_conflict_inform)
  done

end


text \<open>Here, we add another ever cheaper check as even the simple check is too expensive for
the propagation loop. During refinement, it is better to keep the trail implicit (by saving
how many literals are known to the theory part instead of keeping an explicit trail in the theory
part too).\<close>

locale theory_checker_impl =
  theory_checker inform full_check save_state restore_state trail checked
  for
    inform :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'theory \<Rightarrow> 'theory \<times> 'v clause theory_status\<close> and
    full_check :: \<open>'theory \<Rightarrow> 'theory \<times> 'v clause theory_status\<close> and
    save_state :: \<open>'theory \<Rightarrow> 'saved_state\<close> and
    restore_state :: \<open>'saved_state \<Rightarrow> 'theory \<Rightarrow> 'theory\<close> and
    trail :: \<open>'theory \<Rightarrow> ('v, 'v clause) ann_lits\<close>  and
    checked :: \<open>'theory \<Rightarrow> bool\<close> +
  fixes
    cheap_inform :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'theory \<Rightarrow> 'theory \<times> 'v clause theory_status\<close>
  assumes
    real_conflict_inform: \<open>inform L \<T> = (\<T>', Conflict C) \<Longrightarrow> trail \<T>' \<Turnstile>as CNot C\<close>
begin

end


context theory_checker
begin


fun cheap_inform_m :: \<open>('v, 'v clause) ann_lit \<Rightarrow>  ('v, 'theory) e_theory \<Rightarrow>
  ('v, 'theory) e_theory \<times> 'v clause theory_status\<close> where
  \<open>cheap_inform_m L (M, \<T>) = ((M @ [L], \<T>), Updated)\<close>

fun inform_m :: \<open>('v, 'v clause) ann_lit \<Rightarrow> ('v, 'theory) e_theory \<Rightarrow>
   ('v, 'theory) e_theory \<times> 'v clause theory_status\<close> where
  \<open>inform_m L (M, \<T>) = informAll (M @ [L]) \<T>\<close>

fun full_check_m :: \<open> ('v, 'theory) e_theory \<Rightarrow>
   ('v, 'theory) e_theory \<times> 'v clause theory_status\<close> where
  \<open>full_check_m (M, \<T>) = (case informAll M \<T> of (\<T>', Conflict C) \<Rightarrow> (\<T>', Conflict C)
     | ((_, \<T>'), Updated) \<Rightarrow> (\<lambda>(a, b). (([], a), b)) (full_check \<T>'))\<close>

fun save_state_m :: \<open>('v, 'theory) e_theory \<Rightarrow> 'saved_state\<close> where
  \<open>save_state_m (M, \<T>) = save_state \<T>\<close>

fun restore_state_m :: \<open>'saved_state \<Rightarrow> ('v, 'theory) e_theory \<Rightarrow>  ('v, 'theory) e_theory\<close> where
  \<open>restore_state_m k (M, \<T>)= (M, restore_state k \<T>)\<close>

fun trail_m :: \<open>('v, 'theory) e_theory \<Rightarrow> _\<close> where
  \<open>trail_m (M, \<T>) = trail \<T> @ M\<close>

lemma trail_m_def:
  \<open>trail_m = (\<lambda>(a, b). trail b @ a)\<close>
  by (auto)

lemma informAll_Updated_flushed:
  \<open>informAll M \<T> = (\<T>', Updated) \<Longrightarrow> fst \<T>' = []\<close>
  by (induction M arbitrary: \<T> \<T>')
    (auto split: prod.splits theory_status.splits)

lemma informAll_Updated_checked:
  \<open>informAll M \<T> = (\<T>', Updated) \<Longrightarrow> checked \<T> \<Longrightarrow>  checked (snd \<T>')\<close>
  by (induction M arbitrary: \<T> \<T>')
    (auto split: prod.splits theory_status.splits dest: inform_checked)


lemma informAll_Updated_checked':
  \<open>informAll (M @ [L]) \<T> = (\<T>', Updated) \<Longrightarrow> checked (snd \<T>')\<close>
  by (induction M arbitrary: \<T> \<T>')
    (auto split: prod.splits theory_status.splits dest: inform_checked)

fun checked_m :: \<open>('v, 'theory) e_theory \<Rightarrow> bool\<close> where
  \<open>checked_m (M, \<T>) \<longleftrightarrow> M = [] \<and> checked \<T>\<close>

interpretation theory_checker_impl:  theory_checker_impl where
  cheap_inform = cheap_inform_m and
  inform = inform_m and
  full_check = full_check_m and
  save_state = save_state_m and
  restore_state = restore_state_m and
  trail = trail_m and
  checked = checked_m
  apply unfold_locales
  subgoal for L \<T> \<T>' C
    by (cases \<T>'; cases \<T>)
     (auto split: prod.splits theory_status.splits
      simp: true_annots_append_l true_annots_commute
      dest!: real_conflict_inform real_conflict_informAll)
  subgoal for \<T> \<T>' C
    by (cases \<T>'; cases \<T>)
      (auto split: prod.splits theory_status.splits
        simp: true_annots_append_l true_annots_commute
        dest!: real_conflict_inform real_conflict_informAll real_conflict_full_check)
  subgoal for L \<T>
    using trail_inform[of L \<open>snd (fst (informAll (fst \<T> @ [L]) (snd \<T>)))\<close>]
      trail_informAll[of \<open>fst \<T> @ [L]\<close> \<open>snd \<T>\<close>]
    by (cases \<T>)
     (auto split: prod.splits theory_status.splits intro: true_clss_mono_left simp: trail_m_def
      dest: real_conflict_inform real_conflict_informAll real_conflict_full_check)
  subgoal for \<T>' \<T>
    using restore_save[of \<open>snd \<T>'\<close> \<open>snd \<T>\<close>]
    by (cases \<T>; cases \<T>')
     auto
  subgoal for L \<T> \<T>'
    using trail_inform[of L \<open>snd (fst (informAll (fst \<T> @ [L]) (snd \<T>)))\<close>]
      trail_informAll[of \<open>fst \<T> @ [L]\<close> \<open>snd \<T>\<close>]
    by (cases \<T>; cases \<T>')
      (auto dest: informAll_Updated_flushed informAll_Updated_checked')
  done

end

end

