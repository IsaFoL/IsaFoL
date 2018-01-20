theory Watched_Literals_Watch_List_Initialisation
  imports Watched_Literals_Watch_List Watched_Literals_Initialisation
begin


subsection \<open>Initialisation\<close>

fun calculate_correct_watching
  :: \<open>'v clauses_l \<Rightarrow> ('v literal \<Rightarrow> watched) \<Rightarrow> nat \<Rightarrow> ('v literal \<Rightarrow> watched)\<close> where
  \<open>calculate_correct_watching [] W _ = W\<close>
| \<open>calculate_correct_watching (C # N) W i =
     (let W = calculate_correct_watching N W (Suc i) in
     if C = []
     then W
     else
       if tl C = []
       then
         W(hd C:= i # W (hd C))
       else
         W(hd C:= i # W (hd C), hd (tl C):= i # W (hd (tl C)))
   )\<close>

lemma image_mset_Suc: \<open>Suc `# {#C \<in># M. P C#} = {#C \<in># Suc `# M. P (C-1)#}\<close>
  by (induction M) auto

lemma clause_to_update_def2:
  \<open>clause_to_update L (M, C # N, U, D, NE, UE, {#}, {#}) =
    image_mset Suc (filter_mset
      (\<lambda>C::nat. L \<in> set (watched_l (N!C)))
      (mset [0..<length N]))\<close>
proof -
  have 1: \<open>Suc `# mset [0..<length N] =  mset [1..<Suc (length N)]\<close>
    unfolding mset_map[symmetric]
    using map_add_upt[of 1 \<open>length N\<close>] by force
  show ?thesis
    unfolding clause_to_update_def image_mset_Suc 1 get_clauses_l.simps length_Cons
    by (rule filter_mset_cong) (auto split: if_splits)
qed

lemma clause_to_update_Cons: \<open>clause_to_update L (M, C # C' # N, U, D, NE, UE, {#}, {#}) =
         (if L \<in> set (watched_l C') then {#1#} else {#}) +
         Suc `# clause_to_update L (M, C # N, U, D, NE, UE, {#}, {#})\<close> for L C
proof -
  define dont_be_silly where
    \<open>dont_be_silly L = {#C \<in># mset [0..<length N]. L \<in> set (watched_l (N ! C))#}\<close> for L
  have [simp]: \<open>Suc `# mset_set {a..<b} = mset_set {Suc a..<Suc b}\<close> for a b
    by (simp add: image_mset_mset_set)
  have 1: \<open>mset [0..<Suc (length N)] = add_mset 0 (mset [1..<Suc (length N)])\<close>
    by (subst upt_conv_Cons) auto
  have 2: \<open>{#C \<in># mset [1..<Suc (length N)].
            L \<in> set (watched_l ((C' # N) ! C))#} = Suc `# {#C \<in># mset [0..<length N].
            L \<in> set (watched_l (N ! C))#}\<close> for L
    unfolding image_mset_Suc
    by (rule filter_mset_cong_inner_outer) (auto split: if_splits simp: atLeastLessThanSuc)
  show ?thesis
    unfolding clause_to_update_def2 length_Cons mset.simps filter_mset_add_mset 1
    unfolding dont_be_silly_def[symmetric] 2
    by auto
qed

lemma calculate_correct_watching:
   \<open>mset ((calculate_correct_watching N (\<lambda>_. []) i) L) =
           image_mset (\<lambda>n. n+i-1) (clause_to_update L (M, C # N, U, D, NE, UE, {#}, {#}))\<close>
proof -
  show ?thesis
  proof (induction N arbitrary: i L)
    case Nil
    then show ?case by (auto simp: clause_to_update_def)
  next
    case (Cons C N)
    consider
      (Nil) \<open>C = []\<close> |
      (C1) K where \<open>C = [K]\<close> |
      (C2) K K' C' where \<open>C = K # K' # C'\<close>
      by (cases C; cases \<open>tl C\<close>) auto
    then show ?case
    proof cases
      case Nil note C = this
      show ?thesis
        using Cons C
        by (simp add: clause_to_update_Cons Let_def)
    next
      case C1 note C = this
      show ?thesis
        by (auto simp add: C Let_def Cons clause_to_update_Cons)
    next
      case C2
      then show ?thesis
        using Cons by (simp add: clause_to_update_Cons Let_def)
    qed
  qed
qed

lemma twl_struct_invs_init_twl_struct_invs:
  \<open>snd S = {#} \<Longrightarrow> twl_struct_invs_init S \<longleftrightarrow> twl_struct_invs (fst S)\<close>
  by (cases S) (auto simp: twl_struct_invs_def twl_struct_invs_init_def)

(* TODO Kill?

subsection \<open>Final Theorem with Initialisation\<close>

fun init_wl_of :: \<open>'v twl_st_l\<Rightarrow> 'v twl_st_wl\<close> where
  \<open>init_wl_of (M, N, U, D, NE, UE, _, Q) =
       ((M, N, U, D, NE, UE, Q, calculate_correct_watching (tl N) (\<lambda>_. []) 1))\<close>


theorem init_dt_wl:
  fixes CS S
  defines S\<^sub>0: \<open>S\<^sub>0 \<equiv> (([], [[]], 0, None, {#}, {#}, {#}, {#}), {#})\<close>
  defines S: \<open>S \<equiv>  init_wl_of (fst (init_dt CS S\<^sub>0))\<close>
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    no_confl: \<open>get_conflict_wl S = None\<close> and
    snd_init: \<open>snd (init_dt CS S\<^sub>0) = {#}\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le> SPEC (\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
             (state\<^sub>W_of (twl_st_of_wl None S))
             (state\<^sub>W_of (twl_st_of_wl None T)))\<close>
proof -
  obtain M N U D NE UE WS Q OC where
    init: \<open>init_dt CS S\<^sub>0 = ((M, N, U, D, NE, UE, WS, Q), OC)\<close>
    by (cases \<open>init_dt CS S\<^sub>0\<close>) auto
  have \<open>N \<noteq> []\<close>
    using clauses_init_dt_not_Nil[of CS \<open>snd S\<^sub>0\<close>] init unfolding S\<^sub>0 by auto
  then have corr_w: \<open>correct_watching S\<close>
    unfolding S init
    by (auto simp: correct_watching.simps
        calculate_correct_watching[of _ _ _ M \<open>hd N\<close> U D NE UE])
  have
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S)) = mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>twl_list_invs (st_l_of_wl None S)\<close>
    unfolding S S\<^sub>0
    subgoal
      using init_dt(1)[OF dist] snd_init
        by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 twl_struct_invs_init_twl_struct_invs)
    subgoal
      using init_dt(2)[OF dist] snd_init
      by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 clauses_def)
    subgoal
      using init_dt(3)[OF dist] snd_init
      by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 clauses_def)
    subgoal
      using init_dt(5)[OF dist]
      by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 clauses_def twl_list_invs_def)
    don
  from cdcl_twl_stgy_prog_wl_spec_final2[OF this(1,3) no_confl this(4) corr_w]
  show ?thesis
    .
qed

*)
end
