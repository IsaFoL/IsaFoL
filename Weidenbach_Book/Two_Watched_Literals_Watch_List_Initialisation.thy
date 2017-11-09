theory Two_Watched_Literals_Watch_List_Initialisation
  imports Two_Watched_Literals_Initialisation
begin

section \<open>Third Refinement: Remembering watched\<close>

subsection \<open>Types\<close>

type_synonym clauses_to_update_wl = "nat multiset"
type_synonym watched = "nat list"
type_synonym 'v lit_queue_wl = "'v literal multiset"

type_synonym 'v twl_st_wl =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl \<times>
    ('v literal \<Rightarrow> watched)"

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
  \<open>clause_to_update L (M, C # N, U, D, NP, UP, {#}, {#}) =
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

lemma clause_to_update_Cons: \<open>clause_to_update L (M, C # C' # N, U, D, NP, UP, {#}, {#}) =
         (if L \<in> set (watched_l C') then {#1#} else {#}) +
         Suc `# clause_to_update L (M, C # N, U, D, NP, UP, {#}, {#})\<close> for L C
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
           image_mset (\<lambda>n. n+i-1) (clause_to_update L (M, C # N, U, D, NP, UP, {#}, {#}))\<close>
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

end