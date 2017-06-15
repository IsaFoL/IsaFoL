theory CDCL_Two_Watched_Literals_VMTF
imports Main
begin

type_synonym 'v abs_vmtf = \<open>'v set \<times> 'v set\<close>
type_synonym 'v abs_vmtf_remove = \<open>'v abs_vmtf \<times> 'v set\<close>

subsection \<open>Variable-Move-to-Front\<close>

subsubsection \<open>Specification\<close>

datatype 'v vmtf_atm = VMTF_ATM (stamp : nat) (get_prev: \<open>nat option\<close>) (get_next: \<open>nat option\<close>)


inductive vmtf :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat vmtf_atm list \<Rightarrow> bool\<close> where
Nil: \<open>vmtf [] st xs\<close> |
Cons1: \<open>a < length xs \<Longrightarrow> m \<ge> n \<Longrightarrow> xs ! a = VMTF_ATM (n::nat) None None \<Longrightarrow> vmtf [a] m xs\<close> |
Cons: \<open>vmtf (b # l) m xs \<Longrightarrow> a < length xs \<Longrightarrow> xs ! a = VMTF_ATM n None (Some b) \<Longrightarrow>
  a \<noteq> b \<Longrightarrow> a \<notin> set l \<Longrightarrow> n > m \<Longrightarrow> xs' = xs[b := VMTF_ATM (stamp (xs!b)) (Some a) (get_next (xs!b))] \<Longrightarrow>
    n' >= n \<Longrightarrow>
  vmtf (a # b # l) n' xs'\<close>

inductive_cases vmtfE: \<open>vmtf xs st ys\<close>

lemma vmtf_le_length: \<open>vmtf l m xs \<Longrightarrow> i \<in> set l \<Longrightarrow> i < length xs\<close>
  apply (induction rule: vmtf.induct)
  subgoal by (auto intro: vmtf.intros)
  subgoal by (auto intro: vmtf.intros)
  subgoal by (auto intro: vmtf.intros)
  done

lemma vmtf_distinct: \<open>vmtf l m xs \<Longrightarrow> distinct l\<close>
  apply (induction rule: vmtf.induct)
  subgoal by (auto intro: vmtf.intros)
  subgoal by (auto intro: vmtf.intros)
  subgoal by (auto intro: vmtf.intros)
  done

lemma vmtf_eq_iff:
  assumes
    \<open>\<forall>i \<in> set l. xs ! i = ys ! i\<close> and
    \<open>\<forall>i \<in> set l. i < length xs \<and> i < length ys\<close>
  shows \<open>vmtf l m ys \<longleftrightarrow> vmtf l m xs\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have \<open>vmtf l m xs\<close>
    if
      \<open>vmtf l m ys\<close> and
      \<open>(\<forall>i \<in> set l. xs ! i = ys ! i)\<close> and
      \<open>(\<forall>i \<in> set l. i < length xs \<and> i < length ys)\<close>
    for xs ys
    using that
  proof (induction arbitrary: xs rule: vmtf.induct)
    case (Nil st xs zs)
    then show ?case by (auto intro: vmtf.intros)
  next
    case (Cons1 a xs n zs)
    show ?case by (rule vmtf.Cons1) (use Cons1 in \<open>auto intro!: intro: vmtf.intros\<close>)
  next
    case (Cons b l m xs c n ys n' zs) note vmtf = this(1) and a_le_y = this(2) and ys_a = this(3) and
      ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and nn' = this(8) and IH = this(9) and H = this(10-)
    have \<open>vmtf (c # b # l) n' ys\<close>
      by (rule vmtf.Cons[OF Cons.hyps])
    have [simp]: \<open>b < length xs\<close>  \<open>b < length zs\<close>
      using H xs' by auto
    have [simp]: \<open>b \<notin> set l\<close>
      using vmtf_distinct[OF vmtf] by auto
    then have K: \<open>\<forall>i\<in>set l. zs ! i = (if b = i then x else xs ! i) =
       (\<forall>i\<in>set l. zs ! i = xs ! i)\<close> for x
       using H(2)
       by (simp add: H(1) nth_list_update xs')
    have next_xs_b: \<open>get_next (xs ! b) = None\<close> if \<open>l = []\<close>
      using vmtf unfolding that by (auto simp: elim!: vmtfE)
    have prev_xs_b: \<open>get_prev (xs ! b) = None\<close>
      using vmtf by (auto elim: vmtfE)
    have vmtf_zs: \<open>vmtf (b # l) m (zs[b := xs!b])\<close>
      apply (rule IH)
      subgoal using H(1) ab next_xs_b prev_xs_b unfolding xs' by (auto simp: nth_list_update K)
      subgoal using H(2) ab next_xs_b prev_xs_b unfolding xs' by (auto simp: nth_list_update K)
      done
    show ?case
      apply (rule vmtf.Cons[OF vmtf_zs, of _ n])
      subgoal using a_le_y xs' H(2) by auto
      subgoal using ab ys_a xs' H(1) by (auto simp: nth_list_update K)
      subgoal using ab .
      subgoal using a_l .
      subgoal using mn .
      subgoal using ab xs' H(1) by (cases \<open>xs ! b\<close>)  (auto simp: nth_list_update eq_commute[of \<open>zs ! b\<close>])
      subgoal using nn' .
      done
  qed
  then show ?thesis
    using assms by metis
qed

lemma vmtf_stamp_increase: \<open>vmtf xs p ys \<Longrightarrow> p \<le> p' \<Longrightarrow> vmtf xs p' ys\<close>
  apply (induction rule: vmtf.induct)
  subgoal by (auto intro: vmtf.intros)
  subgoal by (rule vmtf.Cons1) (auto intro!: vmtf.intros)
  subgoal by (auto intro: vmtf.intros)
  done

definition vmtf_dequeue where
\<open>vmtf_dequeue xs x =
  (let x = xs ! x;
    update_prev = \<lambda>xs.
      (case get_prev x of None \<Rightarrow> xs
      | Some a \<Rightarrow> xs[a:= VMTF_ATM (stamp (xs!a)) (get_prev (xs!a)) (get_next x)]);
    update_next = \<lambda>xs.
      (case get_next x of None \<Rightarrow> xs
      | Some a \<Rightarrow> xs[a:= VMTF_ATM (stamp (xs!a)) (get_prev x) (get_next (xs!a))])
    in
  update_next (update_prev xs))
  \<close>
lemma vmtf_different_same_neq: \<open>vmtf (b # c # l') m xs \<Longrightarrow> vmtf (c # l') m xs \<Longrightarrow> False\<close>
  apply (cases l')
   apply (force elim: vmtfE)
  apply (subst (asm) vmtf.simps)
  apply (subst (asm)(2) vmtf.simps)
  apply auto (* TODO Proof *)
  by (metis length_list_update nth_list_update_eq nth_list_update_neq option.distinct(1) vmtf_atm.sel(2))

lemma
  assumes \<open>vmtf l m xs\<close> and \<open>x \<in> set l\<close>
  shows \<open>vmtf (remove1 x l) m (vmtf_dequeue xs x)\<close>
  using assms(1,2)
proof (induction rule: vmtf.induct)
  case (Nil st xs)
  then show ?case by (auto intro: vmtf.intros)
next
  case (Cons1 a xs n)
  then have vmtf: \<open>vmtf (remove1 x [a]) n xs\<close>
      by (auto intro!: vmtf.intros)
  then show ?case
    apply  (cases \<open>x = a\<close>)
    subgoal
      by (auto intro!: vmtf.intros)
    subgoal using Cons1
      by (auto intro: vmtf.intros simp: vmtf_dequeue_def Let_def split: option.splits)
    done
next
  case (Cons b l m xs a n xs' n'') note vmtf = this(1) and a_le_y = this(2) and ys_a = this(3) and
      ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and nn' = this(8) and IH = this(9) and H = this(10-)

  have [simp]: \<open>b < length xs\<close>
    using vmtf_le_length[OF vmtf] by auto
  have xs_b: \<open>xs ! b = VMTF_ATM (stamp (xs ! b)) None (get_next (xs ! b))\<close>
    using vmtf by (auto elim: vmtfE)
  have \<open>xs[b := VMTF_ATM (stamp (xs ! b)) None (get_next (xs ! b))] = xs\<close>
    unfolding xs_b[symmetric] by simp
  have [simp]: \<open>length (vmtf_dequeue xs' b) = length xs'\<close> for xs' b
    by (auto simp: vmtf_dequeue_def Let_def split: option.splits)
  show ?case
  proof (cases \<open>x = a\<close>)
    case True
    then show ?thesis
      using Cons vmtf by (auto simp: vmtf_dequeue_def Let_def nth_list_update xs_b[symmetric] split: option.splits
        intro: vmtf_stamp_increase)
  next
    case xa: False
    have \<open>vmtf (remove1 x (b # l)) m (vmtf_dequeue xs x)\<close>
      by (rule IH) (use xa H in auto)
    have \<open>vmtf (a # l) n'' (vmtf_dequeue xs' b)\<close>
      if \<open>a \<noteq> b\<close> and vmtf_l: \<open>vmtf l m xs\<close>
    proof (cases l)
      case Nil
      show ?thesis
        unfolding Nil
        apply (rule vmtf.intros(2)[of _ _ \<open>stamp (xs ! a)\<close>])
        subgoal using a_le_y xs' mn nn' by simp
        subgoal using mn nn' vmtf ys_a by simp
        subgoal using vmtf a_le_y that ys_a
          by (auto elim!: vmtfE simp: vmtf_dequeue_def Let_def xs' nth_list_update Nil)
        done
    next
      case (Cons c l')
      note vmtf' = vmtf_l[unfolded Cons]

      have [simp]: \<open>get_next (xs ! b) = Some c\<close> \<open>get_prev (xs ! b) = None\<close>
        using vmtf unfolding Cons
        by (auto elim: vmtfE  simp: vmtf_dequeue_def Let_def xs' nth_list_update )
      show ?thesis
        unfolding Cons
        apply (rule vmtf.Cons[OF vmtf', of _ n])
        subgoal using a_le_y by simp
        subgoal using vmtf a_le_y that ys_a a_l unfolding Cons
          by (auto elim!:  simp: vmtf_dequeue_def Let_def xs' nth_list_update
              dest: vmtf_different_same_neq)
        subgoal using a_l unfolding Cons by simp
        subgoal using a_l unfolding Cons by simp
        subgoal using mn .
        subgoal using ab a_le_y a_l unfolding Cons xs'
               apply (auto simp: vmtf_dequeue_def Let_def nth_list_update)
          sorry
        sorry
    qed

    show ?thesis
      apply (cases \<open>x = b\<close>)
      using xa vmtf
      apply simp_all


     sorry
  qed

oops

context twl_array_code_ops
begin

paragraph \<open>Invariants\<close>

text \<open>Invariants
  \<^item> The atoms are always disjoint.
  \<^item> The atoms of \<^term>\<open>ys\<close> are \<^emph>\<open>always\<close> set.
  \<^item> The atoms of \<^term>\<open>zs\<close> are \<^emph>\<open>never\<close> set and have been remove from \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close>.
  \<^item> The atoms of \<^term>\<open>xs\<close> \<^emph>\<open>can be\<close> set but do not have to.
\<close>

definition abs_vmtf_remove_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf_remove \<Rightarrow> bool\<close> where
\<open>abs_vmtf_remove_inv M \<equiv> \<lambda>((xs, ys), zs).
  (\<forall>L\<in>ys. L \<in> atm_of ` lits_of_l M) \<and>
  xs \<inter> ys = {} \<and>
  xs \<inter> zs = {} \<and>
  ys \<inter> zs = {} \<and>
  xs \<union> ys \<union> zs = atms_of N\<^sub>1 \<and>
  (\<forall>L\<in>zs. L \<in> atm_of ` lits_of_l M) \<and>
  finite xs \<and> finite ys \<and> finite zs
  \<close>

abbreviation abs_vmtf_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf \<Rightarrow> bool\<close> where
\<open>abs_vmtf_inv M vm \<equiv> abs_vmtf_remove_inv M (vm, {})\<close>


paragraph \<open>Operations\<close>

fun abs_vmtf_bump :: \<open>nat literal \<Rightarrow> nat abs_vmtf_remove \<Rightarrow> nat abs_vmtf_remove\<close> where [simp del]:
\<open>abs_vmtf_bump L ((xs, ys), zs) = ((xs - {atm_of L}, ys - {atm_of L}), insert (atm_of L) zs)\<close>

fun abs_vmtf_bump_flush :: \<open>nat abs_vmtf_remove \<Rightarrow> nat abs_vmtf_remove\<close> where [simp del]:
\<open>abs_vmtf_bump_flush ((xs, ys), zs) = ((xs, ys \<union> zs), {})\<close>

lemmas abs_vmtf_bump_flush_def = abs_vmtf_bump_flush.simps
lemmas abs_vmtf_bump_def = abs_vmtf_bump.simps


lemma abs_vmtf_remove_inv_abs_vmtf_bump:
  assumes \<open>L \<in># N\<^sub>1\<close> and \<open>abs_vmtf_remove_inv M vm\<close> and \<open>defined_lit M L\<close>
  shows \<open>abs_vmtf_remove_inv M (abs_vmtf_bump L vm)\<close>
  using assms by (fastforce simp: abs_vmtf_remove_inv_def abs_vmtf_bump_def Decided_Propagated_in_iff_in_lits_of_l
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of lits_of_def uminus_lit_swap)

lemma abs_vmtf_remove_inv_abs_vmtf_bump_flush:
  assumes \<open>abs_vmtf_remove_inv M vm\<close>
  shows \<open>abs_vmtf_remove_inv M (abs_vmtf_bump_flush vm)\<close>
  using assms by (auto simp: abs_vmtf_remove_inv_def abs_vmtf_bump_flush_def Decided_Propagated_in_iff_in_lits_of_l
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of)


definition abs_vmtf_unset :: \<open>nat literal \<Rightarrow> nat abs_vmtf \<Rightarrow> nat abs_vmtf nres\<close> where
\<open>abs_vmtf_unset L \<equiv> \<lambda>(xs, ys). do {
    if atm_of L \<in> ys
    then do {
        ys' \<leftarrow> SPEC (\<lambda>ys'. ys' \<subseteq> ys \<and> atm_of L \<in> ys');
        RETURN (xs \<union> ys', ys-ys')
    }
    else RETURN (xs, ys)
  }\<close>

lemma abs_vmtf_remove_inv_abs_vmtf_unset:
  assumes \<open>abs_vmtf_inv M vm\<close> and \<open>undefined_lit M L\<close>
  shows \<open>abs_vmtf_unset L vm \<le> SPEC (abs_vmtf_inv M)\<close>
  using assms unfolding abs_vmtf_unset_def
  apply (cases vm)
  apply clarify
  apply refine_vcg
  by (fastforce simp: abs_vmtf_remove_inv_def abs_vmtf_bump_def Decided_Propagated_in_iff_in_lits_of_l
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of lits_of_def uminus_lit_swap)

definition abs_vmtf_find_next :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf \<Rightarrow> (nat option \<times> nat abs_vmtf) nres\<close> where
\<open>abs_vmtf_find_next M vm = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(L, vm).
       (L = None \<longrightarrow> abs_vmtf_inv M vm) \<and>
       (L \<noteq> None \<longrightarrow> (abs_vmtf_inv (Decided (Pos (the L)) # M) vm \<and> undefined_lit M (Pos (the L))))\<^esup>
      (\<lambda>(x, (xs, ys)). x = None \<and> xs \<noteq> {})
      (\<lambda>(x, (xs, ys)). do {
          ASSERT(xs \<noteq> {});
          x \<leftarrow> SPEC(\<lambda>x. x \<in> xs);
          if undefined_lit M (Pos x) then RETURN (Some x, (xs - {x}, insert x ys))
          else RETURN (None, (xs - {x}, insert x ys))
      })
      (None, vm)
  }\<close>

lemma abs_vmtf_remove_inv_abs_vmtf_find_next:
  assumes \<open>abs_vmtf_inv M vm\<close>
  shows \<open>abs_vmtf_find_next M vm \<le> SPEC (\<lambda>(L, vm).
      (L = None \<longrightarrow> (abs_vmtf_inv M vm \<and> (\<forall>L\<in>#N\<^sub>1. defined_lit M L))) \<and>
      (L \<noteq> None \<longrightarrow> (abs_vmtf_inv (Decided (Pos (the L)) # M) vm \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  have body_defined_abs: \<open>abs_vmtf_inv M' vm'\<close>
    if  \<open>abs_vmtf_inv M vm\<close> and \<open>M' = M\<close> and
        \<open>vm' = (xs - {L}, insert L ys)\<close> and
        \<open>vm = (xs, ys)\<close> and
        def_L: \<open>\<not>undefined_lit M (Pos L)\<close> and
        \<open>L \<in> xs\<close>
    for vm vm' xs ys M M' L
    proof -
        have \<open>L \<in> atm_of ` lits_of_l M\<close>
        using def_L by (metis (full_types) Decided_Propagated_in_iff_in_lits_of_l atm_of_uminus
            image_iff literal.sel(1))
        then show ?thesis
        using that by (auto simp: abs_vmtf_remove_inv_def)
    qed
  show ?thesis
    using assms unfolding abs_vmtf_find_next_def
    apply (cases vm)
    apply clarify
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(x, (xs, ys)). card xs)\<close>])
    subgoal by auto -- \<open>well-foundedness\<close>
    subgoal by auto -- \<open>WHILE inital round\<close>
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (auto simp: abs_vmtf_remove_inv_def) -- \<open>body if undefined\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def)
    subgoal by auto
    subgoal by (simp add:  abs_vmtf_remove_inv_def abs_vmtf_remove_inv_def card_Diff1_less
        del: card_Diff_singleton card_Diff_subset card_Diff_singleton card_Diff_insert) -- \<open>Termination\<close>
    subgoal by (rule body_defined_abs) simp_all+ -- \<open>body if defined\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def)
    subgoal by (auto simp: abs_vmtf_remove_inv_def)
    subgoal by (simp add:  abs_vmtf_remove_inv_def abs_vmtf_remove_inv_def card_Diff1_less
        del: card_Diff_singleton card_Diff_subset card_Diff_singleton card_Diff_insert)-- \<open>Termination\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def) --\<open>final theorem\<close>
    subgoal by (auto simp: abs_vmtf_remove_inv_def Decided_Propagated_in_iff_in_lits_of_l
        atm_of_in_atm_of_set_in_uminus atms_of_def dest!: atm_of_in_atm_of_set_in_uminus)
    subgoal by fast
    subgoal by fast
    done
qed

lemma abs_vmtf_remove_inv_change_hd:
  assumes \<open>atm_of (lit_of L) = atm_of (lit_of L')\<close>
  shows \<open>abs_vmtf_remove_inv (L # M) (vm, {}) \<longleftrightarrow> abs_vmtf_remove_inv (L' # M) (vm, {})\<close>
  using assms by (auto simp: abs_vmtf_remove_inv_def)

end


subsubsection \<open>Implementation\<close>

datatype (in-) 'v vmtf_atm = VMTF_ATM (stamp : nat) (get_prev: \<open>nat option\<close>) (get_next: \<open>nat option\<close>)

type_synonym (in -) 'v vmtf_atms = \<open>'v vmtf_atm list \<times> nat \<times> nat\<close>

abbreviation vmtf_fst :: \<open>'v vmtf_atms \<Rightarrow> nat\<close> where
\<open>vmtf_fst \<equiv> \<lambda>(a, b, c). b\<close>

abbreviation vmtf_last :: \<open>'v vmtf_atms \<Rightarrow> nat\<close> where
\<open>vmtf_last \<equiv> \<lambda>(a, b, c). c\<close>

abbreviation vmtf_get :: \<open>'v vmtf_atms \<Rightarrow> nat \<Rightarrow> 'v vmtf_atm\<close> where
\<open>vmtf_get \<equiv> \<lambda>(a, b, c) i. a!i\<close>

fun  (in -) option_pred where
\<open>option_pred P None = True\<close> |
\<open>option_pred P (Some a) = P a\<close>

definition vtmf_atms_invs :: \<open>'v vmtf_atms \<Rightarrow> bool\<close> where
\<open>vtmf_atms_invs == \<lambda>(atms, fst, last).
   (\<forall>i<length atms. option_pred (\<lambda>j. j < length atms) (get_prev (atms!i))) \<and>
   (\<forall>i<length atms. option_pred (\<lambda>j. j < length atms) (get_next (atms!i))) \<and>

   (\<forall>i<length atms. option_pred (\<lambda>j. get_next (atms!j) = Some i) (get_prev (atms!i))) \<and>
   (\<forall>i<length atms. option_pred (\<lambda>j. get_prev (atms!j) = Some i) (get_next (atms!i)))
\<close>

end