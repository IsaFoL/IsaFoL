theory CDCL_Two_Watched_Literals_VMTF
imports CDCL_Two_Watched_Literals_List_Watched_Domain
begin


declare nth_list_update[simp]


subsection \<open>Variable-Move-to-Front\<close>

subsubsection \<open>Variants around head and last\<close>

definition option_hd :: \<open>'a list \<Rightarrow> 'a option\<close> where
  \<open>option_hd xs = (if xs = [] then None else Some (hd xs))\<close>

lemma option_hd_None_iff[iff]: \<open>option_hd zs = None \<longleftrightarrow> zs = []\<close>
  by (auto simp: option_hd_def)

lemma option_hd_Some_iff[iff]: \<open>option_hd zs = Some y \<longleftrightarrow> (zs \<noteq> [] \<and> y = hd zs)\<close>
  by (auto simp: option_hd_def)

lemma option_hd_Some_hd[simp]: \<open>zs \<noteq> [] \<Longrightarrow> option_hd zs = Some (hd zs)\<close>
  by (auto simp: option_hd_def)

lemma option_hd_Nil[simp]: \<open>option_hd [] = None\<close>
  by (auto simp: option_hd_def)

definition option_last where
\<open>option_last l = (if l = [] then None else Some (last l))\<close>

lemma
  option_last_None_iff[iff]: \<open>option_last l = None \<longleftrightarrow> l = []\<close> \<open>None = option_last l \<longleftrightarrow> l = []\<close> and
  option_last_Some_iff[iff]: \<open>option_last l = Some a \<longleftrightarrow> l \<noteq> [] \<and> a = last l\<close>
    \<open>Some a = option_last l \<longleftrightarrow> l \<noteq> [] \<and> a = last l\<close>
  by (auto simp: option_last_def)

lemma option_last_Some[simp]: \<open>l \<noteq> [] \<Longrightarrow> option_last l = Some (last l)\<close>
  by (auto simp: option_last_def)

lemma option_last_Nil[simp]: \<open>option_last [] = None\<close>
  by (auto simp: option_last_def)

lemma option_last_remove1_not_last:
  \<open>x \<noteq> last xs \<Longrightarrow> option_last xs = option_last (remove1 x xs)\<close>
  by (cases xs rule: rev_cases)
    (auto simp: option_last_def remove1_Nil_iff remove1_append)


subsubsection \<open>Specification\<close>

type_synonym 'v abs_l_vmtf = \<open>'v set \<times> 'v set\<close>
type_synonym 'v abs_l_vmtf_remove = \<open>'v abs_l_vmtf \<times> 'v set\<close>

datatype 'v l_vmtf_atm = l_vmtf_ATM (stamp : nat) (get_prev: \<open>nat option\<close>) (get_next: \<open>nat option\<close>)

inductive l_vmtf :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat l_vmtf_atm list \<Rightarrow> bool\<close> where
Nil: \<open>l_vmtf [] st xs\<close> |
Cons1: \<open>a < length xs \<Longrightarrow> m \<ge> n \<Longrightarrow> xs ! a = l_vmtf_ATM (n::nat) None None \<Longrightarrow> l_vmtf [a] m xs\<close> |
Cons: \<open>l_vmtf (b # l) m xs \<Longrightarrow> a < length xs \<Longrightarrow> xs ! a = l_vmtf_ATM n None (Some b) \<Longrightarrow>
  a \<noteq> b \<Longrightarrow> a \<notin> set l \<Longrightarrow> n > m \<Longrightarrow>
  xs' = xs[b := l_vmtf_ATM (stamp (xs!b)) (Some a) (get_next (xs!b))] \<Longrightarrow> n' \<ge> n \<Longrightarrow>
  l_vmtf (a # b # l) n' xs'\<close>

inductive_cases l_vmtfE: \<open>l_vmtf xs st zs\<close>

lemma l_vmtf_le_length: \<open>l_vmtf l m xs \<Longrightarrow> i \<in> set l \<Longrightarrow> i < length xs\<close>
  apply (induction rule: l_vmtf.induct)
  subgoal by (auto intro: l_vmtf.intros)
  subgoal by (auto intro: l_vmtf.intros)
  subgoal by (auto intro: l_vmtf.intros)
  done

lemma l_vmtf_distinct: \<open>l_vmtf l m xs \<Longrightarrow> distinct l\<close>
  apply (induction rule: l_vmtf.induct)
  subgoal by (auto intro: l_vmtf.intros)
  subgoal by (auto intro: l_vmtf.intros)
  subgoal by (auto intro: l_vmtf.intros)
  done

lemma l_vmtf_eq_iff:
  assumes
    \<open>\<forall>i \<in> set l. xs ! i = zs ! i\<close> and
    \<open>\<forall>i \<in> set l. i < length xs \<and> i < length zs\<close>
  shows \<open>l_vmtf l m zs \<longleftrightarrow> l_vmtf l m xs\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have \<open>l_vmtf l m xs\<close>
    if
      \<open>l_vmtf l m zs\<close> and
      \<open>(\<forall>i \<in> set l. xs ! i = zs ! i)\<close> and
      \<open>(\<forall>i \<in> set l. i < length xs \<and> i < length zs)\<close>
    for xs zs
    using that
  proof (induction arbitrary: xs rule: l_vmtf.induct)
    case (Nil st xs zs)
    then show ?case by (auto intro: l_vmtf.intros)
  next
    case (Cons1 a xs n zs)
    show ?case by (rule l_vmtf.Cons1) (use Cons1 in \<open>auto intro!: intro: l_vmtf.intros\<close>)
  next
    case (Cons b l m xs c n zs n' zs') note l_vmtf = this(1) and a_le_y = this(2) and zs_a = this(3)
      and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and nn' = this(8) and
       IH = this(9) and H = this(10-)
    have \<open>l_vmtf (c # b # l) n' zs\<close>
      by (rule l_vmtf.Cons[OF Cons.hyps])
    have [simp]: \<open>b < length xs\<close>  \<open>b < length zs\<close>
      using H xs' by auto
    have [simp]: \<open>b \<notin> set l\<close>
      using l_vmtf_distinct[OF l_vmtf] by auto
    then have K: \<open>\<forall>i\<in>set l. zs ! i = (if b = i then x else xs ! i) =
       (\<forall>i\<in>set l. zs ! i = xs ! i)\<close> for x
       using H(2)
       by (simp add: H(1) xs')
    have next_xs_b: \<open>get_next (xs ! b) = None\<close> if \<open>l = []\<close>
      using l_vmtf unfolding that by (auto simp: elim!: l_vmtfE)
    have prev_xs_b: \<open>get_prev (xs ! b) = None\<close>
      using l_vmtf by (auto elim: l_vmtfE)
    have l_vmtf_zs: \<open>l_vmtf (b # l) m (zs'[b := xs!b])\<close>
      apply (rule IH)
      subgoal using H(1) ab next_xs_b prev_xs_b H unfolding xs' by (auto simp: K)
      subgoal using H(2) ab next_xs_b prev_xs_b unfolding xs' by (auto simp: K)
      done
    have \<open>zs' ! b = l_vmtf_ATM (stamp (xs ! b)) (Some c) (get_next (xs ! b))\<close>
      using H(1) unfolding xs' by auto
    show ?case
      apply (rule l_vmtf.Cons[OF l_vmtf_zs, of _ n])
      subgoal using a_le_y xs' H(2) by auto
      subgoal using ab zs_a xs' H(1) by (auto simp: K)
      subgoal using ab .
      subgoal using a_l .
      subgoal using mn .
      subgoal using ab xs' H(1) by (metis H(2) insert_iff list.set(2) list_update_id
            list_update_overwrite nth_list_update_eq)
      subgoal using nn' .
      done
  qed
  then show ?thesis
    using assms by metis
qed

lemmas l_vmtf_eq_iffI = l_vmtf_eq_iff[THEN iffD1]

lemma l_vmtf_stamp_increase: \<open>l_vmtf xs p zs \<Longrightarrow> p \<le> p' \<Longrightarrow> l_vmtf xs p' zs\<close>
  apply (induction rule: l_vmtf.induct)
  subgoal by (auto intro: l_vmtf.intros)
  subgoal by (rule l_vmtf.Cons1) (auto intro!: l_vmtf.intros)
  subgoal by (auto intro: l_vmtf.intros)
  done

lemma l_vmtf_single_iff: \<open>l_vmtf [a] m xs \<longleftrightarrow> (a < length xs \<and> m \<ge> stamp (xs ! a) \<and>
     xs ! a = l_vmtf_ATM (stamp (xs ! a)) None None)\<close>
  by (auto 5 5 elim!: l_vmtfE intro: l_vmtf.intros)

lemma l_vmtf_append_decomp:
  assumes \<open>l_vmtf (axs @ [ax, ay] @ azs) an A\<close>
  shows \<open>(l_vmtf (axs @ [ax]) an (A[ax:= l_vmtf_ATM (stamp (A!ax)) (get_prev (A!ax)) None]) \<and>
    l_vmtf (ay # azs) (stamp (A!ay)) (A[ay:= l_vmtf_ATM (stamp (A!ay)) None (get_next (A!ay))]) \<and>
    stamp (A!ax) > stamp (A!ay))\<close>
  using assms
proof (induction \<open>axs @ [ax, ay] @ azs\<close> an A arbitrary: axs ax ay azs rule: l_vmtf.induct)
  case (Nil st xs)
  then show ?case by simp
next
  case (Cons1 a xs m n)
  then show ?case by auto
next
  case (Cons b l m xs a n xs' n') note l_vmtf = this(1) and IH = this(2) and a_le_y = this(3) and
    zs_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10-)
  have b_le_xs: \<open>b < length xs\<close>
    using l_vmtf by (auto intro: l_vmtf_le_length simp: xs')
  show ?case
  proof (cases \<open>axs\<close>)
    case [simp]: Nil
    then have [simp]: \<open>ax = a\<close> \<open>ay = b\<close> \<open>azs = l\<close>
      using decomp by auto
    show ?thesis
    proof (cases l)
      case Nil
      then show ?thesis
        using l_vmtf xs' a_le_y zs_a ab a_l mn nn' by (cases \<open>xs ! b\<close>)
          (auto simp: l_vmtf_single_iff)
    next
      case (Cons al als) note l = this
      have l_vmtf_b: \<open>l_vmtf [b] m (xs[b := l_vmtf_ATM (stamp (xs ! b)) (get_prev (xs ! b)) None])\<close> and
        l_vmtf_l: \<open>l_vmtf (al # als) (stamp (xs ! al))
           (xs[al := l_vmtf_ATM (stamp (xs ! al)) None (get_next (xs ! al))])\<close> and
        stamp_al_b: \<open>stamp (xs ! al) < stamp (xs ! b)\<close>
        using IH[of Nil b al als] unfolding l by auto
      have \<open>l_vmtf [a] n' (xs'[a := l_vmtf_ATM (stamp (xs' ! a)) (get_prev (xs' ! a)) None])\<close>
          using a_le_y xs' ab mn nn' zs_a by (auto simp: l_vmtf_single_iff)
      have al_b[simp]: \<open>al \<noteq> b\<close> and b_als: \<open>b \<notin> set als\<close>
        using l_vmtf unfolding l by (auto dest: l_vmtf_distinct)
      have al_le_xs: \<open>al < length xs\<close>
        using l_vmtf l_vmtf_l by (auto intro: l_vmtf_le_length simp: l xs')
      have xs_al: \<open>xs ! al = l_vmtf_ATM (stamp (xs ! al)) (Some b) (get_next (xs ! al))\<close>
        using l_vmtf unfolding l by (auto 5 5 elim: l_vmtfE)
      have xs_b: \<open>xs ! b = l_vmtf_ATM (stamp (xs ! b)) None (get_next (xs ! b))\<close>
        using l_vmtf_b l_vmtf xs' by (cases \<open>xs ! b\<close>) (auto elim: l_vmtfE simp: l l_vmtf_single_iff)

      have \<open>l_vmtf (b # al # als) (stamp (xs' ! b))
          (xs'[b := l_vmtf_ATM (stamp (xs' ! b)) None (get_next (xs' ! b))])\<close>
        apply (rule l_vmtf.Cons[OF l_vmtf_l, of _ \<open>stamp (xs' ! b)\<close>])
        subgoal using b_le_xs by auto
        subgoal using xs_b l_vmtf_b l_vmtf xs' by (cases \<open>xs ! b\<close>)
            (auto elim: l_vmtfE simp: l l_vmtf_single_iff)
        subgoal using al_b by blast
        subgoal using b_als .
        subgoal using xs' b_le_xs stamp_al_b by (simp add:)
        subgoal using ab unfolding xs' by (simp add: b_le_xs al_le_xs xs_al[symmetric]
              xs_b[symmetric])
        subgoal by simp
        done
      moreover have \<open>l_vmtf [a] n'
          (xs'[a := l_vmtf_ATM (stamp (xs' ! a)) (get_prev (xs' ! a)) None])\<close>
        using ab a_le_y mn nn' zs_a by (auto simp: l_vmtf_single_iff xs')
      moreover have \<open>stamp (xs' ! b) < stamp (xs' ! a)\<close>
        using b_le_xs ab mn l_vmtf_b zs_a by (auto simp add: xs' l_vmtf_single_iff)
      ultimately show ?thesis
        unfolding l by (simp add: l)
    qed
  next
    case (Cons aaxs axs') note axs = this
    have [simp]: \<open>aaxs = a\<close> and bl: \<open>b # l = axs' @ [ax, ay] @ azs\<close>
      using decomp unfolding axs by simp_all
    have
      l_vmtf_axs': \<open>l_vmtf (axs' @ [ax]) m
        (xs[ax := l_vmtf_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close> and
      l_vmtf_ay: \<open>l_vmtf (ay # azs) (stamp (xs ! ay))
        (xs[ay := l_vmtf_ATM (stamp (xs ! ay)) None (get_next (xs ! ay))])\<close> and
      stamp: \<open>stamp (xs ! ay) < stamp (xs ! ax)\<close>
      using IH[OF bl] by fast+
    have b_ay: \<open>b \<noteq> ay\<close>
      using bl l_vmtf_distinct[OF l_vmtf] by (cases axs') auto
    have l_vmtf_ay': \<open>l_vmtf (ay # azs) (stamp (xs' ! ay))
        (xs[ay := l_vmtf_ATM (stamp (xs ! ay)) None (get_next (xs ! ay))])\<close>
      using l_vmtf_ay xs' b_ay by (auto)
    have [simp]: \<open>ay < length xs\<close>
        using l_vmtf by (auto intro: l_vmtf_le_length simp: bl xs')
    have in_azs_noteq_b: \<open>i \<in> set azs \<Longrightarrow> i \<noteq> b\<close> for i
      using l_vmtf_distinct[OF l_vmtf] bl by (cases axs') (auto simp: xs' b_ay)
    have a_ax[simp]: \<open>a \<noteq> ax\<close>
      using ab a_l bl by (cases axs') (auto simp: xs' b_ay)
    have \<open>l_vmtf (axs @ [ax]) n'
       (xs'[ax := l_vmtf_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
    proof (cases axs')
      case Nil
      then have [simp]: \<open>ax = b\<close>
        using bl by auto
      have \<open>l_vmtf [ax] m (xs[ax := l_vmtf_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close>
        using l_vmtf_axs' unfolding axs Nil by simp
      then have \<open>l_vmtf (aaxs # ax # []) n'
          (xs'[ax := l_vmtf_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
        apply (rule l_vmtf.Cons[of _ _ _ _ _ n])
        subgoal using a_le_y by auto
        subgoal using zs_a a_le_y ab by auto
        subgoal using ab by auto
        subgoal by simp
        subgoal using mn .
        subgoal using zs_a a_le_y ab xs' b_le_xs  by auto
        subgoal using nn' .
        done
      then show ?thesis
        using l_vmtf_axs' unfolding axs Nil by simp
    next
      case (Cons aaaxs' axs'')
      have [simp]: \<open>aaaxs' = b\<close>
        using bl unfolding Cons by auto
      have \<open>l_vmtf (aaaxs' # axs'' @ [ax]) m
          (xs[ax := l_vmtf_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close>
        using l_vmtf_axs' unfolding axs Cons by simp
      then have \<open>l_vmtf (a # aaaxs' # axs'' @ [ax]) n'
          (xs'[ax := l_vmtf_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
        apply (rule l_vmtf.Cons[of _ _ _ _ _ n])
        subgoal using a_le_y by auto
        subgoal using zs_a a_le_y a_ax ab by (auto simp del: \<open>a \<noteq> ax\<close>)
        subgoal using ab by auto
        subgoal using a_l bl unfolding Cons by simp
        subgoal using mn .
        subgoal using zs_a a_le_y ab xs' b_le_xs  by (auto simp: list_update_swap)
        subgoal using nn' .
        done
      then show ?thesis
        unfolding axs Cons by simp
    qed
    moreover have \<open>l_vmtf (ay # azs) (stamp (xs' ! ay))
        (xs'[ay := l_vmtf_ATM (stamp (xs' ! ay)) None (get_next (xs' ! ay))])\<close>
      apply (rule l_vmtf_eq_iffI[OF _ _ l_vmtf_ay'])
      subgoal using l_vmtf_distinct[OF l_vmtf] bl b_le_xs in_azs_noteq_b by (auto simp: xs' b_ay)
      subgoal using l_vmtf_le_length[OF l_vmtf] bl unfolding xs' by auto
      done
    moreover have \<open>stamp (xs' ! ay) < stamp (xs' ! ax)\<close>
      using stamp unfolding axs xs' by (auto simp: b_le_xs b_ay)
    ultimately show ?thesis
      unfolding axs xs' by fast
  qed
qed

lemma l_vmtf_append_rebuild:
  assumes
    \<open>(l_vmtf (axs @ [ax]) an A) \<close> and
    \<open>l_vmtf (ay # azs) (stamp (A!ay)) A\<close> and
    \<open>stamp (A!ax) > stamp (A!ay)\<close> and
    \<open>distinct (axs @ [ax, ay] @ azs)\<close>
  shows \<open>l_vmtf (axs @ [ax, ay] @ azs) an
    (A[ax := l_vmtf_ATM (stamp (A!ax)) (get_prev (A!ax)) (Some ay) ,
       ay := l_vmtf_ATM (stamp (A!ay)) (Some ax) (get_next (A!ay))])\<close>
  using assms
proof (induction \<open>axs @ [ax]\<close> an A arbitrary: axs ax ay azs rule: l_vmtf.induct)
  case (Nil st xs)
  then show ?case by simp
next
  case (Cons1 a xs m n) note a_le_xs = this(1) and nm = this(2) and xs_a = this(3) and a = this(4)
    and l_vmtf = this(5) and stamp = this(6) and dist = this(7)
  have a_ax: \<open>ax = a\<close>
    using a by simp

  have l_vmtf_ay': \<open>l_vmtf (ay # azs) (stamp (xs ! ay)) (xs[ax := l_vmtf_ATM n None (Some ay)])\<close>
    apply (rule l_vmtf_eq_iffI[OF _ _ l_vmtf])
    subgoal using dist a_ax a_le_xs by auto
    subgoal using l_vmtf l_vmtf_le_length by auto
    done

  then have \<open>l_vmtf (ax # ay # azs) m (xs[ax := l_vmtf_ATM n None (Some ay),
      ay := l_vmtf_ATM (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    apply (rule l_vmtf.Cons[of _ _ _ _ _ \<open>stamp (xs ! a)\<close>])
    subgoal using a_le_xs unfolding a_ax by auto
    subgoal using xs_a a_ax a_le_xs by auto
    subgoal using dist by auto
    subgoal using dist by auto
    subgoal using stamp by (simp add: a_ax)
    subgoal using a_ax a_le_xs dist by auto
    subgoal by (simp add: nm xs_a)
    done
  then show ?case
    using a_ax a xs_a by auto
next
  case (Cons b l m xs a n xs' n') note l_vmtf = this(1) and IH = this(2) and a_le_y = this(3) and
    zs_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10) and l_vmtf_ay = this(11) and stamp = this(12) and
    dist = this(13)

  have dist_b: \<open>distinct ((a # b # l) @ ay # azs)\<close>
    using dist unfolding decomp by auto
  then have b_ay: \<open>b \<noteq> ay\<close>
    by auto
  have b_le_xs: \<open>b < length xs\<close>
    using l_vmtf l_vmtf_le_length by auto
  have a_ax: \<open>a \<noteq> ax\<close> and a_ay: \<open>a \<noteq> ay\<close>
    using dist_b decomp dist by (cases axs; auto)+
  have l_vmtf_ay': \<open>l_vmtf (ay # azs) (stamp (xs ! ay)) xs\<close>
    apply (rule l_vmtf_eq_iffI[of _ _ xs'])
    subgoal using xs' b_ay dist_b  b_le_xs by auto
    subgoal using l_vmtf_le_length[OF l_vmtf_ay] xs' by auto
    subgoal using xs' b_ay dist_b  b_le_xs l_vmtf_ay xs' by auto
    done

  have \<open>l_vmtf (tl axs @ [ax, ay] @ azs) m
          (xs[ax := l_vmtf_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) (Some ay),
              ay := l_vmtf_ATM (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    apply (rule IH)
    subgoal using decomp by (cases axs) auto
    subgoal using l_vmtf_ay' .
    subgoal using stamp xs' b_ay b_le_xs by (cases \<open>ax = b\<close>) auto
    subgoal using dist by (cases axs) auto
    done
  moreover have \<open>tl axs @ [ax, ay] @ azs = b # l @ ay # azs\<close>
    using decomp by (cases axs) auto
  ultimately have l_vmtf_tl_axs: \<open>l_vmtf (b # l @ ay # azs) m
          (xs[ax := l_vmtf_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) (Some ay),
              ay := l_vmtf_ATM (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    by metis

  then have \<open>l_vmtf (a # b # l @ ay # azs) n'
     (xs'[ax := l_vmtf_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) (Some ay),
          ay := l_vmtf_ATM (stamp (xs' ! ay)) (Some ax) (get_next (xs' ! ay))])\<close>
    apply (rule l_vmtf.Cons[of _ _ _ _ _ \<open>stamp (xs ! a)\<close>])
    subgoal using a_le_y by simp
    subgoal using zs_a a_le_y a_ax a_ay by auto
    subgoal using ab .
    subgoal using dist_b by auto
    subgoal using mn by (simp add: zs_a)
    subgoal using zs_a a_le_y a_ax a_ay b_ay b_le_xs unfolding xs'
      by (auto simp: list_update_swap)
    subgoal using stamp xs' nn' b_ay b_le_xs zs_a by auto
    done
  then show ?case
    by (metis append.assoc append_Cons append_Nil decomp)
qed

text \<open>
  It is tempting to remove the \<^term>\<open>update_x\<close>. However, it leads to more complicated
  reasoning later: What happens if x is not in the list, but its successor is? Moreover, it is
  unlikely to really make a big difference (performance-wise).\<close>
definition l_vmtf_dequeue where
\<open>l_vmtf_dequeue xs y =
  (let x = xs ! y;
    update_prev = \<lambda>xs.
      (case get_prev x of None \<Rightarrow> xs
      | Some a \<Rightarrow> xs[a:= l_vmtf_ATM (stamp (xs!a)) (get_prev (xs!a)) (get_next x)]);
    update_next = \<lambda>xs.
      (case get_next x of None \<Rightarrow> xs
      | Some a \<Rightarrow> xs[a:= l_vmtf_ATM (stamp (xs!a)) (get_prev x) (get_next (xs!a))]);
    update_x = \<lambda>xs. xs[y:= l_vmtf_ATM (stamp (xs!y)) None None]
    in
  update_x (update_next (update_prev xs)))
  \<close>

lemma l_vmtf_different_same_neq: \<open>l_vmtf (b # c # l') m xs \<Longrightarrow> l_vmtf (c # l') m xs \<Longrightarrow> False\<close>
  apply (cases l')
   apply (force elim: l_vmtfE)
  apply (subst (asm) l_vmtf.simps)
  apply (subst (asm)(2) l_vmtf.simps)
  apply auto (* TODO Proof *)
  by (metis length_list_update nth_list_update_eq nth_list_update_neq option.distinct(1) l_vmtf_atm.sel(2))

lemma l_vmtf_last_next:
  \<open>l_vmtf (xs @ [x]) m A \<Longrightarrow> get_next (A ! x) = None\<close>
  apply (induction "xs @ [x]" m A arbitrary: xs x rule: l_vmtf.induct) (* TODO Proof *)
    apply auto
  by (metis list.distinct(1) list.sel(3) list.set_intros(1) nth_list_update_eq nth_list_update_neq
      self_append_conv2 tl_append2 l_vmtf_atm.sel(3) l_vmtf_le_length)

lemma l_vmtf_last_mid_get_next:
  \<open>l_vmtf (xs @ [x, y] @ zs) m A \<Longrightarrow> get_next (A ! x) = Some y\<close>
  apply (induction "xs @ [x, y] @ zs" m A arbitrary: xs x rule: l_vmtf.induct) (* TODO Proof *)
    apply auto
  by (metis list.sel(1) list.sel(3) list.set_intros(1) nth_list_update_eq nth_list_update_neq
      self_append_conv2 tl_append2 l_vmtf_atm.sel(3) l_vmtf_le_length)

lemma l_vmtf_last_mid_get_prev:
  assumes \<open>l_vmtf (xs @ [x, y] @ zs) m A\<close>
  shows \<open>get_prev (A ! y) = Some x\<close>
    using assms
proof (induction "xs @ [x, y] @ zs" m A arbitrary: xs x rule: l_vmtf.induct)
  case (Nil st xs)
  then show ?case by auto
next
  case (Cons1 a xs m n)
  then show ?case by auto
next
  case (Cons b l m xxs a n xxs' n') note l_vmtf = this(1) and IH = this(2) and a_le_y = this(3) and
    zs_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Cons l_vmtf_le_length by auto
  next
    case (Cons aaxs axs')
    then have b_l: \<open>b # l = tl xs @ [x, y] @ zs\<close>
      using decomp by auto
    then have \<open>get_prev (xxs ! y) = Some x\<close>
      by (rule IH)
    moreover have \<open>x \<noteq> y\<close>
      using l_vmtf_distinct[OF l_vmtf] b_l by auto
    moreover have \<open>b \<noteq> y\<close>
      using l_vmtf_distinct[OF l_vmtf] decomp by (cases axs') (auto simp add: Cons)
    moreover have \<open>y < length xxs\<close> \<open>b < length xxs\<close>
      using l_vmtf_le_length[OF l_vmtf, unfolded b_l] l_vmtf_le_length[OF l_vmtf] by auto
    ultimately show ?thesis
      unfolding xs' by auto
  qed
qed

lemma length_l_vmtf_dequeue[simp]: \<open>length (l_vmtf_dequeue A x) = length A\<close>
  unfolding l_vmtf_dequeue_def by (auto simp: Let_def split: option.splits)

lemma l_vmtf_skip_fst:
  assumes l_vmtf: \<open>l_vmtf (x # y' # zs') m A\<close>
  shows \<open>\<exists>n. l_vmtf (y' # zs') n (A[y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))]) \<and>
     m \<ge> n\<close>
  using assms
proof (rule l_vmtfE, goal_cases)
  case 1
  then show ?case by simp
next
  case (2 a n)
  then show ?case by simp
next
  case (3 b l m xs a n)
  moreover have \<open>get_prev (xs ! b) = None\<close>
    using 3(3) by (fastforce elim: l_vmtfE)
  moreover have \<open>b < length xs\<close>
    using 3(3) l_vmtf_le_length by auto
  ultimately show ?case
    by (cases \<open>xs ! b\<close>) (auto simp: eq_commute[of \<open>xs ! b\<close>])
qed

definition none_or_notin_list where
\<open>none_or_notin_list m l \<equiv> m = None \<or> the m \<notin> set l\<close>

definition l_vmtf_notin where
  \<open>l_vmtf_notin l m xs \<longleftrightarrow> (\<forall>i<length xs. i\<notin>set l \<longrightarrow> (none_or_notin_list (get_prev (xs ! i)) l \<and>
      none_or_notin_list (get_next (xs ! i)) l))\<close>

lemma l_vmtf_notinI:
  \<open>(\<And>i. i <length xs \<Longrightarrow> i\<notin>set l \<Longrightarrow> (none_or_notin_list (get_prev (xs ! i)) l \<and>
      none_or_notin_list (get_next (xs ! i)) l)) \<Longrightarrow> l_vmtf_notin l m xs\<close>
  by (auto simp: l_vmtf_notin_def)

lemma stamp_l_vmtf_dequeue:
  \<open>axs < length zs \<Longrightarrow> stamp (l_vmtf_dequeue zs x ! axs) = stamp (zs ! axs)\<close>
  by (cases \<open>zs ! (the (get_next (zs ! x)))\<close>; cases \<open>(the (get_next (zs ! x))) = axs\<close>;
      cases \<open>(the (get_prev (zs ! x))) = axs\<close>; cases \<open>zs ! x\<close>)
    (auto simp: nth_list_update' l_vmtf_dequeue_def Let_def split: option.splits)

lemma sorted_many_eq_append: \<open>sorted (xs @ [x, y]) \<longleftrightarrow> sorted (xs @ [x]) \<and> x \<le> y\<close>
  using sorted_append[of \<open>xs @ [x]\<close> \<open>[y]\<close>] sorted_append[of xs \<open>[x]\<close>]
  by force

lemma l_vmtf_stamp_sorted:
  assumes \<open>l_vmtf l m A\<close>
  shows \<open>sorted (map (\<lambda>a. stamp (A!a)) (rev l)) \<and> (\<forall>a \<in> set l. stamp (A!a) \<le> m)\<close>
  using assms
proof (induction rule: l_vmtf.induct)
  case (Cons b l m xs a n xs' n') note l_vmtf = this(1) and IH = this(9) and a_le_y = this(2) and
    zs_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8)
  have H:
  \<open>map (\<lambda>aa. stamp (xs[b := l_vmtf_ATM (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! aa)) (rev l) =
     map (\<lambda>a. stamp (xs ! a)) (rev l)\<close>
    apply (rule map_cong)
    subgoal by auto
    subgoal using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] by auto
    done
  have [simp]: \<open>stamp (xs[b := l_vmtf_ATM (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! b) =
     stamp (xs ! b)\<close>
    using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] by (cases \<open>xs ! b\<close>) auto
  have \<open>stamp (xs[b := l_vmtf_ATM (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! aa) \<le> n'\<close>
    if \<open>aa \<in> set l\<close> for aa
    apply (cases \<open>aa = b\<close>)
    subgoal using Cons by auto
    subgoal using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] IH nn' mn that by auto
    done
  then show ?case
    using Cons by (auto simp: H sorted_many_eq_append)
qed auto


text \<open>
  This a version of @{thm nth_list_update} with a different condition (\<^term>\<open>j\<close>
  instead of \<^term>\<open>i\<close>). This is more useful here.
  \<close>
(* TODO: Move*)
lemma nth_list_update_le'[simp]:
"j < length xs \<Longrightarrow> (xs[i:=x])!j = (if i = j then x else xs!j)"
  by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)

lemma l_vmtf_l_vmtf_dequeue:
  assumes l_vmtf: \<open>l_vmtf l m A\<close> and notin: \<open>l_vmtf_notin l m A\<close> and valid: \<open>x < length A\<close>
  shows \<open>l_vmtf (remove1 x l) m (l_vmtf_dequeue A x)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  have
      \<open>none_or_notin_list (get_prev (A ! x)) l\<close> and
      \<open>none_or_notin_list (get_next (A ! x)) l\<close>
    using notin False valid unfolding l_vmtf_notin_def by auto
  then have l_vmtf_eq: \<open>(l_vmtf_dequeue A x) ! a = A ! a\<close> if \<open>a \<in> set l\<close> for a
    using that False valid unfolding l_vmtf_notin_def l_vmtf_dequeue_def
    by (cases \<open>A ! (the (get_prev (A ! x)))\<close>; cases \<open>A ! (the (get_next (A ! x)))\<close>)
      (auto simp: Let_def none_or_notin_list_def split: option.splits)
  show ?thesis
    unfolding H
    apply (rule l_vmtf_eq_iffI[OF _ _ l_vmtf])
    subgoal using l_vmtf_eq by blast
    subgoal using l_vmtf_le_length[OF l_vmtf] by auto
    done
next
  case True
  then obtain xs zs where
    l: \<open>l = xs @ x # zs\<close>
    by (meson split_list)
  have r_l: \<open>remove1 x l = xs @ zs\<close>
    using l_vmtf_distinct[OF l_vmtf] unfolding l by (simp add: remove1_append)
  have dist: \<open>distinct l\<close>
    using l_vmtf_distinct[OF l_vmtf] .
  have le_length: \<open>i \<in> set l \<Longrightarrow> i < length A\<close> for i
    using l_vmtf_le_length[OF l_vmtf] .
  consider
    (xs_zs_empty) \<open>xs = []\<close> and \<open>zs = []\<close> |
    (xs_nempty_zs_empty) x' xs' where \<open>xs = xs' @ [x']\<close> and \<open>zs = []\<close> |
    (xs_empty_zs_nempty) y' zs' where \<open>xs = []\<close> and \<open>zs = y' # zs'\<close> |
    (xs_zs_nempty) x' y' xs' zs' where  \<open>xs = xs' @ [x']\<close> and \<open>zs = y' # zs'\<close>
    by (cases xs rule: rev_cases; cases zs)
  then show ?thesis
  proof cases
    case xs_zs_empty
    then show ?thesis
      using l_vmtf by (auto simp: r_l intro: l_vmtf.intros)
  next
    case xs_empty_zs_nempty note xs = this(1) and zs = this(2)
    have [simp]: \<open>x \<noteq> y'\<close> \<open>y' \<noteq> x\<close> \<open>x \<notin> set zs'\<close>
      using dist  unfolding l xs zs by auto
    have prev_next: \<open>get_prev (A ! x) = None\<close> \<open>get_next (A ! x) = option_hd zs\<close>
      using l_vmtf unfolding l xs zs
      by (cases zs; auto 5 5 simp: option_hd_def elim: l_vmtfE; fail)+
    then have vmtf': \<open>l_vmtf (y' # zs') m (A[y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      using l_vmtf unfolding r_l unfolding l xs zs -- \<open>TODO proof\<close>
      by (auto simp: l_vmtf_dequeue_def Let_def nth_list_update' zs
          split: option.splits
          intro: l_vmtf.intros l_vmtf_stamp_increase dest: l_vmtf_skip_fst)
    show ?thesis
      apply (rule l_vmtf_eq_iffI[of _ _
            \<open>(A[y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close> m])
      subgoal
        using  prev_next unfolding r_l unfolding l xs zs
        by (cases \<open>A ! x\<close>) (auto simp: l_vmtf_dequeue_def Let_def nth_list_update')
      subgoal
        using prev_next le_length unfolding r_l unfolding l xs zs
        by (cases \<open>A ! x\<close>) auto
      subgoal
        using vmtf' unfolding r_l unfolding l xs zs by auto
      done
  next
    case xs_nempty_zs_empty note xs = this(1) and zs = this(2)
    have [simp]: \<open>x \<noteq> x'\<close> \<open>x' \<noteq> x\<close> \<open>x' \<notin> set xs'\<close> \<open>x \<notin> set xs'\<close>
      using dist  unfolding l xs zs by auto
    have prev_next: \<open>get_prev (A ! x) = Some x'\<close> \<open>get_next (A ! x) = None\<close>
      using l_vmtf l_vmtf_append_decomp[of xs' x' x zs m A] unfolding l xs zs
      by (auto simp: l_vmtf_single_iff intro: l_vmtf_last_mid_get_prev)
    then have vmtf': \<open>l_vmtf (xs' @ [x']) m (A[x' := l_vmtf_ATM (stamp (A ! x')) (get_prev (A ! x')) None])\<close>
      using l_vmtf unfolding r_l unfolding l xs zs
      by (auto simp: l_vmtf_dequeue_def Let_def l_vmtf_append_decomp split: option.splits
          intro: l_vmtf.intros)
    show ?thesis
      apply (rule l_vmtf_eq_iffI[of _ _
            \<open>(A[x' := l_vmtf_ATM (stamp (A ! x')) (get_prev (A ! x')) None])\<close> m])
      subgoal
        using prev_next unfolding r_l unfolding l xs zs
        by (cases \<open>A ! x'\<close>) (auto simp: l_vmtf_dequeue_def Let_def nth_list_update')
      subgoal
        using prev_next le_length unfolding r_l unfolding l xs zs
        by (cases \<open>A ! x\<close>) auto
      subgoal
        using vmtf' unfolding r_l unfolding l xs zs by auto
      done
  next
    case xs_zs_nempty note xs = this(1) and zs = this(2)
    have l_vmtf_x'_x: \<open>l_vmtf (xs' @ [x', x] @ (y' #  zs')) m A\<close> and
      l_vmtf_x_y: \<open>l_vmtf ((xs' @ [x']) @ [x, y'] @ zs') m A\<close>
      using l_vmtf unfolding l xs zs by simp_all
    from l_vmtf_append_decomp[OF l_vmtf_x'_x] have
      l_vmtf_xs: \<open>l_vmtf (xs' @ [x']) m (A[x' := l_vmtf_ATM (stamp (A ! x')) (get_prev (A ! x')) None])\<close> and
      l_vmtf_zs: \<open>l_vmtf (x # y' # zs') (stamp (A ! x)) (A[x := l_vmtf_ATM (stamp (A ! x)) None (get_next (A ! x))])\<close> and
      stamp: \<open>stamp (A ! x) < stamp (A ! x')\<close>
      by fast+
    have [simp]: \<open>y' < length A\<close> \<open>x < length A\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> \<open>x' < length A\<close> \<open>y' \<noteq> x'\<close>
      \<open>x' \<noteq> x\<close> \<open>x \<noteq> x'\<close> \<open>y' \<noteq> x\<close>
      and x_zs': \<open>x \<notin> set zs'\<close> \<open>x \<notin> set xs'\<close> and x'_zs': \<open>x' \<notin> set zs'\<close> and y'_xs': \<open>y' \<notin> set xs'\<close>
      using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] unfolding l xs zs
      by auto
    obtain n where
      l_vmtf_zs': \<open>l_vmtf (y' # zs') n (A[x := l_vmtf_ATM (stamp (A ! x)) None (get_next (A ! x)),
          y' := l_vmtf_ATM (stamp (A[x := l_vmtf_ATM (stamp (A ! x)) None (get_next (A ! x))] ! y')) None
       (get_next (A[x := l_vmtf_ATM (stamp (A ! x)) None (get_next (A ! x))] ! y'))])\<close> and
      \<open>n \<le> stamp (A ! x)\<close>
      using l_vmtf_skip_fst[OF l_vmtf_zs] by blast
    then have l_vmtf_y'_zs'_x_y': \<open>l_vmtf (y' # zs') n (A[x := l_vmtf_ATM (stamp (A ! x)) None (get_next (A ! x)),
          y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      by auto

    define A' where \<open>A' = A[x' := l_vmtf_ATM (stamp (A ! x')) (get_prev (A ! x')) None,
         y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))]\<close>
    have l_vmtf_y'_zs'_y': \<open>l_vmtf (y' # zs') n (A[y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      apply (rule l_vmtf_eq_iffI[OF _ _ l_vmtf_y'_zs'_x_y'])
      subgoal using x_zs' by auto
      subgoal using l_vmtf_le_length[OF l_vmtf] unfolding l xs zs by auto
      done
    moreover have stamp_y'_n: \<open>stamp (A[x' := l_vmtf_ATM (stamp (A ! x')) (get_prev (A ! x')) None] ! y') \<le> n\<close>
      using l_vmtf_stamp_sorted[OF l_vmtf_y'_zs'_y'] stamp unfolding l xs zs
      by (auto simp: sorted_append)
    ultimately have l_vmtf_y'_zs'_y': \<open>l_vmtf (y' # zs') (stamp (A' ! y'))
       (A[y' := l_vmtf_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      using l l_vmtf l_vmtf_append_decomp xs_zs_nempty(2) A'_def by auto
    have l_vmtf_y'_zs'_x'_y': \<open>l_vmtf (y' # zs') (stamp (A' ! y')) A'\<close>
      apply (rule l_vmtf_eq_iffI[OF _ _ l_vmtf_y'_zs'_y'])
      subgoal using dist le_length x'_zs' A'_def unfolding l xs zs by auto
      subgoal using dist le_length x'_zs' A'_def unfolding l xs zs by auto
      done
    have l_vmtf_xs': \<open>l_vmtf (xs' @ [x']) m A'\<close>
      apply (rule l_vmtf_eq_iffI[OF _ _ l_vmtf_xs])
      subgoal using y'_xs' A'_def by auto
      subgoal using l_vmtf_le_length[OF l_vmtf_xs] A'_def by auto
      done
    have vmtf_x'_y': \<open>l_vmtf (xs' @ [x', y'] @ zs') m
       (A'[x' := l_vmtf_ATM (stamp (A' ! x')) (get_prev (A' ! x')) (Some y'),
         y' := l_vmtf_ATM (stamp (A' ! y')) (Some x') (get_next (A' ! y'))])\<close>
      apply (rule l_vmtf_append_rebuild[OF l_vmtf_xs' l_vmtf_y'_zs'_x'_y'])
      subgoal using stamp_y'_n l_vmtf_xs l_vmtf_zs stamp \<open>n \<le> stamp (A ! x)\<close>
        unfolding A'_def by auto
      subgoal by (metis append.assoc append_Cons distinct_remove1 r_l self_append_conv2 l_vmtf
            l_vmtf_distinct xs zs)
      done
    have \<open>l_vmtf (xs' @ [x', y'] @ zs') m
       (A'[x' := l_vmtf_ATM (stamp (A' ! x')) (get_prev (A' ! x')) (Some y'),
         y' := l_vmtf_ATM (stamp (A' ! y')) (Some x') (get_next (A' ! y')),
         x := l_vmtf_ATM (stamp (A' ! x)) None None])\<close>
      apply (rule l_vmtf_eq_iffI[OF _ _ vmtf_x'_y'])
      subgoal
        using l_vmtf_last_mid_get_next[OF l_vmtf_x_y] l_vmtf_last_mid_get_prev[OF l_vmtf_x'_x] x_zs'
        by (cases \<open>A!x\<close>; auto simp: nth_list_update' A'_def)
      subgoal using le_length unfolding l xs zs A'_def by auto
      done
    moreover have \<open>xs' @ [x', y'] @ zs' = remove1 x l\<close>
      unfolding r_l xs zs by auto
    moreover have \<open>A'[x' := l_vmtf_ATM (stamp (A' ! x')) (get_prev (A' ! x')) (Some y'),
         y' := l_vmtf_ATM (stamp (A' ! y')) (Some x') (get_next (A' ! y')),
         x := l_vmtf_ATM (stamp (A' ! x)) None None] = l_vmtf_dequeue A x\<close>
      using l_vmtf_last_mid_get_next[OF l_vmtf_x_y] l_vmtf_last_mid_get_prev[OF l_vmtf_x'_x]
      unfolding A'_def l_vmtf_dequeue_def (* TODO proof *)
      apply (auto simp: Let_def)
        by (metis (no_types, lifting) list_update_overwrite list_update_swap)
    ultimately show ?thesis
      by force
  qed
qed

lemma
   none_or_notin_list_None[simp]: \<open>none_or_notin_list None l\<close> and
   none_or_notin_list_Some[simp]: \<open>none_or_notin_list (Some a) l \<longleftrightarrow> a \<notin> set l\<close>
  by (auto simp: none_or_notin_list_def)

lemma l_vmtf_notin_dequeue:
  assumes l_vmtf: \<open>l_vmtf l m A\<close> and notin: \<open>l_vmtf_notin l m A\<close> and valid: \<open>x < length A\<close>
  shows \<open>l_vmtf_notin (remove1 x l) m (l_vmtf_dequeue A x)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  have
    \<open>none_or_notin_list (get_prev (A ! x)) l\<close> and
    \<open>none_or_notin_list (get_next (A ! x)) l\<close>
    using notin False valid unfolding l_vmtf_notin_def by auto
  show ?thesis
    using notin valid False unfolding l_vmtf_notin_def
    by (auto simp: l_vmtf_notin_def l_vmtf_dequeue_def Let_def H split: option.splits)
next
  case True
  then obtain xs zs where
    l: \<open>l = xs @ x # zs\<close>
    by (meson split_list)
  have r_l: \<open>remove1 x l = xs @ zs\<close>
    using l_vmtf_distinct[OF l_vmtf] unfolding l by (simp add: remove1_append)

  consider
    (xs_zs_empty) \<open>xs = []\<close> and \<open>zs = []\<close> |
    (xs_nempty_zs_empty) x' xs' where \<open>xs = xs' @ [x']\<close> and \<open>zs = []\<close> |
    (xs_empty_zs_nempty) y' zs' where \<open>xs = []\<close> and \<open>zs = y' # zs'\<close> |
    (xs_zs_nempty) x' y' xs' zs' where  \<open>xs = xs' @ [x']\<close> and \<open>zs = y' # zs'\<close>
    by (cases xs rule: rev_cases; cases zs)
  then show ?thesis
  proof cases
    case xs_zs_empty
    then show ?thesis
      using notin l_vmtf unfolding l apply (cases \<open>A ! x\<close>)
        by (auto simp: l_vmtf_notin_def l_vmtf_dequeue_def Let_def l_vmtf_single_iff
          none_or_notin_list_def split: option.splits)
  next
    case xs_empty_zs_nempty note xs = this(1) and zs = this(1)
    have prev_next: \<open>get_prev (A ! x) = None\<close> \<open>get_next (A ! x) = option_hd zs\<close>
      using l_vmtf unfolding l xs zs
      by (cases zs; auto 5 5 simp: option_hd_def elim: l_vmtfE; fail)+
    show ?thesis
      apply (rule l_vmtf_notinI)
      apply (case_tac \<open>i = x\<close>)
      subgoal
        using l_vmtf prev_next unfolding r_l unfolding l xs zs
        by (cases zs) (auto simp: l_vmtf_dequeue_def Let_def
            l_vmtf_notin_def l_vmtf_single_iff
            split: option.splits
            simp del: none_or_notin_list_Some)
      subgoal
        using l_vmtf notin prev_next unfolding r_l unfolding l xs zs
        by (auto simp: l_vmtf_dequeue_def Let_def
            l_vmtf_notin_def l_vmtf_single_iff none_or_notin_list_def
            simp del: none_or_notin_list_None none_or_notin_list_Some
            split: option.splits
            intro: l_vmtf.intros l_vmtf_stamp_increase dest: l_vmtf_skip_fst)
       done
  next
    case xs_nempty_zs_empty note xs = this(1) and zs = this(2)
    have prev_next: \<open>get_prev (A ! x) = Some x'\<close> \<open>get_next (A ! x) = None\<close>
      using l_vmtf l_vmtf_append_decomp[of xs' x' x zs m A] unfolding l xs zs
      by (auto simp: l_vmtf_single_iff intro: l_vmtf_last_mid_get_prev)
    then show ?thesis
      using l_vmtf notin unfolding r_l unfolding l xs zs
      by (auto simp: l_vmtf_dequeue_def Let_def l_vmtf_append_decomp l_vmtf_notin_def
          none_or_notin_list_def
          split: option.splits
          intro: l_vmtf.intros)
  next
    case xs_zs_nempty note xs = this(1) and zs = this(2)
    have l_vmtf_x'_x: \<open>l_vmtf (xs' @ [x', x] @ (y' #  zs')) m A\<close> and
      l_vmtf_x_y: \<open>l_vmtf ((xs' @ [x']) @ [x, y'] @ zs') m A\<close>
      using l_vmtf unfolding l xs zs by simp_all
    have [simp]: \<open>y' < length A\<close> \<open>x < length A\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> \<open>x' < length A\<close> \<open>y' \<noteq> x'\<close>
      \<open>y' \<noteq> x\<close> \<open>y' \<notin> set xs\<close>  \<open>y' \<notin> set zs'\<close>
      and x_zs': \<open>x \<notin> set zs'\<close> and x'_zs': \<open>x' \<notin> set zs'\<close> and y'_xs': \<open>y' \<notin> set xs'\<close>
      using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] unfolding l xs zs
      by auto
    have \<open>get_next (A!x) = Some y'\<close> \<open>get_prev (A!x) = Some x'\<close>
      using l_vmtf_last_mid_get_prev[OF l_vmtf_x'_x] l_vmtf_last_mid_get_next[OF l_vmtf_x_y]
      by fast+
    then show ?thesis
      using notin x_zs' x'_zs' y'_xs' unfolding l xs zs
      by (auto simp: l_vmtf_notin_def l_vmtf_dequeue_def none_or_notin_list_def)
  qed
qed

lemma l_vmtf_stamp_distinct:
  assumes \<open>l_vmtf l m A\<close>
  shows \<open>distinct (map (\<lambda>a. stamp (A!a)) l)\<close>
  using assms
proof (induction rule: l_vmtf.induct)
  case (Cons b l m xs a n xs' n') note l_vmtf = this(1) and IH = this(9) and a_le_y = this(2) and
    zs_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8)
  have [simp]: \<open>map (\<lambda>aa. stamp
                 (if b = aa
                  then l_vmtf_ATM (stamp (xs ! aa)) (Some a) (get_next (xs ! aa))
                  else xs ! aa)) l =
        map (\<lambda>aa. stamp (xs ! aa)) l
       \<close> for a
    apply (rule map_cong)
    subgoal ..
    subgoal using l_vmtf_distinct[OF l_vmtf] by auto
    done
  show ?case
    using Cons l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf]
    by (auto simp: sorted_many_eq_append leD l_vmtf_stamp_sorted cong: if_cong)
qed auto

lemma l_vmtf_thighten_stamp:
  assumes l_vmtf: \<open>l_vmtf l m xs\<close> and n: \<open>\<forall>a\<in>set l. stamp (xs ! a) \<le> n\<close>
  shows \<open>l_vmtf l n xs\<close>
proof -
  consider
    (empty) \<open>l = []\<close> |
    (single) x where \<open>l = [x]\<close> |
    (more_than_two) x y ys where \<open>l = x # y # ys\<close>
    by (cases l; cases \<open>tl l\<close>) auto
  then show ?thesis
  proof cases
    case empty
    then show ?thesis by (auto intro: l_vmtf.intros)
  next
    case (single x)
    then show ?thesis using n l_vmtf by (auto simp: l_vmtf_single_iff)
  next
    case (more_than_two x y ys) note l = this
    then have l_vmtf': \<open>l_vmtf ([] @ [x, y] @ ys) m xs\<close>
      using l_vmtf by auto
    from l_vmtf_append_decomp[OF this] have
      \<open>l_vmtf ([x]) m (xs[x := l_vmtf_ATM (stamp (xs ! x)) (get_prev (xs ! x)) None])\<close> and
      l_vmtf_y_ys: \<open>l_vmtf (y # ys) (stamp (xs ! y))
        (xs[y := l_vmtf_ATM (stamp (xs ! y)) None (get_next (xs ! y))])\<close> and
      \<open>stamp (xs ! y) < stamp (xs ! x)\<close>
      by auto
    have [simp]: \<open>x \<noteq> y\<close> \<open>x \<notin> set ys\<close> \<open>x < length xs\<close> \<open>y < length xs\<close>
      using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] unfolding l by auto
    show ?thesis
      unfolding l
      apply (rule l_vmtf.Cons[OF l_vmtf_y_ys, of _ \<open>stamp (xs ! x)\<close>])
      subgoal using l_vmtf_le_length[OF l_vmtf] unfolding l by auto
      subgoal using l_vmtf unfolding l by (cases \<open>xs ! x\<close>) (auto elim: l_vmtfE)
      subgoal by simp
      subgoal by simp
      subgoal using l_vmtf_stamp_sorted[OF l_vmtf] l_vmtf_stamp_distinct[OF l_vmtf]
       by (auto simp: l sorted_many_eq_append)
      subgoal
        using l_vmtf l_vmtf_last_mid_get_prev[OF l_vmtf']
        apply (cases \<open>xs ! y\<close>)
        by simp (auto simp: l eq_commute[of \<open>xs ! y\<close>])
      subgoal using n unfolding l by auto
      done
  qed
qed

lemma l_vmtf_rescale:
  assumes
    \<open>l_vmtf l m xs\<close> and
    \<open>sorted (map (\<lambda>a. st ! a) (rev l))\<close> and \<open>distinct (map (\<lambda>a. st ! a) l)\<close>
    \<open>\<forall>a \<in> set l. get_prev (zs ! a) = get_prev (xs ! a)\<close> and
    \<open>\<forall>a \<in> set l. get_next (zs ! a) = get_next (xs ! a)\<close> and
    \<open>\<forall>a \<in> set l. stamp (zs ! a) = st ! a\<close> and
    \<open>length xs \<le> length zs\<close> and
    \<open>\<forall>a\<in>set l. a < length st\<close>
  shows \<open>l_vmtf l (Max (set st)) zs\<close>
  using assms
proof (induction arbitrary: zs rule: l_vmtf.induct)
  case (Nil st xs)
  then show ?case by (auto intro: l_vmtf.intros)
next
  case (Cons1 a xs m n)
  then show ?case by (cases \<open>zs ! a\<close>) (auto simp: l_vmtf_single_iff intro!: Max_ge nth_mem)
next
  case (Cons b l m xs a n xs' n' zs) note l_vmtf = this(1) and a_le_y = this(2) and
    zs_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8) and IH = this(9) and H = this(10-)
  have [simp]: \<open>b < length xs\<close> \<open>b \<noteq> a\<close> \<open>a \<noteq> b\<close> \<open>b \<notin> set l\<close> \<open>b < length zs\<close> \<open>a < length zs\<close>
    using l_vmtf_distinct[OF l_vmtf] l_vmtf_le_length[OF l_vmtf] ab H(6) a_le_y unfolding xs'
    by force+

  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  define zs' where \<open>zs' \<equiv> (zs[b := l_vmtf_ATM (st ! b) (get_prev (xs ! b)) (get_next (xs ! b)),
          a := l_vmtf_ATM (st ! a) None (Some b)])\<close>
  have zs_upd_zs: \<open>zs = zs
    [b := l_vmtf_ATM (st ! b) (get_prev (xs ! b)) (get_next (xs ! b)),
     a := l_vmtf_ATM (st ! a) None (Some b),
     b := l_vmtf_ATM (st ! b) (Some a) (get_next (xs ! b))]
    \<close>
    using H(2-5) xs' zs_a \<open>b < length xs\<close>
    by (metis list.set_intros(1) list.set_intros(2) list_update_id list_update_overwrite
      nth_list_update_eq nth_list_update_neq l_vmtf_atm.collapse l_vmtf_atm.sel(2,3))

  have vtmf_b_l: \<open>l_vmtf (b # l) (Max (set st)) zs'\<close>
    unfolding zs'_def
    apply (rule IH)
    subgoal using H(1) by (simp add: sorted_many_eq_append)
    subgoal using H(2) by auto
    subgoal using H(3,4,5) xs' zs_a a_l ab by (auto split: if_splits)
    subgoal using H(4) xs' zs_a a_l ab by auto
    subgoal using H(5) xs' a_l ab by auto
    subgoal using H(6) xs' by auto
    subgoal using H(7) xs' by auto
    done
  then have \<open>l_vmtf (b # l) (stamp (zs' ! b)) zs'\<close>
    by (rule l_vmtf_thighten_stamp)
      (use l_vmtf_stamp_sorted[OF vtmf_b_l] in \<open>auto simp: sorted_append\<close>)

  then show ?case
    apply (rule l_vmtf.Cons[of _ _ _ _ _ \<open>st ! a\<close>])
    unfolding zs'_def
    subgoal using a_le_y H(6) xs' by auto
    subgoal using a_le_y by auto
    subgoal using ab.
    subgoal using a_l .
    subgoal using nn' mn H(1,2) by (auto simp: sorted_many_eq_append)
    subgoal using zs_upd_zs by auto
    subgoal using H by (auto intro!: Max_ge nth_mem)
    done
qed

lemma l_vmtf_last_prev:
  assumes vmtf: \<open>l_vmtf (xs @ [x]) m A\<close>
  shows \<open>get_prev (A ! x) = option_last xs\<close>
proof (cases xs rule: rev_cases)
  case Nil
  then show ?thesis using vmtf by (cases \<open>A!x\<close>) (auto simp: l_vmtf_single_iff)
next
  case (snoc xs' y')
  then  show ?thesis
    using l_vmtf_last_mid_get_prev[of xs' y' x \<open>[]\<close> m A] vmtf by auto
qed


context twl_array_code_ops
begin

paragraph \<open>Invariants\<close>

text \<open>Invariants
  \<^item> The atoms are alwazs disjoint.
  \<^item> The atoms of \<^term>\<open>zs\<close> are \<^emph>\<open>always\<close> set.
  \<^item> The atoms of \<^term>\<open>zs\<close> are \<^emph>\<open>never\<close> set and have been remove from \<^term>\<open>xs\<close> and \<^term>\<open>zs\<close>.
  \<^item> The atoms of \<^term>\<open>xs\<close> \<^emph>\<open>can be\<close> set but do not have to.
\<close>

definition abs_l_vmtf_remove_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_l_vmtf_remove \<Rightarrow> bool\<close> where
\<open>abs_l_vmtf_remove_inv M \<equiv> \<lambda>((xs, ys), zs).
  (\<forall>L\<in>ys. L \<in> atm_of ` lits_of_l M) \<and>
  xs \<inter> ys = {} \<and>
  xs \<inter> zs = {} \<and>
  ys \<inter> zs = {} \<and>
  xs \<union> zs \<union> ys = atms_of N\<^sub>1 \<and>
  (\<forall>L\<in>zs. L \<in> atm_of ` lits_of_l M) \<and>
  finite xs \<and> finite zs \<and> finite zs
  \<close>

abbreviation abs_l_vmtf_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_l_vmtf \<Rightarrow> bool\<close> where
\<open>abs_l_vmtf_inv M vm \<equiv> abs_l_vmtf_remove_inv M (vm, {})\<close>


paragraph \<open>Operations\<close>

fun abs_l_vmtf_bump :: \<open>nat literal \<Rightarrow> nat abs_l_vmtf_remove \<Rightarrow> nat abs_l_vmtf_remove\<close> where [simp del]:
\<open>abs_l_vmtf_bump L ((xs, ys), zs) = ((xs - {atm_of L}, ys - {atm_of L}), insert (atm_of L) zs)\<close>

fun abs_l_vmtf_bump_flush :: \<open>nat abs_l_vmtf_remove \<Rightarrow> nat abs_l_vmtf_remove\<close> where [simp del]:
\<open>abs_l_vmtf_bump_flush ((xs, ys), zs) = ((xs, ys \<union> zs), {})\<close>

lemmas abs_l_vmtf_bump_flush_def = abs_l_vmtf_bump_flush.simps
lemmas abs_l_vmtf_bump_def = abs_l_vmtf_bump.simps

lemma abs_l_vmtf_remove_inv_abs_l_vmtf_bump:
  assumes \<open>L \<in># N\<^sub>1\<close> and \<open>abs_l_vmtf_remove_inv M vm\<close> and \<open>defined_lit M L\<close>
  shows \<open>abs_l_vmtf_remove_inv M (abs_l_vmtf_bump L vm)\<close>
  using assms
  by (fastforce simp: abs_l_vmtf_remove_inv_def abs_l_vmtf_bump_def Decided_Propagated_in_iff_in_lits_of_l
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of lits_of_def uminus_lit_swap)

lemma abs_l_vmtf_remove_inv_abs_l_vmtf_bump_flush:
  assumes \<open>abs_l_vmtf_remove_inv M vm\<close>
  shows \<open>abs_l_vmtf_remove_inv M (abs_l_vmtf_bump_flush vm)\<close>
  using assms by (auto simp: abs_l_vmtf_remove_inv_def abs_l_vmtf_bump_flush_def Decided_Propagated_in_iff_in_lits_of_l
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of)


definition abs_l_vmtf_unset :: \<open>nat literal \<Rightarrow> nat abs_l_vmtf \<Rightarrow> nat abs_l_vmtf nres\<close> where
\<open>abs_l_vmtf_unset L \<equiv> \<lambda>(xs, zs). do {
    if atm_of L \<in> zs
    then do {
        zs' \<leftarrow> SPEC (\<lambda>zs'. zs' \<subseteq> zs \<and> atm_of L \<in> zs');
        RETURN (xs \<union> zs', zs-zs')
    }
    else RETURN (xs, zs)
  }\<close>

lemma abs_l_vmtf_remove_inv_abs_l_vmtf_unset:
  assumes \<open>abs_l_vmtf_inv M vm\<close> and \<open>undefined_lit M L\<close>
  shows \<open>abs_l_vmtf_unset L vm \<le> SPEC (abs_l_vmtf_inv M)\<close>
  using assms unfolding abs_l_vmtf_unset_def
  apply (cases vm)
  apply clarify
  apply refine_vcg
  by (fastforce simp: abs_l_vmtf_remove_inv_def abs_l_vmtf_bump_def Decided_Propagated_in_iff_in_lits_of_l
    in_N\<^sub>1_atm_of_in_atms_of_iff atm_of_eq_atm_of lits_of_def uminus_lit_swap)

definition abs_l_vmtf_find_next :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_l_vmtf \<Rightarrow> (nat option \<times> nat abs_l_vmtf) nres\<close> where
\<open>abs_l_vmtf_find_next M vm = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(L, vm).
       (L = None \<longrightarrow> abs_l_vmtf_inv M vm) \<and>
       (L \<noteq> None \<longrightarrow> (abs_l_vmtf_inv (Decided (Pos (the L)) # M) vm \<and> undefined_lit M (Pos (the L))))\<^esup>
      (\<lambda>(x, (xs, zs)). x = None \<and> xs \<noteq> {})
      (\<lambda>(x, (xs, zs)). do {
          ASSERT(xs \<noteq> {});
          x \<leftarrow> SPEC(\<lambda>x. x \<in> xs);
          if undefined_lit M (Pos x) then RETURN (Some x, (xs - {x}, insert x zs))
          else RETURN (None, (xs - {x}, insert x zs))
      })
      (None, vm)
  }\<close>

lemma abs_l_vmtf_remove_inv_abs_l_vmtf_find_next:
  assumes \<open>abs_l_vmtf_inv M vm\<close>
  shows \<open>abs_l_vmtf_find_next M vm \<le> SPEC (\<lambda>(L, vm).
      (L = None \<longrightarrow> (abs_l_vmtf_inv M vm \<and> (\<forall>L\<in>#N\<^sub>1. defined_lit M L))) \<and>
      (L \<noteq> None \<longrightarrow> (abs_l_vmtf_inv (Decided (Pos (the L)) # M) vm \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  have body_defined_abs: \<open>abs_l_vmtf_inv M' vm'\<close>
    if  \<open>abs_l_vmtf_inv M vm\<close> and \<open>M' = M\<close> and
        \<open>vm' = (xs - {L}, insert L zs)\<close> and
        \<open>vm = (xs, zs)\<close> and
        def_L: \<open>\<not>undefined_lit M (Pos L)\<close> and
        \<open>L \<in> xs\<close>
    for vm vm' xs zs M M' L
    proof -
        have \<open>L \<in> atm_of ` lits_of_l M\<close>
        using def_L by (metis (full_types) Decided_Propagated_in_iff_in_lits_of_l atm_of_uminus
            image_iff literal.sel(1))
        then show ?thesis
        using that by (auto simp: abs_l_vmtf_remove_inv_def)
    qed
  show ?thesis
    using assms unfolding abs_l_vmtf_find_next_def
    apply (cases vm)
    apply clarify
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(x, (xs, zs)). card xs)\<close>])
    subgoal by auto -- \<open>well-foundedness\<close>
    subgoal by auto -- \<open>WHILE inital round\<close>
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (auto simp: abs_l_vmtf_remove_inv_def) -- \<open>body if undefined\<close>
    subgoal by (auto simp: abs_l_vmtf_remove_inv_def)
    subgoal by auto
    subgoal by (simp add: abs_l_vmtf_remove_inv_def card_Diff1_less del:  card_Diff_insert)
      -- \<open>Termination\<close>
    subgoal by (rule body_defined_abs) simp_all+ -- \<open>body if defined\<close>
    subgoal by (auto simp: abs_l_vmtf_remove_inv_def)
    subgoal by (auto simp: abs_l_vmtf_remove_inv_def)
    subgoal by (simp add:  abs_l_vmtf_remove_inv_def card_Diff1_less
        del: card_Diff_insert)-- \<open>Termination\<close>
    subgoal by (auto simp: abs_l_vmtf_remove_inv_def) --\<open>final theorem\<close>
    subgoal by (auto simp: abs_l_vmtf_remove_inv_def Decided_Propagated_in_iff_in_lits_of_l
        atm_of_in_atm_of_set_in_uminus atms_of_def dest!: atm_of_in_atm_of_set_in_uminus)
    subgoal by fast
    subgoal by fast
    done
qed

lemma abs_l_vmtf_remove_inv_change_hd:
  assumes \<open>atm_of (lit_of L) = atm_of (lit_of L')\<close>
  shows \<open>abs_l_vmtf_remove_inv (L # M) (vm, {}) \<longleftrightarrow> abs_l_vmtf_remove_inv (L' # M) (vm, {})\<close>
  using assms by (auto simp: abs_l_vmtf_remove_inv_def)


subsubsection \<open>Implementation\<close>

type_synonym vmtf_imp = \<open>nat l_vmtf_atm list × nat × nat option × nat option × nat list\<close>

definition vmtf_imp :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat abs_l_vmtf_remove \<times> vmtf_imp) set\<close> where
\<open>vmtf_imp M = {(((xs, ys), zs), (A, m, lst, next_search, removed)). 
   (\<exists>xs' ys'. xs = set xs' \<and> ys = set ys' \<and> zs = set removed
   \<and> l_vmtf (rev ys' @ rev xs') m A \<and> lst = option_last (xs' @ ys') \<and> next_search = option_last xs'
   \<and> abs_l_vmtf_remove_inv M ((xs, ys), zs) \<and> l_vmtf_notin (rev ys' @ rev xs') m A
  )}\<close>

definition vmtf_dequeue :: \<open>vmtf_imp \<Rightarrow> nat \<Rightarrow> vmtf_imp\<close> where
\<open>vmtf_dequeue \<equiv> (\<lambda>(A, m, lst, next_search, removed) L.
  (l_vmtf_dequeue A L, m, if lst = Some L then get_next (A ! L) else lst,
     if next_search = Some L then get_next (A ! L) else next_search, L # removed))
\<close>

(* TODO Move *)
lemma (in -) distinct_remove1_rev: \<open>distinct xs \<Longrightarrow> remove1 x (rev xs) = rev (remove1 x xs)\<close>
  using split_list[of x xs]
  by (cases \<open>x \<in> set xs\<close>) (auto simp: remove1_append remove1_idem)

lemma abs_l_vmtf_bump_vmtf_dequeue:
  assumes \<open>(vm, (A, m, lst, next_search, removed)) \<in> vmtf_imp M\<close> and
    L: \<open>L \<in># N\<^sub>1\<close> and
    def_L: \<open>defined_lit M L\<close> and
    atm_L_A: \<open>atm_of L < length A\<close>
  shows \<open>(abs_l_vmtf_bump L vm, vmtf_dequeue (A, m, lst, next_search, removed) (atm_of L)) \<in> vmtf_imp M\<close>
  unfolding vmtf_imp_def abs_l_vmtf_bump_def
proof clarify
  fix xxs yys zzs A' m' lst' next_search' removed'
  assume
    dump: \<open>((xxs, yys), zzs) = abs_l_vmtf_bump L vm\<close> and
    dequeue: \<open>vmtf_dequeue (A, m, lst, next_search, removed) (atm_of L) = (A', m', lst', next_search', removed')\<close>
  have A': \<open>A' = l_vmtf_dequeue A (atm_of L)\<close> and
    lst': \<open>lst' = (if lst = Some (atm_of L) then get_next (A ! (atm_of L)) else lst)\<close> and
    m'm: \<open>m' = m\<close> and
    removed: \<open>removed' = atm_of L # removed\<close>
    using dequeue unfolding vmtf_dequeue_def by auto
  obtain xs ys zs where
    xs: \<open>set xs = fst (fst vm)\<close> and
    ys: \<open>set ys = snd (fst vm)\<close> and
    zs: \<open>set zs = snd vm\<close> and
    zs': \<open>set zs = set removed\<close> and
    vmtf: \<open>l_vmtf (rev ys @ rev xs) m A\<close> and
    notin: \<open>l_vmtf_notin (rev ys @ rev xs) m A\<close> and
    next_search: \<open>next_search = option_last xs\<close> and
    abs_inv: \<open>abs_l_vmtf_remove_inv M vm\<close> and
    lst: \<open>lst = option_last (xs @ ys)\<close>
    using assms unfolding vmtf_imp_def by (cases vm) auto
  let ?ys = \<open>rev ys\<close>
  let ?xs = \<open>rev xs\<close>
  have dist: \<open>distinct (xs @ ys)\<close>
    using l_vmtf_distinct[OF vmtf] by auto
  have xs_ys: \<open>remove1 (atm_of L) (rev ys) @ remove1 (atm_of L) (rev xs) =
    remove1 (atm_of L) (rev ys @ rev xs)\<close>
    using dist by (auto simp: remove1_append remove1_idem disjoint_iff_not_equal
        intro!: remove1_idem)
  have remove_rev_xs_ys:
    \<open>remove1 (atm_of L) (rev ys @ rev xs) = rev (remove1 (atm_of L) ys) @ rev (remove1 (atm_of L) xs)\<close>
    using dist by (auto simp: remove1_append distinct_remove1_rev intro: remove1_idem[symmetric])
  have remove_xs_ys: \<open>remove1 (atm_of L) (xs @ ys) = remove1 (atm_of L) xs @ remove1 (atm_of L) ys\<close>
     by (metis dist remove_rev_xs_ys rev_append rev_rev_ident distinct_remove1_rev)
  have \<open>xxs = set (remove1 (atm_of L) xs)\<close>
    using dump xs ys zs dist by (cases vm; auto simp: abs_l_vmtf_bump_def)
  moreover have \<open>yys = set (remove1 (atm_of L) ys)\<close>
    using dump xs ys zs dist by (cases vm; auto simp: abs_l_vmtf_bump_def)
  moreover have \<open>zzs = set (atm_of L # zs)\<close>
    using dump xs ys zs dist by (cases vm; auto simp: abs_l_vmtf_bump_def)
  moreover have \<open>l_vmtf (remove1 (atm_of L) (rev ys) @ remove1 (atm_of L) (rev xs)) m' A'\<close>
    using l_vmtf_l_vmtf_dequeue[OF vmtf notin, of \<open>atm_of L\<close>] dequeue dist atm_L_A
    unfolding vmtf_dequeue_def by (auto split: if_splits simp: xs_ys)
  moreover {
    have \<open>[hd (rev xs), hd (tl (rev xs))] @ tl (tl (rev xs)) = rev xs\<close>
      if \<open>xs \<noteq> []\<close> \<open>tl xs \<noteq> []\<close>
      apply (cases xs rule: rev_cases; cases \<open>tl xs\<close> rule: rev_cases)
       using that by (auto simp: tl_append split: list.splits)
    then have [simp]: \<open>get_next (A ! last xs) = option_last (remove1 (last xs) xs)\<close> if \<open>xs \<noteq> []\<close>
      using l_vmtf_last_mid_get_next[of \<open>?ys\<close> \<open>hd ?xs\<close>
          \<open>hd (tl ?xs)\<close> \<open>tl (tl ?xs)\<close> m A] vmtf l_vmtf_distinct[OF vmtf] that
        distinct_remove1_last_butlast[of xs] (* TODO proof *)
      by (cases xs rule: rev_cases; cases \<open>tl xs\<close> rule: rev_cases)
        (auto simp: tl_append l_vmtf_last_next split: list.splits elim: l_vmtfE)
    have \<open>xs \<noteq> [] \<Longrightarrow> xs \<noteq> [atm_of L] \<Longrightarrow>  atm_of L \<noteq> last xs \<Longrightarrow> last xs = last (remove1 (atm_of L) xs)\<close>
      by (induction xs)  (auto simp: remove1_Nil_iff)
    then have [simp]: \<open>option_last xs = option_last (remove1 (atm_of L) xs)\<close> if \<open>atm_of L \<noteq> last xs\<close>
      using that l_vmtf_distinct[OF vmtf]
      by (auto simp: option_last_def remove1_Nil_iff)
    have \<open>next_search' = option_last (remove1 (atm_of L) xs)\<close>
      using dequeue dist atm_L_A next_search unfolding vmtf_dequeue_def
      by (auto split: if_splits simp: xs_ys) } note next_search' = this
  moreover {
    have \<open>[hd (rev ys), hd (tl (rev ys))] @ tl (tl (rev ys)) = rev ys\<close>
      if \<open>ys \<noteq> []\<close> \<open>tl ys \<noteq> []\<close>
      apply (cases ys rule: rev_cases)
       using that by (auto simp: tl_append split: list.splits)
    then have \<open>get_next (A ! last (xs @ ys)) = option_last (remove1 (last (xs @ ys)) (xs @ ys))\<close>
      if \<open>xs @ ys \<noteq> []\<close>
      using l_vmtf_last_next[of \<open>?xs @ butlast ?ys\<close> \<open>last ?ys\<close>] that
      using l_vmtf_last_next[of \<open>butlast ?xs\<close> \<open>last ?xs\<close>]  vmtf dist
        distinct_remove1_last_butlast[of \<open>?ys @ ?xs\<close>] (* TODO proof *)
      by (cases ys rule: rev_cases; cases \<open>tl ys\<close> rule: rev_cases)
         (auto simp: tl_append l_vmtf_last_prev option_last_def remove1_append butlast_append
          split: list.splits if_splits elim: l_vmtfE)
    moreover have \<open>last ys \<notin> set xs\<close> if \<open>ys \<noteq> []\<close>
      using l_vmtf_distinct[OF vmtf] that by (cases ys rule: rev_cases) auto
    ultimately have \<open>lst' = option_last (remove1 (atm_of L) (xs @ ys))\<close>
      using dequeue dist atm_L_A lst l_vmtf_distinct[OF vmtf] vmtf
      unfolding vmtf_dequeue_def
      apply (cases ys rule: rev_cases)
      subgoal by (auto simp: remove1_append option_last_remove1_not_last split: if_splits)
      subgoal by (auto simp: remove1_append remove1_Nil_iff)
      done
  }
  moreover have \<open>abs_l_vmtf_remove_inv M ((xxs, yys), zzs)\<close>
    unfolding dump by (rule abs_l_vmtf_remove_inv_abs_l_vmtf_bump)
      (use def_L L abs_inv in auto)
  moreover have \<open>l_vmtf_notin (remove1 (atm_of L) ?ys @ remove1 (atm_of L) ?xs) m' A'\<close>
    unfolding xs_ys A'
    apply (rule l_vmtf_notin_dequeue)
    subgoal using vmtf unfolding m'm .
    subgoal using notin unfolding m'm .
    subgoal using atm_L_A .
    done
  ultimately show \<open>\<exists>xs' ys'.
       xxs = set xs' \<and>
       yys = set ys' \<and>
       zzs = set removed' \<and>
       l_vmtf (rev ys' @ rev xs') m' A' \<and>
       lst' = option_last (xs' @ ys') \<and>
       next_search' = option_last xs' \<and>
       abs_l_vmtf_remove_inv M ((xxs, yys), zzs) \<and>
       l_vmtf_notin (rev ys' @ rev xs') m' A'\<close>
    apply -
    apply (rule exI[of _ \<open>remove1 (atm_of L) xs\<close>])
    apply (rule exI[of _ \<open>remove1 (atm_of L) ys\<close>])
    unfolding xs_ys remove_xs_ys remove_rev_xs_ys removed 
    by (clarsimp simp: zs')
qed

definition vmtf_add_one :: \<open>_ \<Rightarrow> nat \<Rightarrow> _\<close> where
\<open>vmtf_add_one = (\<lambda>(A, m, lst, next_search) L.
  (A[L := l_vmtf_ATM m lst None], m+1, Some L, next_search))\<close>

definition vmtf_flush :: \<open>vmtf_imp \<Rightarrow> nat \<Rightarrow> vmtf_imp nres\<close> where
\<open>vmtf_flush \<equiv> (\<lambda>(A, m, lst, next_search, removed) L. do {
    removed' \<leftarrow> SPEC (\<lambda>removed'. mset removed' = mset removed);
    (_, (A, m, lst, next_search)) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i,(A, m, lst, next_search)). i < length removed)
      (\<lambda>(i,(A, m, lst, next_search)). do {
         ASSERT(i < length removed);
         RETURN (i+1, vmtf_add_one (A, m, lst, next_search) L)})
      (0, (A, m, lst, next_search));
    RETURN (A, m, lst, next_search, [])
  })\<close>
      

  
end

end