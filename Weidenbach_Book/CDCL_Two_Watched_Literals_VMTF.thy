theory CDCL_Two_Watched_Literals_VMTF
imports CDCL_Two_Watched_Literals_List_Watched_Domain
begin


declare nth_list_update[simp]
text \<open>
  This a version of @{thm nth_list_update} with a different condition (\<^term>\<open>j\<close>
  instead of \<^term>\<open>i\<close>). This is more useful here.
  \<close>
(* TODO: Move*)
lemma nth_list_update_le'[simp]:
  "j < length xs \<Longrightarrow> (xs[i:=x])!j = (if i = j then x else xs!j)"
  by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)
(* End Move *)


subsection \<open>Variable-Move-to-Front\<close>

subsubsection \<open>Variants around head and last\<close>

definition option_hd :: \<open>'a list \<Rightarrow> 'a option\<close> where
  \<open>option_hd xs = (if xs = [] then None else Some (hd xs))\<close>

lemma option_hd_None_iff[iff]: \<open>option_hd zs = None \<longleftrightarrow> zs = []\<close>  \<open>None = option_hd zs \<longleftrightarrow> zs = []\<close>
  by (auto simp: option_hd_def)

lemma option_hd_Some_iff[iff]: \<open>option_hd zs = Some y \<longleftrightarrow> (zs \<noteq> [] \<and> y = hd zs)\<close>
  \<open>Some y = option_hd zs \<longleftrightarrow> (zs \<noteq> [] \<and> y = hd zs)\<close>
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

lemma option_hd_rev: \<open>option_hd (rev xs) = option_last xs\<close>
  by (cases xs rule: rev_cases) auto

lemma map_option_option_last:
  \<open>map_option f (option_last xs) = option_last (map f xs)\<close>
  by (cases xs rule: rev_cases) auto


subsubsection \<open>Specification\<close>

type_synonym 'v abs_l_vmtf = \<open>'v set \<times> 'v set\<close>
type_synonym 'v abs_l_vmtf_remove = \<open>'v abs_l_vmtf \<times> 'v set\<close>

datatype 'v al_vmtf_atm = l_vmtf_ATM (stamp : nat) (get_prev: \<open>'v option\<close>) (get_next: \<open>'v option\<close>)
type_synonym l_vmtf_atm = \<open>nat al_vmtf_atm\<close>

inductive l_vmtf :: \<open>nat list \<Rightarrow> nat \<Rightarrow> l_vmtf_atm list \<Rightarrow> bool\<close> where
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
definition l_vmtf_dequeue :: \<open>nat \<Rightarrow> l_vmtf_atm list \<Rightarrow> l_vmtf_atm list\<close> where
\<open>l_vmtf_dequeue y xs =
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
  by (metis length_list_update nth_list_update_eq nth_list_update_neq option.distinct(1)
   al_vmtf_atm.sel(2))

lemma l_vmtf_last_next:
  \<open>l_vmtf (xs @ [x]) m A \<Longrightarrow> get_next (A ! x) = None\<close>
  apply (induction "xs @ [x]" m A arbitrary: xs x rule: l_vmtf.induct) (* TODO Proof *)
    apply auto
  by (metis list.distinct(1) list.sel(3) list.set_intros(1) nth_list_update_eq nth_list_update_neq
      self_append_conv2 tl_append2 al_vmtf_atm.sel(3) l_vmtf_le_length)

lemma l_vmtf_last_mid_get_next:
  \<open>l_vmtf (xs @ [x, y] @ zs) m A \<Longrightarrow> get_next (A ! x) = Some y\<close>
  apply (induction "xs @ [x, y] @ zs" m A arbitrary: xs x rule: l_vmtf.induct) (* TODO Proof *)
    apply auto
  by (metis list.sel(1) list.sel(3) list.set_intros(1) nth_list_update_eq nth_list_update_neq
      self_append_conv2 tl_append2 al_vmtf_atm.sel(3) l_vmtf_le_length)

lemma l_vmtf_last_mid_get_next_option_hd:
  \<open>l_vmtf (xs @ x # zs) m A \<Longrightarrow> get_next (A ! x) = option_hd zs\<close>
  using l_vmtf_last_mid_get_next[of xs x \<open>hd zs\<close> \<open>tl zs\<close> m A]
  l_vmtf_last_next[of xs x]
  by (cases zs) auto

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

lemma length_l_vmtf_dequeue[simp]: \<open>length (l_vmtf_dequeue x A) = length A\<close>
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

definition l_vmtf_notin where
  \<open>l_vmtf_notin l m xs \<longleftrightarrow> (\<forall>i<length xs. i\<notin>set l \<longrightarrow> (get_prev (xs ! i) = None \<and>
      get_next (xs ! i) = None))\<close>

lemma l_vmtf_notinI:
  \<open>(\<And>i. i <length xs \<Longrightarrow> i\<notin>set l \<Longrightarrow> get_prev (xs ! i) = None \<and>
      get_next (xs ! i) = None) \<Longrightarrow> l_vmtf_notin l m xs\<close>
  by (auto simp: l_vmtf_notin_def)

lemma stamp_l_vmtf_dequeue:
  \<open>axs < length zs \<Longrightarrow> stamp (l_vmtf_dequeue x zs ! axs) = stamp (zs ! axs)\<close>
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

lemma l_vmtf_l_vmtf_dequeue:
  assumes l_vmtf: \<open>l_vmtf l m A\<close> and notin: \<open>l_vmtf_notin l m A\<close> and valid: \<open>x < length A\<close>
  shows \<open>l_vmtf (remove1 x l) m (l_vmtf_dequeue x A)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  have
      \<open>get_prev (A ! x) = None \<close> and
      \<open>get_next (A ! x) = None\<close>
    using notin False valid unfolding l_vmtf_notin_def by auto
  then have l_vmtf_eq: \<open>(l_vmtf_dequeue x A) ! a = A ! a\<close> if \<open>a \<in> set l\<close> for a
    using that False valid unfolding l_vmtf_notin_def l_vmtf_dequeue_def
    by (cases \<open>A ! (the (get_prev (A ! x)))\<close>; cases \<open>A ! (the (get_next (A ! x)))\<close>)
      (auto simp: Let_def split: option.splits)
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
         x := l_vmtf_ATM (stamp (A' ! x)) None None] = l_vmtf_dequeue x A\<close>
      using l_vmtf_last_mid_get_next[OF l_vmtf_x_y] l_vmtf_last_mid_get_prev[OF l_vmtf_x'_x]
      unfolding A'_def l_vmtf_dequeue_def (* TODO proof *)
      apply (auto simp: Let_def)
        by (metis (no_types, lifting) list_update_overwrite list_update_swap)
    ultimately show ?thesis
      by force
  qed
qed

lemma l_vmtf_hd_next:
   \<open>l_vmtf (x # a # list) m A \<Longrightarrow> get_next (A ! x) = Some a\<close>
  by (auto 5 5 elim: l_vmtfE)

lemma l_vmtf_notin_dequeue:
  assumes l_vmtf: \<open>l_vmtf l m A\<close> and notin: \<open>l_vmtf_notin l m A\<close> and valid: \<open>x < length A\<close>
  shows \<open>l_vmtf_notin (remove1 x l) m (l_vmtf_dequeue x A)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  have
    \<open>get_prev (A ! x) = None\<close> and
    \<open>get_next (A ! x) = None\<close>
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
           split: option.splits)
  next
    case xs_empty_zs_nempty note xs = this(1) and zs = this(1)
    have prev_next: \<open>get_prev (A ! x) = None\<close> \<open>get_next (A ! x) = option_hd zs\<close>
      using l_vmtf unfolding l xs zs
      by (cases zs; auto simp: option_hd_def elim: l_vmtfE dest: l_vmtf_hd_next)+
    show ?thesis
      apply (rule l_vmtf_notinI)
      apply (case_tac \<open>i = x\<close>)
      subgoal
        using l_vmtf prev_next unfolding r_l unfolding l xs zs
        by (cases zs) (auto simp: l_vmtf_dequeue_def Let_def
            l_vmtf_notin_def l_vmtf_single_iff
            split: option.splits)
      subgoal
        using l_vmtf notin prev_next unfolding r_l unfolding l xs zs
        by (auto simp: l_vmtf_dequeue_def Let_def
            l_vmtf_notin_def l_vmtf_single_iff
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
      by (auto simp: l_vmtf_notin_def l_vmtf_dequeue_def)
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
      nth_list_update_eq nth_list_update_neq al_vmtf_atm.collapse al_vmtf_atm.sel(2,3))

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

paragraph \<open>Abstract Invariants\<close>

text \<open>
  Invariants
  \<^item> The atoms of \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close> are always disjoint.
  \<^item> The atoms of \<^term>\<open>ys\<close> are \<^emph>\<open>always\<close> set.
  \<^item> The atoms of \<^term>\<open>xs\<close> \<^emph>\<open>can\<close> be set but do not have to.
  \<^item> The atoms of \<^term>\<open>zs\<close> are either in \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close>.
\<close>

definition abs_l_vmtf_remove_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_l_vmtf_remove \<Rightarrow> bool\<close> where
\<open>abs_l_vmtf_remove_inv M \<equiv> \<lambda>((xs, ys), zs).
  (\<forall>L\<in>ys. L \<in> atm_of ` lits_of_l M) \<and>
  xs \<inter> ys = {} \<and>
  zs \<subseteq> xs \<union> ys \<and>
  xs \<union> ys = atms_of N\<^sub>1
  \<close>

abbreviation abs_l_vmtf_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_l_vmtf \<Rightarrow> bool\<close> where
\<open>abs_l_vmtf_inv M vm \<equiv> abs_l_vmtf_remove_inv M (vm, {})\<close>


subsubsection \<open>Implementation\<close>

type_synonym (in -) vmtf_imp = \<open>l_vmtf_atm list \<times> nat \<times> nat option \<times> nat option\<close>
type_synonym (in -) vmtf_imp_remove = \<open>vmtf_imp \<times> nat list\<close>

text \<open>
  We use the opposite direction of the VMTF paper: The latest added element \<^term>\<open>lst\<close> is at
  the beginning.
\<close>

definition vmtf_imp :: \<open>(nat, nat) ann_lits \<Rightarrow> vmtf_imp_remove set\<close> where
\<open>vmtf_imp M = {((A, m, lst, next_search), removed).
   (\<exists>xs' ys'.
     l_vmtf (ys' @ xs') m A \<and> lst = option_hd (ys' @ xs') \<and> next_search = option_hd xs'
   \<and> abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed) \<and> l_vmtf_notin (ys' @ xs') m A
   \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length A) \<and> (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)
  )}\<close>

lemma vmtf_imp_consD:
  assumes vmtf: \<open>((A, m, lst, next_search), remove) \<in> vmtf_imp M\<close>
  shows \<open>((A, m, lst, next_search), remove) \<in> vmtf_imp (L # M)\<close>
proof -
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  moreover have \<open>abs_l_vmtf_remove_inv (L # M) ((set xs', set ys'), set remove)\<close>
    using abs_vmtf unfolding abs_l_vmtf_remove_inv_def by auto
  ultimately have \<open>l_vmtf (ys' @ xs') m A \<and>
       lst = option_hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       abs_l_vmtf_remove_inv (L # M) ((set xs', set ys'), set remove) \<and>
       l_vmtf_notin (ys' @ xs') m A \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length A) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
      by fast
  then show ?thesis
    unfolding vmtf_imp_def by fast
qed

definition vmtf_dequeue :: \<open>nat \<Rightarrow> vmtf_imp \<Rightarrow> vmtf_imp\<close> where
\<open>vmtf_dequeue \<equiv> (\<lambda>L (A, m, lst, next_search).
  (l_vmtf_dequeue L A, m, if lst = Some L then get_next (A ! L) else lst,
     if next_search = Some L then get_next (A ! L) else next_search))\<close>

text \<open>It would be better to distinguish whether L is set in M or not.\<close>
definition vmtf_enqueue :: \<open>nat \<Rightarrow> vmtf_imp \<Rightarrow>  vmtf_imp\<close> where
\<open>vmtf_enqueue = (\<lambda>L (A, m, lst, next_search).
  (case lst of
    None \<Rightarrow> (A[L := l_vmtf_ATM m lst None], m+1, Some L, Some L)
  | Some lst \<Rightarrow>
      (A[L := l_vmtf_ATM (m+1) None (Some lst),
         lst := l_vmtf_ATM (stamp (A!lst)) (Some L) (get_next (A!lst))],
      m+1, Some L, Some L)))\<close>

definition vmtf_en_dequeue :: \<open>nat \<Rightarrow> vmtf_imp \<Rightarrow>  vmtf_imp\<close> where
\<open>vmtf_en_dequeue = (\<lambda>L. vmtf_enqueue L o vmtf_dequeue L)\<close>

(*TODO: Move*)
lemma (in -) in_set_remove1D:
  \<open>a \<in> set (remove1 x xs) \<Longrightarrow> a \<in> set xs\<close>
  by (meson notin_set_remove1)

lemma (in -) take_length_takeWhile_eq_takeWhile:
  \<open>take (length (takeWhile P xs)) xs = takeWhile P xs\<close>
  by (induction xs) auto
(*End Move*)

lemma abs_l_vmtf_bump_vmtf_dequeue:
  fixes M
  assumes vmtf:\<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close>  and
    L: \<open>L \<in> atms_of N\<^sub>1\<close> and
    dequeue: \<open>(A', m', lst', next_search') = vmtf_dequeue L (A, m, lst, next_search)\<close>
  shows \<open>\<exists>xs' ys'. l_vmtf (ys' @ xs') m' A' \<and> lst' = option_hd (ys' @ xs')
   \<and> next_search' = option_hd xs' \<and> abs_l_vmtf_remove_inv M ((insert L (set xs'), set ys'), set removed)
   \<and> l_vmtf_notin (ys' @ xs') m' A' \<and>
   L \<notin> set (ys' @ xs') \<and> (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
  unfolding vmtf_imp_def
proof -
  have A': \<open>A' = l_vmtf_dequeue L A\<close> and
    lst': \<open>lst' = (if lst = Some L then get_next (A ! L) else lst)\<close> and
    m'm: \<open>m' = m\<close>
    using dequeue unfolding vmtf_dequeue_def by auto
  obtain xs ys where
    vmtf: \<open>l_vmtf (ys @ xs) m A\<close> and
    notin: \<open>l_vmtf_notin (ys @ xs) m A\<close> and
    next_search: \<open>next_search = option_hd xs\<close> and
    abs_inv: \<open>abs_l_vmtf_remove_inv M ((set xs, set ys), set removed)\<close> and
    lst: \<open>lst = option_hd (ys @ xs)\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    L_ys_xs: \<open>\<forall>L\<in>set (ys @ xs). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by auto
  let ?ys = \<open>ys\<close>
  let ?xs = \<open>xs\<close>
  have dist: \<open>distinct (xs @ ys)\<close>
    using l_vmtf_distinct[OF vmtf] by auto
  have xs_ys: \<open>remove1 L ys @ remove1 L xs = remove1 L (ys @ xs)\<close>
    using dist by (auto simp: remove1_append remove1_idem disjoint_iff_not_equal
        intro!: remove1_idem)
  have atm_L_A: \<open>L < length A\<close>
    using atm_A L by blast

  have \<open>l_vmtf (remove1 L ys @ remove1 L xs) m' A'\<close>
    using l_vmtf_l_vmtf_dequeue[OF vmtf notin, of L] dequeue dist atm_L_A
    unfolding vmtf_dequeue_def by (auto split: if_splits simp: xs_ys)
  moreover have next_search': \<open>next_search' = option_hd (remove1 L xs)\<close>
  proof -
    have \<open>[hd xs, hd (tl xs)] @ tl (tl xs) = xs\<close>
      if \<open>xs \<noteq> []\<close> \<open>tl xs \<noteq> []\<close>
      apply (cases xs; cases \<open>tl xs\<close>)
       using that by (auto simp: tl_append split: list.splits)
    then have [simp]: \<open>get_next (A ! hd xs) = option_hd (remove1 (hd xs) xs)\<close> if \<open>xs \<noteq> []\<close>
      using l_vmtf_last_mid_get_next[of \<open>?ys\<close> \<open>hd ?xs\<close>
          \<open>hd (tl ?xs)\<close> \<open>tl (tl ?xs)\<close> m A] vmtf l_vmtf_distinct[OF vmtf] that
        distinct_remove1_last_butlast[of xs] (* TODO proof *)
      by (cases xs; cases \<open>tl xs\<close>)
        (auto simp: tl_append l_vmtf_last_next split: list.splits elim: l_vmtfE)
    have \<open>xs \<noteq> [] \<Longrightarrow> xs \<noteq> [L] \<Longrightarrow>  L \<noteq> hd xs \<Longrightarrow> hd xs = hd (remove1 L xs)\<close>
      by (induction xs) (auto simp: remove1_Nil_iff)
    then have [simp]: \<open>option_hd xs = option_hd (remove1 L xs)\<close> if \<open>L \<noteq> hd xs\<close>
      using that l_vmtf_distinct[OF vmtf]
      by (auto simp: option_hd_def remove1_Nil_iff)
    show ?thesis
      using dequeue dist atm_L_A next_search next_search unfolding vmtf_dequeue_def
      by (auto split: if_splits simp: xs_ys dest: last_in_set)
    qed
  moreover {
    have \<open>[hd ys, hd (tl ys)] @ tl (tl ys) = ys\<close>
      if \<open>ys \<noteq> []\<close> \<open>tl ys \<noteq> []\<close>
       using that by (auto simp: tl_append split: list.splits)
    then have \<open>get_next (A ! hd (ys @ xs)) = option_hd (remove1 (hd (ys @ xs)) (ys @ xs))\<close>
      if \<open>ys @ xs \<noteq> []\<close>
      using l_vmtf_last_next[of \<open>?xs @ butlast ?ys\<close> \<open>last ?ys\<close>] that
      using l_vmtf_last_next[of \<open>butlast ?xs\<close> \<open>last ?xs\<close>]  vmtf dist
        distinct_remove1_last_butlast[of \<open>?ys @ ?xs\<close>] (* TODO proof *)
      by (cases ys; cases \<open>tl ys\<close>)
       (auto simp: tl_append l_vmtf_last_prev remove1_append hd_append remove1_Nil_iff
          split: list.splits if_splits elim: l_vmtfE)
    moreover have \<open>hd ys \<notin> set xs\<close> if \<open>ys \<noteq> []\<close>
      using l_vmtf_distinct[OF vmtf] that by (cases ys) auto
    ultimately have \<open>lst' = option_hd (remove1 L (ys @ xs))\<close>
      using dequeue dist atm_L_A lst l_vmtf_distinct[OF vmtf] vmtf
      unfolding vmtf_dequeue_def
      apply (cases ys)
      subgoal by (cases xs) (auto simp: remove1_append option_hd_def remove1_Nil_iff split: if_splits)
      subgoal by (auto simp: remove1_append option_hd_def remove1_Nil_iff)
      done
  }
  moreover have \<open>abs_l_vmtf_remove_inv M ((insert L (set (remove1 L xs)), set (remove1 L ys)),
    set removed)\<close>
    using abs_inv L dist
    unfolding abs_l_vmtf_remove_inv_def by (auto dest: in_set_remove1D)
  moreover have \<open>l_vmtf_notin (remove1 L ?ys @ remove1 L ?xs) m' A'\<close>
    unfolding xs_ys A'
    apply (rule l_vmtf_notin_dequeue)
    subgoal using vmtf unfolding m'm .
    subgoal using notin unfolding m'm .
    subgoal using atm_L_A .
    done
  moreover have \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A'\<close>
    using atm_A unfolding A' by auto
  moreover have \<open>L \<notin> set (remove1 L ys @ remove1 L xs)\<close>
    using dist by auto
  moreover have \<open>\<forall>L\<in>set (remove1 L (ys @ xs)). L \<in> atms_of N\<^sub>1\<close>
    using L_ys_xs by (auto dest: in_set_remove1D)
  ultimately show ?thesis
    apply -
    apply (rule exI[of _ \<open>remove1 L xs\<close>])
    apply (rule exI[of _ \<open>remove1 L ys\<close>])
    unfolding xs_ys
    by blast
qed

lemma l_vmtf_get_prev_not_itself:
  \<open>l_vmtf xs m A \<Longrightarrow> L \<in> set xs \<Longrightarrow> L < length A \<Longrightarrow> get_prev (A ! L) \<noteq> Some L\<close>
  apply (induction rule: l_vmtf.induct)
  subgoal by auto
  subgoal by (auto simp: l_vmtf_single_iff)
  subgoal by auto
  done

lemma l_vmtf_get_next_not_itself:
  \<open>l_vmtf xs m A \<Longrightarrow> L \<in> set xs \<Longrightarrow> L < length A \<Longrightarrow> get_next (A ! L) \<noteq> Some L\<close>
  apply (induction rule: l_vmtf.induct)
  subgoal by auto
  subgoal by (auto simp: l_vmtf_single_iff)
  subgoal by auto
  done

lemma abs_l_vmtf_bump_vmtf_en_dequeue:
  fixes M
  assumes
    vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close> and
    L: \<open>L \<in> atms_of N\<^sub>1\<close> and
    removed: \<open>mset removed' \<subseteq># remove1_mset L (mset removed)\<close>
  shows \<open>(vmtf_en_dequeue L (A, m, lst, next_search), removed') \<in> vmtf_imp M\<close>
  unfolding vmtf_imp_def
proof clarify
  fix xxs yys zzs A' m' lst' next_search'
  assume dequeue: \<open>(A', m', lst', next_search') = vmtf_en_dequeue L (A, m, lst, next_search)\<close>
  obtain xs ys where
    l_vmtf: \<open>l_vmtf (ys @ xs) m A\<close> and
    notin: \<open>l_vmtf_notin (ys @ xs) m A\<close> and
    next_search: \<open>next_search = option_hd xs\<close> and
    abs_inv: \<open>abs_l_vmtf_remove_inv M ((set xs, set ys), set removed)\<close> and
    lst: \<open>lst = option_hd (ys @ xs)\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    ys_xs_N\<^sub>1: \<open>\<forall>L\<in>set (ys @ xs). L \<in> atms_of N\<^sub>1\<close>
    using assms unfolding vmtf_imp_def by auto
  have atm_L_A: \<open>L < length A\<close>
    using atm_A L by blast
  text \<open>d stands for dequeue\<close>
  obtain Ad md lstd next_searchd where
    de: \<open>vmtf_dequeue L (A, m, lst, next_search) = (Ad, md, lstd, next_searchd) \<close>
    by (cases \<open>vmtf_dequeue L (A, m, lst, next_search)\<close>)
  obtain xs' ys' where
    l_vmtf': \<open>l_vmtf (ys' @ xs') md Ad\<close> and
    lstd: \<open>lstd = option_hd (ys' @ xs')\<close> and
    \<open>next_searchd = option_hd xs'\<close> and
    abs_l: \<open>abs_l_vmtf_remove_inv M ((insert L (set xs'), set ys'), set removed)\<close>  and
    not_in: \<open>l_vmtf_notin (ys' @ xs') md Ad\<close> and
    L_xs'_ys': \<open>L \<notin> set (ys' @ xs')\<close> and
    L_xs'_ys'_N\<^sub>1: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using abs_l_vmtf_bump_vmtf_dequeue[OF vmtf L de[symmetric]] by blast

  have lst': \<open>lst' = Some L\<close> and m': \<open>m' = md + 1\<close> and next_search': \<open>next_search' = Some L\<close>
    using dequeue unfolding vmtf_en_dequeue_def comp_def de
    by (auto simp add: vmtf_enqueue_def split: option.splits)
  have abs': \<open>abs_l_vmtf_remove_inv M ((set (L # ys' @ xs'), set []), set removed')\<close>
    using abs_l removed unfolding abs_l_vmtf_remove_inv_def
    by (auto 5 5 dest: in_diffD)
  have [simp]: \<open>length A' = length A\<close>  \<open>length Ad = length A\<close>
    using dequeue de unfolding vmtf_en_dequeue_def comp_def vmtf_dequeue_def
    by (auto simp add: vmtf_enqueue_def split: option.splits)
  have Ad: \<open>Ad = l_vmtf_dequeue L A\<close>
    using de unfolding vmtf_dequeue_def by auto
  have \<open>get_prev (Ad ! i) \<noteq> Some L\<close>  (is ?prev) and
    \<open>get_next (Ad ! i) \<noteq> Some L\<close> (is ?next)
    if
     i_le_A: \<open>i < length A\<close> and
     i_L: \<open>i \<noteq> L\<close> and
     i_ys': \<open>i \<notin> set ys'\<close> and
     i_xs': \<open>i \<notin> set xs'\<close>
     for i
  proof -
    have \<open>i \<notin> set xs\<close> \<open>i \<notin> set ys\<close> and L_xs_ys: \<open>L \<in> set xs \<or> L \<in> set ys\<close>
      using i_ys' i_xs' abs_l abs_inv i_L unfolding abs_l_vmtf_remove_inv_def
      by auto
    then have
      \<open>get_next (A ! i) = None\<close>
      \<open>get_prev (A ! i) = None\<close>
      using notin i_le_A unfolding Ad l_vmtf_notin_def l_vmtf_dequeue_def
      by (auto simp: Let_def split: option.splits)
    moreover have \<open>get_prev (A ! L) \<noteq> Some L\<close> and \<open>get_next (A ! L) \<noteq> Some L\<close>
      using l_vmtf_get_prev_not_itself[OF l_vmtf, of L] L_xs_ys atm_L_A
      l_vmtf_get_next_not_itself[OF l_vmtf, of L] by auto
    ultimately show ?next and ?prev
      using i_le_A L_xs_ys unfolding Ad l_vmtf_dequeue_def l_vmtf_notin_def
      by (auto simp: Let_def split: option.splits)
  qed
  then have l_vmtf_notin': \<open>l_vmtf_notin (L # ys' @ xs') m' A'\<close>
    using not_in dequeue unfolding vmtf_en_dequeue_def comp_def de l_vmtf_notin_def
      l_vmtf_dequeue_def
    by (auto simp add: vmtf_enqueue_def lstd hd_append split: option.splits)
  have l_vmtf: \<open>l_vmtf (L # (ys' @ xs')) m' A'\<close>
  proof (cases \<open>ys' @ xs'\<close>)
    case Nil
    then have \<open>lstd = None\<close>
      using lstd by auto
    then show ?thesis
      using atm_L_A dequeue unfolding Nil vmtf_en_dequeue_def comp_def de Ad
      by (auto simp: l_vmtf_single_iff vmtf_enqueue_def split: option.splits)
  next
    case (Cons z zs)
    let ?m = \<open>(stamp (Ad!z))\<close>
    let ?Ad = \<open>Ad[L := l_vmtf_ATM m' None (Some z)]\<close>
    have L_z_zs: \<open>L \<notin> set (z # zs)\<close>
      using L_xs'_ys' atm_L_A unfolding Cons
      by simp
    have l_vmtf_z: \<open>l_vmtf (z # zs) md Ad\<close>
      using l_vmtf' unfolding Cons .

    have l_vmtf_A: \<open>l_vmtf (z # zs) md ?Ad\<close>
      apply (rule l_vmtf_eq_iffI[of _ _ Ad])
      subgoal using L_z_zs atm_L_A by auto
      subgoal using l_vmtf_le_length[OF l_vmtf_z] by auto
      subgoal using l_vmtf_z .
      done
    have [simp]: \<open>lstd = Some z\<close>
      using lstd unfolding Cons by simp
    show ?thesis
      unfolding Cons
      apply (rule l_vmtf.Cons[of _ _ md ?Ad _ m'])
      subgoal using l_vmtf_A .
      subgoal using atm_L_A by simp
      subgoal using atm_L_A by simp
      subgoal using L_z_zs by simp
      subgoal using L_z_zs by simp
      subgoal using m' by simp_all
      subgoal
        using atm_L_A dequeue L_z_zs unfolding Nil vmtf_en_dequeue_def comp_def de Ad
        apply (cases \<open>l_vmtf_dequeue z A ! z\<close>)
        by (auto simp: l_vmtf_single_iff vmtf_enqueue_def split: option.splits)
        subgoal by linarith
      done
  qed
  have L_xs'_ys'_N\<^sub>1': \<open>\<forall>L'\<in>set ([] @ L # ys' @ xs'). L' \<in> atms_of N\<^sub>1\<close>
    using L L_xs'_ys'_N\<^sub>1 by auto
  show \<open>\<exists>xs' ys'.
       l_vmtf (ys' @ xs') m' A' \<and>
       lst' = option_hd (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed') \<and>
       l_vmtf_notin (ys' @ xs') m' A' \<and>
       (\<forall>L\<in>atms_of N\<^sub>1. L < length A') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
    apply (rule exI[of _ \<open>L # ys' @ xs'\<close>])
    apply (rule exI[of _ \<open>[]\<close>])
    using lst' next_search' abs' atm_A l_vmtf_notin' l_vmtf ys_xs_N\<^sub>1 L_xs'_ys'_N\<^sub>1'
    by simp
qed

definition vmtf_unset :: \<open>nat \<Rightarrow> vmtf_imp_remove \<Rightarrow> vmtf_imp_remove\<close> where
\<open>vmtf_unset = (\<lambda>L ((A, m, lst, next_search), removed).
  (if next_search = None \<or> stamp (A ! (the next_search)) < stamp (A ! L)
  then ((A, m, lst, Some L), removed)
  else ((A, m, lst, next_search), removed)))\<close>

lemma vmtf_imp_atm_of_ys_iff:
  assumes
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed)\<close> and
    L: \<open>L \<in> atms_of N\<^sub>1\<close>
  shows \<open>L \<in> set ys' \<longleftrightarrow> next_search = None \<or> stamp (A ! (the next_search)) < stamp (A ! L)\<close>
proof -
  let ?xs' = \<open>set xs'\<close>
  let ?ys' = \<open>set ys'\<close>
  have L_xs_ys: \<open>L \<in> ?xs' \<union> ?ys'\<close>
    using abs_vmtf L unfolding abs_l_vmtf_remove_inv_def
    by (auto simp: in_N\<^sub>1_atm_of_in_atms_of_iff)
  have dist: \<open>distinct (xs' @ ys')\<close>
    using l_vmtf_distinct[OF l_vmtf] by auto

  have sorted: \<open>sorted (map (\<lambda>a. stamp (A ! a)) (rev xs' @ rev ys'))\<close> and
    distinct: \<open>distinct (map (\<lambda>a. stamp (A ! a)) (xs' @ ys'))\<close>
    using l_vmtf_stamp_sorted[OF l_vmtf] l_vmtf_stamp_distinct[OF l_vmtf]
    by (auto simp: rev_map[symmetric])
  have next_search_xs: \<open>?xs' = {} \<longleftrightarrow> next_search = None\<close>
    using next_search by auto

  have \<open>stamp (A ! (the next_search)) < stamp (A ! L) \<Longrightarrow> L \<notin> ?xs'\<close>
    if \<open>xs' \<noteq> []\<close>
    using that sorted distinct L_xs_ys unfolding next_search
    by (cases xs') (auto simp: sorted_append)
  moreover have \<open>stamp (A ! (the next_search)) < stamp (A ! L)\<close> (is \<open>?n < ?L\<close>)
    if xs': \<open>xs' \<noteq> []\<close> and \<open>L \<in> ?ys'\<close>
  proof -
    have \<open>?n \<le> ?L\<close>
      using l_vmtf_stamp_sorted[OF l_vmtf] that last_in_set[OF xs']
      by (cases xs')
         (auto simp: rev_map[symmetric] next_search sorted_append sorted_Cons)
    moreover have \<open>?n \<noteq> ?L\<close>
      using l_vmtf_stamp_distinct[OF l_vmtf] that last_in_set[OF xs']
      by (cases xs') (auto simp: rev_map[symmetric] next_search)
    ultimately show ?thesis
      by arith
  qed
  ultimately show ?thesis
    using H L_xs_ys next_search_xs dist by auto
qed

lemma abs_l_vmtf_remove_inv_remove_mono:
  assumes
    \<open>abs_l_vmtf_remove_inv M ((a, b), remove)\<close> and
    \<open>remove' \<subseteq> remove\<close>
  shows \<open>abs_l_vmtf_remove_inv M ((a, b), remove')\<close>
  using assms unfolding abs_l_vmtf_remove_inv_def by (auto simp: mset_subset_eqD)

lemma abs_l_vmtf_unset_vmtf_unset:
  assumes vmtf:\<open>((A, m, lst, next_search), remove) \<in> vmtf_imp M\<close> and L_N: \<open>L \<in> atms_of N\<^sub>1\<close> and
    remove: \<open>mset remove' \<subseteq># mset remove\<close>
  shows \<open>(vmtf_unset L ((A, m, lst, next_search), remove')) \<in> vmtf_imp M\<close> (is \<open>?S \<in> _\<close>)
proof -
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    L_ys'_xs'_N\<^sub>1: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  obtain A' m' lst' next_search' remove'' where
    S: \<open>?S = ((A', m', lst', next_search'), remove'')\<close>
    by (cases ?S) auto
  have L_ys'_iff: \<open>L \<in> set ys' \<longleftrightarrow> (next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L))\<close>
    using vmtf_imp_atm_of_ys_iff[OF l_vmtf next_search abs_vmtf L_N] .
  have \<open>L \<in> set (xs' @ ys')\<close>
    using abs_vmtf L_N unfolding abs_l_vmtf_remove_inv_def by auto
  then have L_ys'_xs': \<open>L \<in> set ys' \<longleftrightarrow> L \<notin> set xs'\<close>
    using l_vmtf_distinct[OF l_vmtf] by auto
  have \<open>\<exists>xs' ys'.
       l_vmtf (ys' @ xs') m' A' \<and>
       lst' = option_hd (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       abs_l_vmtf_remove_inv M ((set xs', set ys'), set remove'') \<and>
       l_vmtf_notin (ys' @ xs') m' A' \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length A') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
  proof (cases \<open>L \<in> set xs'\<close>)
    case True
    then have C: \<open>\<not>(next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L))\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set remove'')\<close>
    apply (rule abs_l_vmtf_remove_inv_remove_mono)
    apply (rule abs_vmtf)
    using remove S unfolding vmtf_unset_def by (auto simp: C)
    show ?thesis
      using S True unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      apply -
      apply (simp add: C)
      using l_vmtf lst next_search abs_vmtf notin atm_A remove L_ys'_xs'_N\<^sub>1
      by auto
  next
    case False
    then have C: \<open>next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L)\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have L_ys: \<open>L \<in> set ys'\<close>
      by (use False L_ys'_xs' in auto)
    define y_ys where \<open>y_ys \<equiv> takeWhile (op \<noteq> L) ys'\<close>
    define x_ys where \<open>x_ys \<equiv> drop (length y_ys) ys'\<close>
    let ?ys' = \<open>y_ys\<close>
    let ?xs' = \<open>x_ys @ xs'\<close>
    have x_ys_take_ys': \<open>y_ys = take (length y_ys) ys'\<close>
        unfolding y_ys_def (* TODO: proof *)
        apply (subst take_length_takeWhile_eq_takeWhile[of \<open>op \<noteq> L\<close> \<open>ys'\<close>, symmetric])
        by (smt L_ys hd_drop_conv_nth le_neq_implies_less length_append_singleton
          length_takeWhile_le nth_length_takeWhile set_takeWhileD take_all take_hd_drop
          take_length_takeWhile_eq_takeWhile)
    have ys'_y_x: \<open>ys' = y_ys @ x_ys\<close>
      by (subst x_ys_take_ys') (auto simp: x_ys_def)
    have y_ys_le_ys': \<open>length y_ys < length ys'\<close>
      using L_ys by (metis (full_types) append_eq_conv_conj append_self_conv le_antisym
        length_takeWhile_le not_less takeWhile_eq_all_conv x_ys_take_ys' y_ys_def)
    from nth_length_takeWhile[OF this[unfolded y_ys_def]] have [simp]: \<open>x_ys \<noteq> []\<close> \<open>hd x_ys = L\<close>
      using y_ys_le_ys' unfolding x_ys_def y_ys_def
      by (auto simp: x_ys_def y_ys_def hd_drop_conv_nth)
    have [simp]: \<open>A' = A\<close> \<open>m' = m\<close> \<open>lst' = lst\<close> \<open>next_search' = Some L\<close> \<open>remove'' = remove'\<close>
      using S unfolding vmtf_unset_def by (auto simp: C)

    have \<open>l_vmtf (?ys' @ ?xs') m A\<close>
      using l_vmtf unfolding ys'_y_x by simp
    moreover have \<open>lst' = option_hd (?ys' @ ?xs')\<close>
      using lst unfolding ys'_y_x by simp
    moreover have \<open>next_search' = option_hd ?xs'\<close>
      by auto
    moreover {
      have \<open>abs_l_vmtf_remove_inv M ((set ?xs', set ?ys'), set remove)\<close>
        using abs_vmtf l_vmtf_distinct[OF l_vmtf] unfolding abs_l_vmtf_remove_inv_def ys'_y_x
        by auto
      then have \<open>abs_l_vmtf_remove_inv M ((set ?xs', set ?ys'), set remove')\<close>
        by (rule abs_l_vmtf_remove_inv_remove_mono) (use remove in auto)
      }
    moreover have \<open>l_vmtf_notin (?ys' @ ?xs') m A\<close>
      using notin unfolding ys'_y_x by simp
    moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of N\<^sub>1\<close>
      using L_ys'_xs'_N\<^sub>1 unfolding ys'_y_x by auto
    ultimately show ?thesis
      using S False atm_A unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      by (fastforce simp add: C)
  qed
  then show ?thesis
    unfolding vmtf_imp_def S
    by fast
qed

definition vmtf_flush :: \<open>vmtf_imp_remove \<Rightarrow> vmtf_imp_remove nres\<close> where
\<open>vmtf_flush \<equiv> (\<lambda>((A, m, lst, next_search), removed). do {
    removed' \<leftarrow> SPEC (\<lambda>removed'. mset removed' = mset removed);
    (_, (A, m, lst, next_search)) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, (A, m, lst, next_search)). i < length removed)
      (\<lambda>(i, (A, m, lst, next_search)). do {
         ASSERT(i < length removed);
         RETURN (i+1, vmtf_en_dequeue (removed!i) (A, m, lst, next_search))})
      (0, (A, m, lst, next_search));
    RETURN ((A, m, lst, next_search), [])
  })\<close>

lemma vmtf_imp_swap_removed:
  assumes
    vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close> and
    mset: \<open>mset removed = mset removed'\<close>
  shows \<open>((A, m, lst, next_search), removed') \<in> vmtf_imp M\<close>
  using assms unfolding vmtf_imp_def by (fastforce dest: mset_eq_setD)

lemma vmtf_imp_change_removed_order:
  assumes
    vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close> and
    mset: \<open>mset removed = mset removed'\<close>
  shows \<open>vmtf_flush ((A, m, lst, next_search), removed') \<le> \<Down> Id (RES (vmtf_imp M))\<close>
proof -
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close>
    using vmtf unfolding vmtf_imp_def by fast
  have \<open>set removed = set removed'\<close>
    using mset by (metis set_mset_mset)
  note H =  WHILET_rule[where R = \<open>measure (\<lambda>(i, (A, m, lst, next_search)). Suc (length removed') - i)\<close> and
      I = \<open>\<lambda>(i, (A, m, lst, next_search)). i \<le> length removed' \<and>
            ((A, m, lst, next_search), drop i removed') \<in> vmtf_imp M\<close>]
  have H': \<open>((A', m', lst', next_search'), drop j removed') \<in> vmtf_imp M\<close>
    if
      s: \<open>case s of (i, A, m, lst, next_search) \<Rightarrow> i \<le> length removed' \<and>
            ((A, m, lst, next_search), drop i removed') \<in> vmtf_imp M\<close> and
      i: \<open>case s of (i, A, m, lst, next_search) \<Rightarrow> i < length removed'\<close> and
      \<open>s = (i, b)\<close> and
      \<open>b = (A, ba)\<close> and
      \<open>ba = (m, bb)\<close> and
      \<open>bb = (lst, next_search)\<close> and
      i_le_rem: \<open>i < length removed'\<close> and
      \<open>x2b = (lst', next_search')\<close> and
      \<open>x2a = (m', x2b)\<close> and
      \<open>x2 = (A', x2a)\<close> and
      \<open>(i + 1, vmtf_en_dequeue (removed' ! i) (A, m, lst, next_search)) = (j, x2)\<close>
    for s i b A ba m bb lst next_search  j x2 A' x2a m' x2b lst' next_search'
  proof -
    have l_vmtf: \<open>((A, m, lst, next_search), drop i removed') \<in> vmtf_imp M\<close>
      using s that by auto
    have \<open>removed' ! i \<in> set removed'\<close>
      using i_le_rem by auto
    then have L: \<open>removed' ! i \<in> atms_of N\<^sub>1\<close>
      using vmtf mset \<open>set removed = set removed'\<close> unfolding vmtf_imp_def abs_l_vmtf_remove_inv_def
      by auto
    have mset: \<open>mset (drop (Suc i) removed') \<subseteq># remove1_mset (removed' ! i) (mset (drop i removed'))\<close>
      by (cases \<open>drop i removed'\<close>) (auto simp: drop_eq_ConsD nth_via_drop)
    have \<open>(vmtf_en_dequeue (removed' ! i) (A, m, lst, next_search), drop (Suc i) removed') \<in> vmtf_imp M\<close>
      using abs_l_vmtf_bump_vmtf_en_dequeue[OF l_vmtf L mset] .
    then show ?thesis
      using that by auto
  qed
  have H: \<open>do {
      WHILE\<^sub>T
        (\<lambda>(i, (A, m, lst, next_search)). i < length removed')
        (\<lambda>(i, (A, m, lst, next_search)). do {
          ASSERT(i < length removed');
          RETURN (i+1, vmtf_en_dequeue (removed'!i) (A, m, lst, next_search))})
        (0, (A, m, lst, next_search))
    } \<le> (RES ({(length removed', a)|a. (a, []) \<in> vmtf_imp M}))\<close>
    unfolding vmtf_flush_def
    apply (refine_vcg H)
    subgoal by auto
    subgoal using vmtf by auto
    subgoal using vmtf mset  by (auto intro: vmtf_imp_swap_removed)
    subgoal by simp
    subgoal by auto
    subgoal by (rule H'; assumption)
    subgoal by auto
    subgoal by auto
    done
  have RES: \<open>RES (vmtf_imp M) = do {
        removed' \<leftarrow> SPEC (\<lambda>removed'. mset removed' = mset removed');
        a \<leftarrow> RES (vmtf_imp M);
        RETURN a}\<close>
    by auto
  have K: \<open>SPEC (\<lambda>uu. \<exists>a. uu = (length removed', a) \<and> (a, []) \<in> vmtf_imp M) \<le>
      \<Down> {(a', a). snd a' = fst a \<and> fst a'= length removed' \<and> snd a = []} (RES (vmtf_imp M))\<close>
    by (force intro!: RES_refine)
  show ?thesis
    unfolding vmtf_flush_def
    apply (subst RES)
    apply clarify
    apply (refine_rcg H[THEN order_trans] K)
    subgoal by auto
    subgoal for r r' a a' x1 x2 x1a x2a x1b x2b x1c x2c
      by (cases a') auto
    done
qed

lemma wf_vmtf_get_next:
  assumes vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close>
  shows \<open>wf {(get_next (A ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of N\<^sub>1}\<close> (is \<open>wf ?R\<close>)
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain f where
    f: \<open>(f (Suc i), f i) \<in> ?R\<close> for i
    unfolding wf_iff_no_infinite_down_chain by blast

  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close>
    using vmtf unfolding vmtf_imp_def by fast
  let ?f0 = \<open>the (f 0)\<close>
  have f_None: \<open>f i \<noteq> None\<close> for i
    using f[of i] by fast
  have f_Suc : \<open>f (Suc n) = get_next (A ! the (f n))\<close> for n
    using f[of n] by auto
  have f0_length: \<open>?f0 < length A\<close>
    using f[of 0] atm_A
    by auto
  have \<open>?f0 \<in> set (ys' @ xs')\<close>
    apply (rule ccontr)
    using notin f_Suc[of 0] f0_length unfolding l_vmtf_notin_def
    by (auto simp: f_None)
  then obtain i0 where
    i0: \<open>(ys' @ xs') ! i0 = ?f0\<close> \<open>i0 < length (ys' @ xs')\<close>
    by (meson in_set_conv_nth)
  define zs where \<open>zs = ys' @ xs'\<close>
  have H: \<open>ys' @ xs' = take m (ys' @ xs') @ [(ys' @ xs') ! m, (ys' @ xs') ! (m+1)] @
     drop (m+2) (ys' @ xs')\<close>
    if \<open>m+1 < length (ys' @ xs')\<close>
    for m
    using that
    unfolding zs_def[symmetric]
    apply -
    apply (subst id_take_nth_drop[of m])
    by (auto simp: Cons_nth_drop_Suc simp del: append_take_drop_id)

  have \<open>the (f n) = (ys' @ xs') ! (i0 + n) \<and> i0 + n < length (ys' @ xs')\<close> for n
  proof (induction n)
    case 0
    then show ?case using i0 by simp
  next
    case (Suc n')
    have i0_le:  \<open>i0 + n' + 1 < length (ys' @ xs')\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>i0 + n' + 1 = length (ys' @ xs')\<close>
        using Suc by auto
      then have \<open>ys' @ xs' = butlast (ys' @ xs') @ [the (f n')]\<close>
        using Suc by (metis add_diff_cancel_right' append_butlast_last_id length_0_conv
            length_butlast less_one not_add_less2 nth_append_length)
      then show False
        using l_vmtf_last_next[of \<open>butlast (ys' @ xs')\<close> \<open>the (f n')\<close> m A] l_vmtf
         f_Suc[of n'] by (auto simp: f_None)
    qed
    have get_next: \<open>get_next (A ! ((ys' @ xs') ! (i0 + n'))) = Some ((ys' @ xs') ! (i0 + n' + 1))\<close>
      apply(rule l_vmtf_last_mid_get_next[of \<open>take (i0 + n') (ys' @ xs')\<close>
        \<open>(ys' @ xs') ! (i0 + n')\<close>
        \<open>(ys' @ xs') ! ((i0 + n') + 1)\<close>
        \<open>drop ((i0 + n') + 2) (ys' @ xs')\<close>
        m A])
      apply (subst H[symmetric])
      subgoal using i0_le .
      subgoal using l_vmtf by simp
      done
    then show ?case
      using f_Suc[of n'] Suc i0_le by auto
  qed
  then show False
    by blast
qed

lemma wf_vmtf_next_search_take_next:
  assumes
    vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close> and
    n: \<open>next_search \<noteq> None\<close> and
    def_n: \<open>defined_lit M (Pos (the next_search))\<close>
  shows \<open>((A, m, lst, get_next (A!the next_search)), removed) \<in> vmtf_imp M\<close>
  unfolding vmtf_imp_def
proof clarify
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    ys'_xs'_N\<^sub>1: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  let ?xs' = \<open>tl xs'\<close>
  let ?ys' = \<open>ys' @ [hd xs']\<close>
  have [simp]: \<open>xs' \<noteq> []\<close>
    using next_search n by auto
  have \<open>l_vmtf (?ys' @ ?xs') m A\<close>
    using l_vmtf by (cases xs') auto
  moreover have \<open>lst = option_hd (?ys' @ ?xs')\<close>
    using lst by auto
  moreover have \<open>get_next (A ! the next_search) = option_hd ?xs'\<close>
    using next_search n l_vmtf
    by (cases xs') (auto dest: l_vmtf_last_mid_get_next_option_hd)
  moreover {
    have [dest]: \<open>defined_lit M (Pos a) \<Longrightarrow> a \<in> atm_of ` lits_of_l M\<close> for a
      by (auto simp: defined_lit_map lits_of_def)
    have \<open>abs_l_vmtf_remove_inv M ((set ?xs', set ?ys'), set removed)\<close>
      using abs_vmtf def_n next_search n l_vmtf_distinct[OF l_vmtf]
      unfolding abs_l_vmtf_remove_inv_def
      by (cases xs') auto }
  moreover have \<open>l_vmtf_notin (?ys' @ ?xs') m A\<close>
    using notin by auto
  moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of N\<^sub>1\<close>
    using ys'_xs'_N\<^sub>1 by auto
  ultimately show \<open>\<exists>xs' ys'. l_vmtf (ys' @ xs') m A \<and>
          lst = option_hd (ys' @ xs') \<and>
          get_next (A ! the next_search) = option_hd xs' \<and>
          abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed) \<and>
          l_vmtf_notin (ys' @ xs') m A \<and>
          (\<forall>L\<in>atms_of N\<^sub>1. L < length A) \<and>
          (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
    using atm_A by blast
qed


definition vmtf_find_next_undef :: \<open>vmtf_imp_remove \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat option) nres\<close> where
\<open>vmtf_find_next_undef \<equiv> (\<lambda>((A, m, lst, next_search), removed) M. do {
    WHILE\<^sub>T\<^bsup>\<lambda>next_search. ((A, m, lst, next_search), removed) \<in> vmtf_imp M \<and>
         (next_search \<noteq> None \<longrightarrow> Pos (the next_search) \<in> snd ` D\<^sub>0)\<^esup>
      (\<lambda>next_search. next_search \<noteq> None \<and> defined_lit M (Pos (the next_search)))
      (\<lambda>next_search. do {
         ASSERT(next_search \<noteq> None);
         let n = the next_search;
         ASSERT(Pos n \<in> snd ` D\<^sub>0);
         ASSERT (n < length A);
         if undefined_lit M (Pos n)
         then RETURN (Some n)
         else RETURN (get_next (A!n))
        }
      )
      next_search
  })\<close>

lemma vmtf_find_next_undef_ref:
  assumes
    vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close>
  shows \<open>vmtf_find_next_undef ((A, m, lst, next_search), removed) M
     \<le> \<Down> Id (SPEC (\<lambda>L. ((A, m, lst, L), removed) \<in> vmtf_imp M \<and>
        (L = None \<longrightarrow> (\<forall>L\<in>#N\<^sub>1. defined_lit M L)) \<and>
        (L \<noteq> None \<longrightarrow> Pos (the L) \<in> snd ` D\<^sub>0 \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close>
    using vmtf unfolding vmtf_imp_def by fast
  have [simp]: \<open>index xs' (hd xs') = 0\<close> if \<open>xs' \<noteq> []\<close> for xs' :: \<open>'a list\<close>
    using that by (cases xs') auto
  have no_next_search_all_defined:
    \<open>((A', m', lst', None), remove) \<in> vmtf_imp M \<Longrightarrow>  x \<in># N\<^sub>1 \<Longrightarrow> defined_lit M x\<close>
    for x A' m' lst' remove
    by (auto simp: vmtf_imp_def abs_l_vmtf_remove_inv_def in_N\<^sub>1_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  have next_search_N\<^sub>1:
    \<open>((A', m', lst', Some y), remove) \<in> vmtf_imp M \<Longrightarrow> y \<in> atms_of N\<^sub>1\<close>
    for A' m' lst' remove y
    by (auto simp: vmtf_imp_def abs_l_vmtf_remove_inv_def in_N\<^sub>1_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  have next_search_le_A':
    \<open>((A', m', lst', Some y), remove) \<in> vmtf_imp M \<Longrightarrow> y < length A'\<close>
    for A' m' lst' remove y
    by (auto simp: vmtf_imp_def abs_l_vmtf_remove_inv_def in_N\<^sub>1_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  show ?thesis
    unfolding vmtf_find_next_undef_def
    apply (refine_vcg
       WHILEIT_rule[where R=\<open>{(get_next (A ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of N\<^sub>1}\<close>])
    subgoal using vmtf by (rule wf_vmtf_get_next)
    subgoal using next_search vmtf by auto
    subgoal using vmtf by (auto dest!: next_search_N\<^sub>1 simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff)
    subgoal using vmtf by auto
    subgoal using vmtf by auto
    subgoal using vmtf by (auto dest: next_search_le_A')
    subgoal by (auto dest!: next_search_N\<^sub>1 simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff)
    subgoal by (auto dest: next_search_le_A')
    subgoal for x1 A' x2 m' x2a lst' next_search' x2c s
      by (auto dest: no_next_search_all_defined next_search_N\<^sub>1)
    subgoal by (auto dest: wf_vmtf_next_search_take_next)
    subgoal by (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff)
        (metis next_search_N\<^sub>1 option.distinct(1) option.sel wf_vmtf_next_search_take_next)
    subgoal by (auto dest: next_search_N\<^sub>1 no_next_search_all_defined wf_vmtf_next_search_take_next)
    subgoal by (auto dest: no_next_search_all_defined next_search_N\<^sub>1)
    subgoal by (auto dest: no_next_search_all_defined)
    subgoal by auto
    subgoal by auto
    done
qed

definition vmtf_dump :: \<open>nat \<Rightarrow> vmtf_imp_remove \<Rightarrow> vmtf_imp_remove\<close> where
\<open>vmtf_dump L = (\<lambda>((A, m, lst, next_search), removed). ((A, m, lst, next_search), L # removed))\<close>

lemma vmtf_dump:
  assumes L: \<open>L \<in>atms_of N\<^sub>1\<close> and vmtf: \<open>((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close>
  shows \<open>vmtf_dump L ((A, m, lst, next_search), removed) \<in> vmtf_imp M\<close>
proof -
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set removed)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  moreover have \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set (L # removed))\<close>
    using abs_vmtf L unfolding abs_l_vmtf_remove_inv_def
    by auto
  ultimately show ?thesis
    unfolding vmtf_imp_def vmtf_dump_def by fast
qed

lemma abs_l_vmtf_unset_vmtf_unset':
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>((A, m, lst, next_search), remove) \<in> vmtf_imp M\<close> and
    L_N: \<open>L \<in> atms_of N\<^sub>1\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>(vmtf_unset L ((A, m, lst, next_search), remove)) \<in> vmtf_imp (tl M)\<close>
     (is \<open>?S \<in> _\<close>)
proof -
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    ys'_xs'_N\<^sub>1: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  obtain A' m' lst' next_search' remove'' where
    S: \<open>?S = ((A', m', lst', next_search'), remove'')\<close>
    by (cases ?S) auto
  have L_ys'_iff: \<open>L \<in> set ys' \<longleftrightarrow> (next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L))\<close>
    using vmtf_imp_atm_of_ys_iff[OF l_vmtf next_search abs_vmtf L_N] .
  have dist: \<open>distinct (ys' @ xs')\<close>
    using l_vmtf_distinct[OF l_vmtf] .
  have \<open>L \<in> set (xs' @ ys')\<close>
    using abs_vmtf L_N unfolding abs_l_vmtf_remove_inv_def by auto
  then have L_ys'_xs': \<open>L \<in> set ys' \<longleftrightarrow> L \<notin> set xs'\<close>
    using dist by auto
  have [simp]: \<open>remove'' = remove\<close>
    using S unfolding vmtf_unset_def by (auto split: if_splits)
  have \<open>\<exists>xs' ys'.
       l_vmtf (ys' @ xs') m' A' \<and>
       lst' = option_hd (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       abs_l_vmtf_remove_inv (tl M) ((set xs', set ys'), set remove'') \<and>
       l_vmtf_notin (ys' @ xs') m' A' \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length A') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
  proof (cases \<open>L \<in> set xs'\<close>)
    case True
    then have C[unfolded L_def]: \<open>\<not>(next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L))\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have abs_vmtf: \<open>abs_l_vmtf_remove_inv (tl M) ((set xs', set ys'), set remove)\<close>
      using S abs_vmtf dist L_ys'_xs' True unfolding abs_l_vmtf_remove_inv_def vmtf_unset_def
      by (cases M) (auto simp: C)
    show ?thesis
      using S True unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      apply -
      apply (simp add: C)
      using l_vmtf lst next_search abs_vmtf notin atm_A ys'_xs'_N\<^sub>1
      by auto
  next
    case False
    then have C[unfolded L_def]: \<open>next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L)\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have L_ys: \<open>L \<in> set ys'\<close>
      by (use False L_ys'_xs' in auto)
    define y_ys where \<open>y_ys \<equiv> takeWhile (op \<noteq> L) ys'\<close>
    define x_ys where \<open>x_ys \<equiv> drop (length y_ys) ys'\<close>
    let ?ys' = \<open>y_ys\<close>
    let ?xs' = \<open>x_ys @ xs'\<close>
    have x_ys_take_ys': \<open>y_ys = take (length y_ys) ys'\<close>
        unfolding y_ys_def (* TODO: proof *)
        apply (subst take_length_takeWhile_eq_takeWhile[of \<open>op \<noteq> L\<close> \<open>ys'\<close>, symmetric])
        by (smt L_ys hd_drop_conv_nth le_neq_implies_less length_append_singleton
          length_takeWhile_le nth_length_takeWhile set_takeWhileD take_all take_hd_drop
          take_length_takeWhile_eq_takeWhile)
    have ys'_y_x: \<open>ys' = y_ys @ x_ys\<close>
      by (subst x_ys_take_ys') (auto simp: x_ys_def)
    have y_ys_le_ys': \<open>length y_ys < length ys'\<close>
      using L_ys by (metis (full_types) append_eq_conv_conj append_self_conv le_antisym
        length_takeWhile_le not_less takeWhile_eq_all_conv x_ys_take_ys' y_ys_def)
    from nth_length_takeWhile[OF this[unfolded y_ys_def]] have [simp]: \<open>x_ys \<noteq> []\<close> \<open>hd x_ys = L\<close>
      using y_ys_le_ys' unfolding x_ys_def y_ys_def
      by (auto simp: x_ys_def y_ys_def hd_drop_conv_nth)
    have [simp]: \<open>A' = A\<close> \<open>m' = m\<close> \<open>lst' = lst\<close> \<open>next_search' = Some (atm_of (lit_of (hd M)))\<close>
      using S unfolding vmtf_unset_def by (auto simp: C)
    have L_y_ys: \<open>L \<notin> set y_ys\<close>
       unfolding y_ys_def  by (metis (full_types) takeWhile_eq_all_conv takeWhile_idem)
    have \<open>l_vmtf (?ys' @ ?xs') m A\<close>
      using l_vmtf unfolding ys'_y_x by simp
    moreover have \<open>lst' = option_hd (?ys' @ ?xs')\<close>
      using lst unfolding ys'_y_x by simp
    moreover have \<open>next_search' = option_hd ?xs'\<close>
      by auto
    moreover {
      have \<open>abs_l_vmtf_remove_inv M ((set ?xs', set ?ys'), set remove)\<close>
        using abs_vmtf dist unfolding abs_l_vmtf_remove_inv_def ys'_y_x
        by auto
      then have \<open>abs_l_vmtf_remove_inv (tl M) ((set ?xs', set ?ys'), set remove)\<close>
        using dist L_y_ys unfolding abs_l_vmtf_remove_inv_def ys'_y_x ys'_y_x
        by (cases M) auto
      }
    moreover have \<open>l_vmtf_notin (?ys' @ ?xs') m A\<close>
      using notin unfolding ys'_y_x by simp
    moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of N\<^sub>1\<close>
      using ys'_xs'_N\<^sub>1  unfolding ys'_y_x by simp
    ultimately show ?thesis
      using S False atm_A unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      by (fastforce simp add: C)
  qed
  then show ?thesis
    unfolding vmtf_imp_def S
    by fast
qed

definition (in twl_array_code_ops) vmtf_dump_and_unset  :: \<open>nat \<Rightarrow> vmtf_imp_remove \<Rightarrow> vmtf_imp_remove\<close> where
  \<open>vmtf_dump_and_unset L M = vmtf_dump L (vmtf_unset L M)\<close>

lemma vmtf_imp_cons_remove_iff:
  \<open>((A, m, lst, next_search), L # b) \<in> vmtf_imp M \<longleftrightarrow> 
     L \<in> atms_of N\<^sub>1 \<and> ((A, m, lst, next_search), b) \<in> vmtf_imp M\<close>
  (is \<open>?A \<longleftrightarrow> ?L \<and> ?B\<close>)
proof
  assume vmtf: ?A
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set (L # b))\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  moreover have \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set b)\<close> and L: ?L
    using abs_vmtf unfolding abs_l_vmtf_remove_inv_def by auto
  ultimately have \<open>l_vmtf (ys' @ xs') m A \<and>
       lst = option_hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       abs_l_vmtf_remove_inv M ((set xs', set ys'), set b) \<and>
       l_vmtf_notin (ys' @ xs') m A \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length A) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
      by fast
  then show \<open>?L \<and> ?B\<close>
    using L unfolding vmtf_imp_def by fast
next
  assume vmtf: \<open>?L \<and> ?B\<close>
  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set b)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def by fast
  moreover have \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set (L # b))\<close>
    using vmtf abs_vmtf unfolding abs_l_vmtf_remove_inv_def by auto
  ultimately have \<open>l_vmtf (ys' @ xs') m A \<and>
       lst = option_hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       abs_l_vmtf_remove_inv M ((set xs', set ys'), set (L # b)) \<and>
       l_vmtf_notin (ys' @ xs') m A \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length A) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1)\<close>
      by fast
  then show \<open>?A\<close>
    unfolding vmtf_imp_def by fast
qed

lemma abs_l_vmtf_unset_vmtf_dump_unset:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>((A, m, lst, next_search), remove) \<in> vmtf_imp M\<close> and
    L_N: \<open>L \<in> atms_of N\<^sub>1\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>(vmtf_dump_and_unset L ((A, m, lst, next_search), remove)) \<in> vmtf_imp (tl M)\<close>
     (is \<open>?S \<in> _\<close>)
  using abs_l_vmtf_unset_vmtf_unset'[OF assms(2-)[unfolded assms(1)]] L_N
  unfolding vmtf_dump_and_unset_def vmtf_dump_def
  by (cases \<open>vmtf_unset (atm_of (lit_of (hd M))) ((A, m, lst, next_search), remove)\<close>)
     (auto simp: vmtf_imp_cons_remove_iff)

end


lemma l_vmtf_Cons:
  assumes
    vmtf: \<open>l_vmtf (b # l) m xs\<close> and
    a_xs: \<open>a < length xs\<close> and
    ab: \<open>a \<noteq> b\<close> and
    a_l: \<open>a \<notin> set l\<close> and
    nm: \<open>n > m\<close> and
    xs': \<open>xs' = xs[a := l_vmtf_ATM n None (Some b),
         b := l_vmtf_ATM (stamp (xs!b)) (Some a) (get_next (xs!b))]\<close> and
    nn': \<open>n' \<ge> n\<close>
  shows \<open>l_vmtf (a # b # l) n' xs'\<close>
proof -
  have \<open>l_vmtf (b # l) m (xs[a := l_vmtf_ATM n None (Some b)])\<close>
    apply (rule l_vmtf_eq_iffI[OF _ _ vmtf])
    subgoal using ab a_l a_xs by auto
    subgoal using a_xs l_vmtf_le_length[OF vmtf] by auto
    done
  then show ?thesis
    apply (rule l_vmtf.Cons[of _ _ _ _ _ n])
    subgoal using a_xs by simp
    subgoal using a_xs by simp
    subgoal using ab .
    subgoal using a_l .
    subgoal using nm .
    subgoal using xs' ab a_xs by (cases \<open>xs ! b\<close>) auto
    subgoal using nn' .
    done
qed

definition (in -) vmtf_cons where
\<open>vmtf_cons A L cnext st =
  (let
    A = A[L := l_vmtf_ATM (Suc st) None cnext];
    A = (case cnext of None \<Rightarrow> A
        | Some cnext \<Rightarrow> A[cnext := l_vmtf_ATM (stamp (A!cnext)) (Some L) (get_next (A!cnext))]) in
  A)
\<close>

lemma vmtf_notin_vmtf_cons:
  assumes
    l_vmtf: \<open>l_vmtf_notin xs m A\<close> and
    cnext: \<open>cnext = option_hd xs\<close> and
    L_xs: \<open>L \<notin> set xs\<close>
  shows
    \<open>l_vmtf_notin (L # xs) (Suc m) (vmtf_cons A L cnext m)\<close>
proof (cases xs)
  case Nil
  then show ?thesis
    using assms by (auto simp: l_vmtf_notin_def vmtf_cons_def elim: l_vmtfE)
next
  case (Cons L' xs') note xs = this
  show ?thesis
    using assms unfolding xs l_vmtf_notin_def xs vmtf_cons_def by auto
qed

lemma vmtf_cons:
  assumes
    l_vmtf: \<open>l_vmtf xs m A\<close> and
    cnext: \<open>cnext = option_hd xs\<close> and
    L_A: \<open>L < length A\<close> and
    L_xs: \<open>L \<notin> set xs\<close>
  shows
    \<open>l_vmtf (L # xs) (Suc m) (vmtf_cons A L cnext m)\<close>
proof (cases xs)
  case Nil
  then show ?thesis
    using assms by (auto simp: l_vmtf_single_iff vmtf_cons_def elim: l_vmtfE)
next
  case (Cons L' xs') note xs = this
  show ?thesis
    unfolding xs
    apply (rule l_vmtf_Cons[OF l_vmtf[unfolded xs], of _ \<open>Suc m\<close>])
    subgoal using L_A .
    subgoal using L_xs unfolding xs by simp
    subgoal using L_xs unfolding xs by simp
    subgoal by simp
    subgoal using cnext L_xs
      by (auto simp: vmtf_cons_def Let_def xs)
    subgoal by linarith
    done
qed

lemma length_vmtf_cons[simp]: \<open>length (vmtf_cons A L n m) = length A\<close>
  by (auto simp: vmtf_cons_def Let_def split: option.splits)


subsection \<open>Phase saving\<close>

type_synonym phase_saver = \<open>bool list\<close>

definition (in twl_array_code_ops) phase_saving :: \<open>phase_saver \<Rightarrow> bool\<close> where
\<open>phase_saving \<phi> \<longleftrightarrow> (\<forall>L\<in>atms_of N\<^sub>1. L < length \<phi>)\<close>

definition get_saved_lit :: \<open>phase_saver \<Rightarrow> nat \<Rightarrow> nat literal\<close> where
\<open>get_saved_lit \<phi> L = (if \<phi>!L then Pos L else Neg L)\<close>

text \<open>Save phase as given (e.g. for literals in the trail):\<close>
definition (in twl_array_code_ops) save_phase :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase L \<phi> = \<phi>[atm_of L := is_pos L]\<close>

text \<open>Save opposite of the phase (e.g. for literals in the conflict clause):\<close>
definition  (in twl_array_code_ops) save_phase_inv :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase_inv L \<phi> = \<phi>[atm_of L := \<not>is_pos L]\<close>
end