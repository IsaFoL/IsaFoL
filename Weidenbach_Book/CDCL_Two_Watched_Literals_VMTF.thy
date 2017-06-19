theory CDCL_Two_Watched_Literals_VMTF
imports Main
begin

type_synonym 'v abs_vmtf = \<open>'v set \<times> 'v set\<close>
type_synonym 'v abs_vmtf_remove = \<open>'v abs_vmtf \<times> 'v set\<close>

subsection \<open>Variable-Move-to-Front\<close>

subsubsection \<open>Specification\<close>

datatype 'v vmtf_atm = VMTF_ATM (stamp : nat) (get_prev: \<open>nat option\<close>) (get_next: \<open>nat option\<close>)

declare nth_list_update[simp]

definition option_hd :: \<open>'a list \<Rightarrow> 'a option\<close> where
  \<open>option_hd xs = (if xs = [] then None else Some (hd xs))\<close>
lemma option_hd_None_iff[iff]: \<open>option_hd ys = None \<longleftrightarrow> ys = []\<close>
  by (auto simp: option_hd_def)
inductive vmtf :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat vmtf_atm list \<Rightarrow> bool\<close> where
Nil: \<open>vmtf [] st xs\<close> |
Cons1: \<open>a < length xs \<Longrightarrow> m \<ge> n \<Longrightarrow> xs ! a = VMTF_ATM (n::nat) None None \<Longrightarrow> vmtf [a] m xs\<close> |
Cons: \<open>vmtf (b # l) m xs \<Longrightarrow> a < length xs \<Longrightarrow> xs ! a = VMTF_ATM n None (Some b) \<Longrightarrow>
  a \<noteq> b \<Longrightarrow> a \<notin> set l \<Longrightarrow> n > m \<Longrightarrow> xs' = xs[b := VMTF_ATM (stamp (xs!b)) (Some a) (get_next (xs!b))] \<Longrightarrow>
    n' \<ge> n \<Longrightarrow>
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

lemma vmtf_single_iff: \<open>vmtf [a] m xs \<longleftrightarrow> (a < length xs \<and> m \<ge> stamp (xs ! a) \<and> xs ! a = VMTF_ATM (stamp (xs ! a)) None None)\<close>
  by (auto 5 5 elim!: vmtfE intro: vmtf.intros)

lemma vmtf_append_decomp:
  assumes \<open>vmtf (axs @ [ax, ay] @ azs) an A\<close>
  shows \<open>(vmtf (axs @ [ax]) an (A[ax:= VMTF_ATM (stamp (A!ax)) (get_prev (A!ax)) None]) \<and>
    vmtf (ay # azs) (stamp (A!ay)) (A[ay:= VMTF_ATM (stamp (A!ay)) None (get_next (A!ay))]) \<and>
    stamp (A!ax) > stamp (A!ay))\<close>
  using assms
proof (induction \<open>axs @ [ax, ay] @ azs\<close> an A arbitrary: axs ax ay azs rule: vmtf.induct)
  case (Nil st xs)
  then show ?case by simp
next
  case (Cons1 a xs m n)
  then show ?case by auto
next
  case (Cons b l m xs a n xs' n') note vmtf = this(1) and IH = this(2) and a_le_y = this(3) and ys_a = this(4) and
    ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and nn' = this(9) and decomp = this(10-)
  have b_le_xs: \<open>b < length xs\<close>
    using vmtf by (auto intro: vmtf_le_length simp: xs')
  show ?case
  proof (cases \<open>axs\<close>)
    case [simp]: Nil
    then have [simp]: \<open>ax = a\<close> \<open>ay = b\<close> \<open>azs = l\<close>
      using decomp by auto
    show ?thesis
    proof (cases l)
      case Nil
      then show ?thesis using vmtf xs' a_le_y ys_a ab a_l mn nn' by (cases \<open>xs ! b\<close>) (auto simp: vmtf_single_iff)
    next
      case (Cons al als) note l = this
      have vmtf_b: \<open>vmtf [b] m (xs[b := VMTF_ATM (stamp (xs ! b)) (get_prev (xs ! b)) None])\<close> and
        vmtf_l: \<open>vmtf (al # als) (stamp (xs ! al)) (xs[al := VMTF_ATM (stamp (xs ! al)) None (get_next (xs ! al))])\<close> and
        stamp_al_b: \<open>stamp (xs ! al) < stamp (xs ! b)\<close>
        using IH[of Nil b al als] unfolding l by auto
      have \<open>vmtf [a] n' (xs'[a := VMTF_ATM (stamp (xs' ! a)) (get_prev (xs' ! a)) None])\<close>
          using a_le_y xs' ab mn nn' ys_a by (auto simp: vmtf_single_iff nth_list_update)
      have al_b[simp]: \<open>al \<noteq> b\<close> and b_als: \<open>b \<notin> set als\<close>
        using vmtf unfolding l by (auto dest: vmtf_distinct)
      have al_le_xs: \<open>al < length xs\<close>
        using vmtf vmtf_l by (auto intro: vmtf_le_length simp: l xs')
      have xs_al: \<open>xs ! al = VMTF_ATM (stamp (xs ! al)) (Some b) (get_next (xs ! al))\<close>
        using vmtf unfolding l by (auto 5 5 elim: vmtfE)
      have xs_b: \<open>xs ! b = VMTF_ATM (stamp (xs ! b)) None (get_next (xs ! b))\<close>
        using vmtf_b vmtf xs' by (cases \<open>xs ! b\<close>) (auto elim: vmtfE simp: l nth_list_update vmtf_single_iff)

      have \<open>vmtf (b # al # als) (stamp (xs' ! b)) (xs'[b := VMTF_ATM (stamp (xs' ! b)) None (get_next (xs' ! b))])\<close>
        apply (rule vmtf.Cons[OF vmtf_l, of _ \<open>stamp (xs' ! b)\<close>])
        subgoal using b_le_xs by auto
        subgoal using xs_b vmtf_b vmtf xs' by (cases \<open>xs ! b\<close>) (auto elim: vmtfE simp: l vmtf_single_iff)
        subgoal using al_b by blast
        subgoal using b_als .
        subgoal using xs' b_le_xs stamp_al_b by (simp add: nth_list_update)
        subgoal using ab unfolding xs' by (simp add: b_le_xs nth_list_update al_le_xs xs_al[symmetric] xs_b[symmetric])
        subgoal by simp
        done
      moreover have \<open>vmtf [a] n' (xs'[a := VMTF_ATM (stamp (xs' ! a)) (get_prev (xs' ! a)) None])\<close>
        using ab a_le_y mn nn' ys_a by (auto simp: vmtf_single_iff xs')
      moreover have \<open>stamp (xs' ! b) < stamp (xs' ! a)\<close>
        using b_le_xs ab mn vmtf_b ys_a by (auto simp add: xs' vmtf_single_iff)
      ultimately show ?thesis
        unfolding l by (simp add: l)
    qed
  next
    case (Cons aaxs axs') note axs = this
    have [simp]: \<open>aaxs = a\<close> and bl: \<open>b # l = axs' @ [ax, ay] @ azs\<close>
      using decomp unfolding axs by simp_all
    have
      vmtf_axs': \<open>vmtf (axs' @ [ax]) m (xs[ax := VMTF_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close> and
      vmtf_ay: \<open>vmtf (ay # azs) (stamp (xs ! ay)) (xs[ay := VMTF_ATM (stamp (xs ! ay)) None (get_next (xs ! ay))])\<close> and
      stamp: \<open>stamp (xs ! ay) < stamp (xs ! ax)\<close>
      using IH[OF bl] by fast+
    have b_ay: \<open>b \<noteq> ay\<close>
      using bl vmtf_distinct[OF vmtf] by (cases axs') auto
    have vmtf_ay': \<open>vmtf (ay # azs) (stamp (xs' ! ay)) (xs[ay := VMTF_ATM (stamp (xs ! ay)) None (get_next (xs ! ay))])\<close>
      using vmtf_ay xs' b_ay by (auto)
    have [simp]: \<open>ay < length xs\<close>
        using vmtf by (auto intro: vmtf_le_length simp: bl xs')
    have in_azs_noteq_b: \<open>i \<in> set azs \<Longrightarrow> i \<noteq> b\<close> for i
      using vmtf_distinct[OF vmtf] bl by (cases axs') (auto simp: xs' b_ay)
    have a_ax[simp]: \<open>a \<noteq> ax\<close>
        using ab a_l bl by (cases axs') (auto simp: xs' b_ay)
    have \<open>vmtf (axs @ [ax]) n' (xs'[ax := VMTF_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
    proof (cases axs')
      case Nil
      then have [simp]: \<open>ax = b\<close>
        using bl by auto
      have \<open>vmtf [ax] m (xs[ax := VMTF_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close>
        using vmtf_axs' unfolding axs Nil by simp
      then have \<open>vmtf (aaxs # ax # []) n' (xs'[ax := VMTF_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
        apply (rule vmtf.Cons[of _ _ _ _ _ n])
        subgoal using a_le_y by auto
        subgoal using ys_a a_le_y ab by auto
        subgoal using ab by auto
        subgoal by simp
        subgoal using mn .
        subgoal using ys_a a_le_y ab xs' b_le_xs  by auto
        subgoal using nn' .
        done
      then show ?thesis
        using vmtf_axs' unfolding axs Nil by simp
    next
      case (Cons aaaxs' axs'')
      have [simp]: \<open>aaaxs' = b\<close>
        using bl unfolding Cons by auto
      have \<open>vmtf (aaaxs' # axs'' @ [ax]) m (xs[ax := VMTF_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close>
        using vmtf_axs' unfolding axs Cons by simp
      then have \<open>vmtf (a # aaaxs' # axs'' @ [ax]) n' (xs'[ax := VMTF_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
        apply (rule vmtf.Cons[of _ _ _ _ _ n])
        subgoal using a_le_y by auto
        subgoal using ys_a a_le_y a_ax ab by (subst nth_list_update_neq) (auto simp: nth_list_update_neq simp del: \<open>a \<noteq> ax\<close>)
        subgoal using ab by auto
        subgoal using a_l bl unfolding Cons by simp
        subgoal using mn .
        subgoal using ys_a a_le_y ab xs' b_le_xs  by (auto simp: list_update_swap nth_list_update)
        subgoal using nn' .
        done
      then show ?thesis
        unfolding axs Cons by simp
    qed
    moreover have \<open>vmtf (ay # azs) (stamp (xs' ! ay))
        (xs'[ay := VMTF_ATM (stamp (xs' ! ay)) None (get_next (xs' ! ay))])\<close>
      apply (rule vmtf_eq_iff[THEN iffD1, OF _ _ vmtf_ay'])
      subgoal using vmtf_distinct[OF vmtf] bl b_le_xs in_azs_noteq_b by (auto simp: xs' b_ay)
      subgoal using vmtf_le_length[OF vmtf] bl unfolding xs' by auto
      done
    moreover have \<open>stamp (xs' ! ay) < stamp (xs' ! ax)\<close>
      using stamp unfolding axs xs' by (auto simp: b_le_xs b_ay)
    ultimately show ?thesis
      unfolding axs xs' by fast
  qed
qed

lemma vmtf_append_rebuild:
  assumes
    \<open>(vmtf (axs @ [ax]) an A) \<close> and
    \<open>vmtf (ay # azs) (stamp (A!ay)) A\<close> and
    \<open>stamp (A!ax) > stamp (A!ay)\<close> and
    \<open>distinct (axs @ [ax, ay] @ azs)\<close>
  shows \<open>vmtf (axs @ [ax, ay] @ azs) an
    (A[ax := VMTF_ATM (stamp (A!ax)) (get_prev (A!ax)) (Some ay) ,
       ay := VMTF_ATM (stamp (A!ay)) (Some ax) (get_next (A!ay))])\<close>
  using assms
proof (induction \<open>axs @ [ax]\<close> an A arbitrary: axs ax ay azs rule: vmtf.induct)
  case (Nil st xs)
  then show ?case by simp
next
  case (Cons1 a xs m n) note a_le_xs = this(1) and nm = this(2) and xs_a = this(3) and a = this(4)
    and vmtf = this(5) and stamp = this(6) and dist = this(7)
  have a_ax: \<open>ax = a\<close>
    using a by simp

  have vmtf_ay': \<open>vmtf (ay # azs) (stamp (xs ! ay)) (xs[ax := VMTF_ATM n None (Some ay)])\<close>
    apply (rule vmtf_eq_iff[THEN iffD1, OF _ _ vmtf])
    subgoal using dist a_ax a_le_xs by (auto simp: nth_list_update)
    subgoal using vmtf vmtf_le_length by auto
    done

  then have \<open>vmtf (ax # ay # azs) m (xs[ax := VMTF_ATM n None (Some ay),
      ay := VMTF_ATM (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    apply (rule vmtf.Cons[of _ _ _ _ _ \<open>stamp (xs ! a)\<close>])
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
  case (Cons b l m xs a n xs' n') note vmtf = this(1) and IH = this(2) and a_le_y = this(3) and
    ys_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10) and vmtf_ay = this(11) and stamp = this(12) and
    dist = this(13)

  have dist_b: \<open>distinct ((a # b # l) @ ay # azs)\<close>
    using dist unfolding decomp by auto
  then have b_ay: \<open>b \<noteq> ay\<close>
    by auto
  have b_le_xs: \<open>b < length xs\<close>
    using vmtf vmtf_le_length by auto
  have a_ax: \<open>a \<noteq> ax\<close> and a_ay: \<open>a \<noteq> ay\<close>
    using dist_b decomp dist by (cases axs; auto)+
  have vmtf_ay': \<open>vmtf (ay # azs) (stamp (xs ! ay)) xs\<close>
    apply (rule vmtf_eq_iff[THEN iffD1, of _ _ xs'])
    subgoal using xs' b_ay dist_b  b_le_xs by (auto simp: nth_list_update)
    subgoal using vmtf_le_length[OF vmtf_ay] xs' by auto
    subgoal using xs' b_ay dist_b  b_le_xs vmtf_ay xs' by (auto simp: nth_list_update)
    done

  have \<open>vmtf (tl axs @ [ax, ay] @ azs) m
          (xs[ax := VMTF_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) (Some ay),
              ay := VMTF_ATM (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    apply (rule IH)
    subgoal using decomp by (cases axs) auto
    subgoal using vmtf_ay' .
    subgoal using stamp xs' b_ay b_le_xs by (cases \<open>ax = b\<close>) auto
    subgoal using dist by (cases axs) auto
    done
  moreover have \<open>tl axs @ [ax, ay] @ azs = b # l @ ay # azs\<close>
    using decomp by (cases axs) auto
  ultimately have vmtf_tl_axs: \<open>vmtf (b # l @ ay # azs) m
          (xs[ax := VMTF_ATM (stamp (xs ! ax)) (get_prev (xs ! ax)) (Some ay),
              ay := VMTF_ATM (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    by metis

  then have \<open>vmtf (a # b # l @ ay # azs) n'
     (xs'[ax := VMTF_ATM (stamp (xs' ! ax)) (get_prev (xs' ! ax)) (Some ay),
          ay := VMTF_ATM (stamp (xs' ! ay)) (Some ax) (get_next (xs' ! ay))])\<close>
    apply (rule vmtf.Cons[of _ _ _ _ _ \<open>stamp (xs ! a)\<close>])
    subgoal using a_le_y by simp
    subgoal using ys_a a_le_y a_ax a_ay by (auto simp: nth_list_update)
    subgoal using ab .
    subgoal using dist_b by auto
    subgoal using mn by (simp add: ys_a)
    subgoal using ys_a a_le_y a_ax a_ay b_ay b_le_xs unfolding xs'
      by (auto simp: list_update_swap)
    subgoal using stamp xs' nn' b_ay b_le_xs ys_a by auto
    done
  then show ?case
    by (metis append.assoc append_Cons append_Nil decomp)
qed

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

lemma vmtf_last_next:
  \<open>vmtf (xs @ [x]) m A \<Longrightarrow> get_next (A ! x) = None\<close>
  apply (induction "xs @ [x]" m A arbitrary: xs x rule: vmtf.induct) (* TODO Proof *)
    apply auto
  by (metis list.distinct(1) list.sel(3) list.set_intros(1) nth_list_update_eq nth_list_update_neq
      self_append_conv2 tl_append2 vmtf_atm.sel(3) vmtf_le_length)

lemma vmtf_last_mid_get_next:
  \<open>vmtf (xs @ [x, y] @ ys) m A \<Longrightarrow> get_next (A ! x) = Some y\<close>
  apply (induction "xs @ [x, y] @ ys" m A arbitrary: xs x rule: vmtf.induct) (* TODO Proof *)
    apply auto
  by (metis list.sel(1) list.sel(3) list.set_intros(1) nth_list_update_eq nth_list_update_neq
      self_append_conv2 tl_append2 vmtf_atm.sel(3) vmtf_le_length)

lemma vmtf_last_mid_get_prev:
  assumes \<open>vmtf (xs @ [x, y] @ ys) m A\<close>
  shows \<open>get_prev (A ! y) = Some x\<close>
    using assms
proof (induction "xs @ [x, y] @ ys" m A arbitrary: xs x rule: vmtf.induct)
  case (Nil st xs)
  then show ?case by auto
next
  case (Cons1 a xs m n)
  then show ?case by auto
next
  case (Cons b l m xxs a n xxs' n') note vmtf = this(1) and IH = this(2) and a_le_y = this(3) and
    ys_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Cons vmtf_le_length by auto
  next
    case (Cons aaxs axs')
    then have b_l: \<open>b # l = tl xs @ [x, y] @ ys\<close>
      using decomp by auto
    then have \<open>get_prev (xxs ! y) = Some x\<close>
      by (rule IH)
    moreover have \<open>x \<noteq> y\<close>
      using vmtf_distinct[OF vmtf] b_l by auto
    moreover have \<open>b \<noteq> y\<close>
      using vmtf_distinct[OF vmtf] decomp by (cases axs') (auto simp add: Cons)
    moreover have \<open>y < length xxs\<close> \<open>b < length xxs\<close>
      using vmtf_le_length[OF vmtf, unfolded b_l] vmtf_le_length[OF vmtf] by auto
    ultimately show ?thesis
      unfolding xs' by auto
  qed
qed

lemma length_vmtf_dequeue[simp]: \<open>length (vmtf_dequeue A x) = length A\<close>
  unfolding vmtf_dequeue_def by (auto simp: Let_def split: option.splits)

lemma vmtf_skip_fst:
  assumes vmtf: \<open>vmtf (x # y' # ys') m A\<close>
  shows \<open>\<exists>n. vmtf (y' # ys') n (A[y' := VMTF_ATM (stamp (A ! y')) None (get_next (A ! y'))]) \<and>
     m \<ge> n\<close>
  using assms
proof (rule vmtfE, goal_cases)
  case 1
  then show ?case by simp
next
  case (2 a n)
  then show ?case by simp
next
  case (3 b l m xs a n)
  moreover have \<open>get_prev (xs ! b) = None\<close>
    using 3(3) by (fastforce elim: vmtfE)
  moreover have \<open>b < length xs\<close>
    using 3(3) vmtf_le_length by auto
  ultimately show ?case
    by (cases \<open>xs ! b\<close>) (auto simp: eq_commute[of \<open>xs ! b\<close>])
qed

abbreviation none_or_notin_list where
\<open>none_or_notin_list m l \<equiv> m = None \<or> the m \<notin> set l\<close>

definition vmtf_notin where
  \<open>vmtf_notin l m xs \<longleftrightarrow> (\<forall>i<length xs. i\<notin>set l \<longrightarrow> (none_or_notin_list (get_prev (xs ! i)) l \<and>
      none_or_notin_list (get_next (xs ! i)) l))\<close>

lemma stamp_vmtf_dequeue:
  \<open>axs < length zs \<Longrightarrow> stamp (vmtf_dequeue zs x ! axs) = stamp (zs ! axs)\<close>
  by (cases \<open>zs ! (the (get_next (zs ! x)))\<close>; cases \<open>(the (get_next (zs ! x))) = axs\<close>;
      cases \<open>(the (get_prev (zs ! x))) = axs\<close>)
    (auto simp: vmtf_dequeue_def Let_def nth_list_update split: option.splits)

lemma sorted_many_eq_append: \<open>sorted (xs @ [x, y]) \<longleftrightarrow> sorted (xs @ [x]) \<and> x \<le> y\<close>
  using sorted_append[of \<open>xs @ [x]\<close> \<open>[y]\<close>] sorted_append[of xs \<open>[x]\<close>]
  by force

lemma vmtf_stamp_sorted:
  assumes \<open>vmtf l m A\<close>
  shows \<open>sorted (map (\<lambda>a. stamp (A!a)) (rev l)) \<and> (\<forall>a \<in> set l. stamp (A!a) \<le> m)\<close>
  using assms
proof (induction rule: vmtf.induct)
  case (Cons b l m xs a n xs' n') note vmtf = this(1) and IH = this(9) and a_le_y = this(2) and
    ys_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8)
  have H:
   \<open>map (\<lambda>aa. stamp (xs[b := VMTF_ATM (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! aa)) (rev l) =
     map (\<lambda>a. stamp (xs ! a)) (rev l)\<close>
    apply (rule map_cong)
    subgoal by auto
    subgoal using vmtf_distinct[OF vmtf] vmtf_le_length[OF vmtf] by auto
    done
  have [simp]: \<open>stamp (xs[b := VMTF_ATM (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! b) = stamp (xs ! b)\<close>
    using vmtf_distinct[OF vmtf] vmtf_le_length[OF vmtf] by (cases \<open>xs ! b\<close>) auto
  have \<open>stamp (xs[b := VMTF_ATM (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! aa) \<le> n'\<close>
    if \<open>aa \<in> set l\<close> for aa
    apply (cases \<open>aa = b\<close>)
    subgoal using Cons by auto
    subgoal using vmtf_distinct[OF vmtf] vmtf_le_length[OF vmtf] IH nn' mn that by auto
    done
  then show ?case
    using Cons by (auto simp: H sorted_many_eq_append)
qed auto


text \<open>
  This a version of @{thm nth_list_update} with a different condition (\<^term>\<open>j\<close>
  instead of \<^term>\<open>i\<close>). This is more useful here.
  \<close>
(* TODO: Move*)
lemma nth_list_update'[simp]:
"j < length xs \<Longrightarrow> (xs[i:=x])!j = (if i = j then x else xs!j)"
  by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)

lemma vmtf_vmtf_dequeue:
  assumes vmtf: \<open>vmtf l m A\<close> and notin: \<open>vmtf_notin l m A\<close> and valid: \<open>x < length A\<close>
  shows \<open>vmtf (remove1 x l) m (vmtf_dequeue A x)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: ‹a ∈ set l ⟹ x ∉ set l \<Longrightarrow> a \<noteq> x› ‹a ∈ set l ⟹ x ∉ set l \<Longrightarrow> x \<noteq> a›  for a x
    by auto
  have
      \<open>none_or_notin_list (get_prev (A ! x)) l\<close> and
      \<open>none_or_notin_list (get_next (A ! x)) l\<close>
    using notin False valid unfolding vmtf_notin_def by auto
  then have vmtf_eq: \<open>(vmtf_dequeue A x) ! a = A ! a\<close> if \<open>a \<in> set l\<close> for a
    using that False valid unfolding vmtf_notin_def vmtf_dequeue_def
    by (cases \<open>A ! (the (get_prev (A ! x)))\<close>; cases \<open>A ! (the (get_next (A ! x)))\<close>)
      (auto simp: Let_def split: option.splits)
  show ?thesis
    unfolding H
    apply (rule vmtf_eq_iff[THEN iffD1, OF _ _ vmtf])
    subgoal using vmtf_eq by blast
    subgoal using vmtf_le_length[OF vmtf] by auto
    done
next
  case True
  then obtain xs ys where
    l: \<open>l = xs @ x # ys\<close>
    by (meson split_list)
  have r_l: \<open>remove1 x l = xs @ ys\<close>
    using vmtf_distinct[OF vmtf] unfolding l by (simp add: remove1_append)

  consider
    (xs_ys_empty) \<open>xs = []\<close> and \<open>ys = []\<close> |
    (xs_nempty_ys_empty) x' xs' where \<open>xs = xs' @ [x']\<close> and \<open>ys = []\<close> |
    (xs_empty_ys_nempty) y' ys' where \<open>xs = []\<close> and \<open>ys = y' # ys'\<close> |
    (xs_ys_nempty) x' y' xs' ys' where  \<open>xs = xs' @ [x']\<close> and \<open>ys = y' # ys'\<close>
    by (cases xs rule: rev_cases; cases ys)
  then show ?thesis
  proof cases
    case xs_ys_empty
    then show ?thesis
      using vmtf by (auto simp: r_l intro: vmtf.intros)
  next
    case xs_empty_ys_nempty note xs = this(1) and ys = this(1)
    have prev_next: \<open>get_prev (A ! x) = None\<close> \<open>get_next (A ! x) = option_hd ys\<close>
      using vmtf unfolding l xs ys
      by (cases ys; auto 5 5 simp: option_hd_def elim: vmtfE)+

    then show ?thesis
      using vmtf unfolding r_l unfolding l xs ys -- \<open>TODO proof\<close>
      apply (auto simp: vmtf_dequeue_def Let_def split: option.splits
          intro: vmtf.intros)
      by (smt list.sel(1) list.simps(3) option.inject option_hd_def vmtf_skip_fst
          vmtf_stamp_increase xs_empty_ys_nempty(2))
  next
    case xs_nempty_ys_empty note xs = this(1) and ys = this(2)
    have prev_next: \<open>get_prev (A ! x) = Some x'\<close> \<open>get_next (A ! x) = None\<close>
      using vmtf vmtf_append_decomp[of xs' x' x ys m A] unfolding l xs ys
      by (auto simp: vmtf_single_iff intro: vmtf_last_mid_get_prev)
    then show ?thesis
      using vmtf unfolding r_l unfolding l xs ys
      by (auto simp: vmtf_dequeue_def Let_def vmtf_append_decomp split: option.splits
          intro: vmtf.intros)
  next
    case xs_ys_nempty note xs = this(1) and ys = this(2)
    have vmtf_x'_x: \<open>vmtf (xs' @ [x', x] @ (y' #  ys')) m A\<close> and vmtf_x_y: \<open>vmtf ((xs' @ [x']) @ [x, y'] @ ys') m A\<close>
      using vmtf unfolding l xs ys by simp_all
    from vmtf_append_decomp[OF vmtf_x'_x] have
      vmtf_xs: \<open>vmtf (xs' @ [x']) m (A[x' := VMTF_ATM (stamp (A ! x')) (get_prev (A ! x')) None])\<close> and
      vmtf_ys: \<open>vmtf (x # y' # ys') (stamp (A ! x)) (A[x := VMTF_ATM (stamp (A ! x)) None (get_next (A ! x))])\<close> and
      stamp: \<open>stamp (A ! x) < stamp (A ! x')\<close>
      by fast+
    have [simp]: \<open>y' < length A\<close> \<open>x < length A\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> \<open>x' < length A\<close> \<open>y' \<noteq> x'\<close>
      and x_ys': \<open>x \<notin> set ys'\<close> and x'_ys': \<open>x' \<notin> set ys'\<close> and y'_xs': \<open>y' \<notin> set xs'\<close>
      using vmtf_distinct[OF vmtf] vmtf_le_length[OF vmtf] unfolding l xs ys
      by auto
    obtain n where
      vmtf_ys': \<open>vmtf (y' # ys') n (A[x := VMTF_ATM (stamp (A ! x)) None (get_next (A ! x)),
          y' := VMTF_ATM (stamp (A[x := VMTF_ATM (stamp (A ! x)) None (get_next (A ! x))] ! y')) None
       (get_next (A[x := VMTF_ATM (stamp (A ! x)) None (get_next (A ! x))] ! y'))])\<close> and
      \<open>n \<le> stamp (A ! x)\<close>
      using vmtf_skip_fst[OF vmtf_ys] by blast
    then have vmtf_y'_ys'_x_y': \<open>vmtf (y' # ys') n (A[x := VMTF_ATM (stamp (A ! x)) None (get_next (A ! x)),
          y' := VMTF_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      by auto

    define A' where \<open>A' = A[x' := VMTF_ATM (stamp (A ! x')) (get_prev (A ! x')) None,
         y' := VMTF_ATM (stamp (A ! y')) None (get_next (A ! y'))]\<close>
    have vmtf_y'_ys'_y': \<open>vmtf (y' # ys') n (A[y' := VMTF_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      apply (rule vmtf_eq_iff[THEN iffD1, OF _ _ vmtf_y'_ys'_x_y'])
      subgoal using x_ys' by auto
      subgoal using vmtf_le_length[OF vmtf] unfolding l xs ys by auto
      done
    moreover have stamp_y'_n: \<open>stamp (A[x' := VMTF_ATM (stamp (A ! x')) (get_prev (A ! x')) None] ! y') \<le> n\<close>
      using vmtf_stamp_sorted[OF vmtf_y'_ys'_y'] stamp unfolding l xs ys
      by (auto simp: sorted_append)
    ultimately have vmtf_y'_ys'_y': \<open>vmtf (y' # ys') (stamp (A' ! y'))
       (A[y' := VMTF_ATM (stamp (A ! y')) None (get_next (A ! y'))])\<close>
      using l vmtf vmtf_append_decomp xs_ys_nempty(2) A'_def by auto
    have vmtf_y'_ys'_x'_y': \<open>vmtf (y' # ys') (stamp (A' ! y')) A'\<close>
      apply (rule vmtf_eq_iff[THEN iffD1, OF _ _ vmtf_y'_ys'_y'])
      subgoal using vmtf_distinct[OF vmtf_y'_ys'_y'] vmtf_le_length[OF vmtf_y'_ys'_y'] x'_ys' A'_def
        by auto
      subgoal using vmtf_distinct[OF vmtf_y'_ys'_y'] vmtf_le_length[OF vmtf_y'_ys'_y'] x'_ys' A'_def
        by auto
      done
    have vmtf_xs': \<open>vmtf (xs' @ [x']) m A'\<close>
      apply (rule vmtf_eq_iff[THEN iffD1, OF _ _ vmtf_xs])
      subgoal using y'_xs' A'_def by auto
      subgoal using vmtf_le_length[OF vmtf_xs] A'_def by auto
      done
    have \<open>vmtf (xs' @ [x', y'] @ ys') m
       (A'[x' := VMTF_ATM (stamp (A' ! x')) (get_prev (A' ! x')) (Some y'),
         y' := VMTF_ATM (stamp (A' ! y')) (Some x') (get_next (A' ! y'))])\<close>
      apply (rule vmtf_append_rebuild[OF vmtf_xs' vmtf_y'_ys'_x'_y'])
      subgoal using stamp_y'_n vmtf_xs vmtf_ys stamp \<open>n \<le> stamp (A ! x)\<close> unfolding A'_def by auto
      subgoal by (metis append.assoc append_Cons distinct_remove1 r_l self_append_conv2 vmtf vmtf_distinct xs ys)
      done
    moreover have \<open>xs' @ [x', y'] @ ys' = remove1 x l\<close>
      unfolding r_l xs ys by auto
    moreover have \<open>A'[x' := VMTF_ATM (stamp (A' ! x')) (get_prev (A' ! x')) (Some y'),
         y' := VMTF_ATM (stamp (A' ! y')) (Some x') (get_next (A' ! y'))] = vmtf_dequeue A x\<close>
      using vmtf_last_mid_get_next[OF vmtf_x_y] vmtf_last_mid_get_prev[OF vmtf_x'_x]
      unfolding A'_def vmtf_dequeue_def (* TODO proof *)
      apply (auto simp: Let_def)
        by (metis (no_types, lifting) list_update_overwrite list_update_swap)
    ultimately show ?thesis
      by force
  qed
qed



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