theory Watched_Literals_VMTF
imports Watched_Literals.Watched_Literals_Watch_List_Domain
begin


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

type_synonym 'v abs_vmtf_ns = \<open>'v set \<times> 'v set\<close>
type_synonym 'v abs_vmtf_ns_remove = \<open>'v abs_vmtf_ns \<times> 'v set\<close>

datatype ('v, 'n) vmtf_node = VMTF_Node (stamp : 'n) (get_prev: \<open>'v option\<close>) (get_next: \<open>'v option\<close>)
type_synonym nat_vmtf_node = \<open>(nat, nat) vmtf_node\<close>

inductive vmtf_ns :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat_vmtf_node list \<Rightarrow> bool\<close> where
Nil: \<open>vmtf_ns [] st xs\<close> |
Cons1: \<open>a < length xs \<Longrightarrow> m \<ge> n \<Longrightarrow> xs ! a = VMTF_Node (n::nat) None None \<Longrightarrow> vmtf_ns [a] m xs\<close> |
Cons: \<open>vmtf_ns (b # l) m xs \<Longrightarrow> a < length xs \<Longrightarrow> xs ! a = VMTF_Node n None (Some b) \<Longrightarrow>
  a \<noteq> b \<Longrightarrow> a \<notin> set l \<Longrightarrow> n > m \<Longrightarrow>
  xs' = xs[b := VMTF_Node (stamp (xs!b)) (Some a) (get_next (xs!b))] \<Longrightarrow> n' \<ge> n \<Longrightarrow>
  vmtf_ns (a # b # l) n' xs'\<close>

inductive_cases vmtf_nsE: \<open>vmtf_ns xs st zs\<close>

lemma vmtf_ns_le_length: \<open>vmtf_ns l m xs \<Longrightarrow> i \<in> set l \<Longrightarrow> i < length xs\<close>
  apply (induction rule: vmtf_ns.induct)
  subgoal by (auto intro: vmtf_ns.intros)
  subgoal by (auto intro: vmtf_ns.intros)
  subgoal by (auto intro: vmtf_ns.intros)
  done

lemma vmtf_ns_distinct: \<open>vmtf_ns l m xs \<Longrightarrow> distinct l\<close>
  apply (induction rule: vmtf_ns.induct)
  subgoal by (auto intro: vmtf_ns.intros)
  subgoal by (auto intro: vmtf_ns.intros)
  subgoal by (auto intro: vmtf_ns.intros)
  done

lemma vmtf_ns_eq_iff:
  assumes
    \<open>\<forall>i \<in> set l. xs ! i = zs ! i\<close> and
    \<open>\<forall>i \<in> set l. i < length xs \<and> i < length zs\<close>
  shows \<open>vmtf_ns l m zs \<longleftrightarrow> vmtf_ns l m xs\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have \<open>vmtf_ns l m xs\<close>
    if
      \<open>vmtf_ns l m zs\<close> and
      \<open>(\<forall>i \<in> set l. xs ! i = zs ! i)\<close> and
      \<open>(\<forall>i \<in> set l. i < length xs \<and> i < length zs)\<close>
    for xs zs
    using that
  proof (induction arbitrary: xs rule: vmtf_ns.induct)
    case (Nil st xs zs)
    then show ?case by (auto intro: vmtf_ns.intros)
  next
    case (Cons1 a xs n zs)
    show ?case by (rule vmtf_ns.Cons1) (use Cons1 in \<open>auto intro: vmtf_ns.intros\<close>)
  next
    case (Cons b l m xs c n zs n' zs') note vmtf_ns = this(1) and a_le_y = this(2) and zs_a = this(3)
      and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and nn' = this(8) and
       IH = this(9) and H = this(10-)
    have \<open>vmtf_ns (c # b # l) n' zs\<close>
      by (rule vmtf_ns.Cons[OF Cons.hyps])
    have [simp]: \<open>b < length xs\<close>  \<open>b < length zs\<close>
      using H xs' by auto
    have [simp]: \<open>b \<notin> set l\<close>
      using vmtf_ns_distinct[OF vmtf_ns] by auto
    then have K: \<open>\<forall>i\<in>set l. zs ! i = (if b = i then x else xs ! i) =
       (\<forall>i\<in>set l. zs ! i = xs ! i)\<close> for x
       using H(2)
       by (simp add: H(1) xs')
    have next_xs_b: \<open>get_next (xs ! b) = None\<close> if \<open>l = []\<close>
      using vmtf_ns unfolding that by (auto simp: elim!: vmtf_nsE)
    have prev_xs_b: \<open>get_prev (xs ! b) = None\<close>
      using vmtf_ns by (auto elim: vmtf_nsE)
    have vmtf_ns_zs: \<open>vmtf_ns (b # l) m (zs'[b := xs!b])\<close>
      apply (rule IH)
      subgoal using H(1) ab next_xs_b prev_xs_b H unfolding xs' by (auto simp: K)
      subgoal using H(2) ab next_xs_b prev_xs_b unfolding xs' by (auto simp: K)
      done
    have \<open>zs' ! b = VMTF_Node (stamp (xs ! b)) (Some c) (get_next (xs ! b))\<close>
      using H(1) unfolding xs' by auto
    show ?case
      apply (rule vmtf_ns.Cons[OF vmtf_ns_zs, of _ n])
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

lemmas vmtf_ns_eq_iffI = vmtf_ns_eq_iff[THEN iffD1]

lemma vmtf_ns_stamp_increase: \<open>vmtf_ns xs p zs \<Longrightarrow> p \<le> p' \<Longrightarrow> vmtf_ns xs p' zs\<close>
  apply (induction rule: vmtf_ns.induct)
  subgoal by (auto intro: vmtf_ns.intros)
  subgoal by (rule vmtf_ns.Cons1) (auto intro!: vmtf_ns.intros)
  subgoal by (auto intro: vmtf_ns.intros)
  done

lemma vmtf_ns_single_iff: \<open>vmtf_ns [a] m xs \<longleftrightarrow> (a < length xs \<and> m \<ge> stamp (xs ! a) \<and>
     xs ! a = VMTF_Node (stamp (xs ! a)) None None)\<close>
  by (auto 5 5 elim!: vmtf_nsE intro: vmtf_ns.intros)

lemma vmtf_ns_append_decomp:
  assumes \<open>vmtf_ns (axs @ [ax, ay] @ azs) an ns\<close>
  shows \<open>(vmtf_ns (axs @ [ax]) an (ns[ax:= VMTF_Node (stamp (ns!ax)) (get_prev (ns!ax)) None]) \<and>
    vmtf_ns (ay # azs) (stamp (ns!ay)) (ns[ay:= VMTF_Node (stamp (ns!ay)) None (get_next (ns!ay))]) \<and>
    stamp (ns!ax) > stamp (ns!ay))\<close>
  using assms
proof (induction \<open>axs @ [ax, ay] @ azs\<close> an ns arbitrary: axs ax ay azs rule: vmtf_ns.induct)
  case (Nil st xs)
  then show ?case by simp
next
  case (Cons1 a xs m n)
  then show ?case by auto
next
  case (Cons b l m xs a n xs' n') note vmtf_ns = this(1) and IH = this(2) and a_le_y = this(3) and
    zs_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10-)
  have b_le_xs: \<open>b < length xs\<close>
    using vmtf_ns by (auto intro: vmtf_ns_le_length simp: xs')
  show ?case
  proof (cases \<open>axs\<close>)
    case [simp]: Nil
    then have [simp]: \<open>ax = a\<close> \<open>ay = b\<close> \<open>azs = l\<close>
      using decomp by auto
    show ?thesis
    proof (cases l)
      case Nil
      then show ?thesis
        using vmtf_ns xs' a_le_y zs_a ab a_l mn nn' by (cases \<open>xs ! b\<close>)
          (auto simp: vmtf_ns_single_iff)
    next
      case (Cons al als) note l = this
      have vmtf_ns_b: \<open>vmtf_ns [b] m (xs[b := VMTF_Node (stamp (xs ! b)) (get_prev (xs ! b)) None])\<close> and
        vmtf_ns_l: \<open>vmtf_ns (al # als) (stamp (xs ! al))
           (xs[al := VMTF_Node (stamp (xs ! al)) None (get_next (xs ! al))])\<close> and
        stamp_al_b: \<open>stamp (xs ! al) < stamp (xs ! b)\<close>
        using IH[of Nil b al als] unfolding l by auto
      have \<open>vmtf_ns [a] n' (xs'[a := VMTF_Node (stamp (xs' ! a)) (get_prev (xs' ! a)) None])\<close>
          using a_le_y xs' ab mn nn' zs_a by (auto simp: vmtf_ns_single_iff)
      have al_b[simp]: \<open>al \<noteq> b\<close> and b_als: \<open>b \<notin> set als\<close>
        using vmtf_ns unfolding l by (auto dest: vmtf_ns_distinct)
      have al_le_xs: \<open>al < length xs\<close>
        using vmtf_ns vmtf_ns_l by (auto intro: vmtf_ns_le_length simp: l xs')
      have xs_al: \<open>xs ! al = VMTF_Node (stamp (xs ! al)) (Some b) (get_next (xs ! al))\<close>
        using vmtf_ns unfolding l by (auto 5 5 elim: vmtf_nsE)
      have xs_b: \<open>xs ! b = VMTF_Node (stamp (xs ! b)) None (get_next (xs ! b))\<close>
        using vmtf_ns_b vmtf_ns xs' by (cases \<open>xs ! b\<close>) (auto elim: vmtf_nsE simp: l vmtf_ns_single_iff)

      have \<open>vmtf_ns (b # al # als) (stamp (xs' ! b))
          (xs'[b := VMTF_Node (stamp (xs' ! b)) None (get_next (xs' ! b))])\<close>
        apply (rule vmtf_ns.Cons[OF vmtf_ns_l, of _ \<open>stamp (xs' ! b)\<close>])
        subgoal using b_le_xs by auto
        subgoal using xs_b vmtf_ns_b vmtf_ns xs' by (cases \<open>xs ! b\<close>)
            (auto elim: vmtf_nsE simp: l vmtf_ns_single_iff)
        subgoal using al_b by blast
        subgoal using b_als .
        subgoal using xs' b_le_xs stamp_al_b by (simp add:)
        subgoal using ab unfolding xs' by (simp add: b_le_xs al_le_xs xs_al[symmetric]
              xs_b[symmetric])
        subgoal by simp
        done
      moreover have \<open>vmtf_ns [a] n'
          (xs'[a := VMTF_Node (stamp (xs' ! a)) (get_prev (xs' ! a)) None])\<close>
        using ab a_le_y mn nn' zs_a by (auto simp: vmtf_ns_single_iff xs')
      moreover have \<open>stamp (xs' ! b) < stamp (xs' ! a)\<close>
        using b_le_xs ab mn vmtf_ns_b zs_a by (auto simp add: xs' vmtf_ns_single_iff)
      ultimately show ?thesis
        unfolding l by (simp add: l)
    qed
  next
    case (Cons aaxs axs') note axs = this
    have [simp]: \<open>aaxs = a\<close> and bl: \<open>b # l = axs' @ [ax, ay] @ azs\<close>
      using decomp unfolding axs by simp_all
    have
      vmtf_ns_axs': \<open>vmtf_ns (axs' @ [ax]) m
        (xs[ax := VMTF_Node (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close> and
      vmtf_ns_ay: \<open>vmtf_ns (ay # azs) (stamp (xs ! ay))
        (xs[ay := VMTF_Node (stamp (xs ! ay)) None (get_next (xs ! ay))])\<close> and
      stamp: \<open>stamp (xs ! ay) < stamp (xs ! ax)\<close>
      using IH[OF bl] by fast+
    have b_ay: \<open>b \<noteq> ay\<close>
      using bl vmtf_ns_distinct[OF vmtf_ns] by (cases axs') auto
    have vmtf_ns_ay': \<open>vmtf_ns (ay # azs) (stamp (xs' ! ay))
        (xs[ay := VMTF_Node (stamp (xs ! ay)) None (get_next (xs ! ay))])\<close>
      using vmtf_ns_ay xs' b_ay by (auto)
    have [simp]: \<open>ay < length xs\<close>
        using vmtf_ns by (auto intro: vmtf_ns_le_length simp: bl xs')
    have in_azs_noteq_b: \<open>i \<in> set azs \<Longrightarrow> i \<noteq> b\<close> for i
      using vmtf_ns_distinct[OF vmtf_ns] bl by (cases axs') (auto simp: xs' b_ay)
    have a_ax[simp]: \<open>a \<noteq> ax\<close>
      using ab a_l bl by (cases axs') (auto simp: xs' b_ay)
    have \<open>vmtf_ns (axs @ [ax]) n'
       (xs'[ax := VMTF_Node (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
    proof (cases axs')
      case Nil
      then have [simp]: \<open>ax = b\<close>
        using bl by auto
      have \<open>vmtf_ns [ax] m (xs[ax := VMTF_Node (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close>
        using vmtf_ns_axs' unfolding axs Nil by simp
      then have \<open>vmtf_ns (aaxs # ax # []) n'
          (xs'[ax := VMTF_Node (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
        apply (rule vmtf_ns.Cons[of _ _ _ _ _ n])
        subgoal using a_le_y by auto
        subgoal using zs_a a_le_y ab by auto
        subgoal using ab by auto
        subgoal by simp
        subgoal using mn .
        subgoal using zs_a a_le_y ab xs' b_le_xs by auto
        subgoal using nn' .
        done
      then show ?thesis
        using vmtf_ns_axs' unfolding axs Nil by simp
    next
      case (Cons aaaxs' axs'')
      have [simp]: \<open>aaaxs' = b\<close>
        using bl unfolding Cons by auto
      have \<open>vmtf_ns (aaaxs' # axs'' @ [ax]) m
          (xs[ax := VMTF_Node (stamp (xs ! ax)) (get_prev (xs ! ax)) None])\<close>
        using vmtf_ns_axs' unfolding axs Cons by simp
      then have \<open>vmtf_ns (a # aaaxs' # axs'' @ [ax]) n'
          (xs'[ax := VMTF_Node (stamp (xs' ! ax)) (get_prev (xs' ! ax)) None])\<close>
        apply (rule vmtf_ns.Cons[of _ _ _ _ _ n])
        subgoal using a_le_y by auto
        subgoal using zs_a a_le_y a_ax ab by (auto simp del: \<open>a \<noteq> ax\<close>)
        subgoal using ab by auto
        subgoal using a_l bl unfolding Cons by simp
        subgoal using mn .
        subgoal using zs_a a_le_y ab xs' b_le_xs by (auto simp: list_update_swap)
        subgoal using nn' .
        done
      then show ?thesis
        unfolding axs Cons by simp
    qed
    moreover have \<open>vmtf_ns (ay # azs) (stamp (xs' ! ay))
        (xs'[ay := VMTF_Node (stamp (xs' ! ay)) None (get_next (xs' ! ay))])\<close>
      apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_ns_ay'])
      subgoal using vmtf_ns_distinct[OF vmtf_ns] bl b_le_xs in_azs_noteq_b by (auto simp: xs' b_ay)
      subgoal using vmtf_ns_le_length[OF vmtf_ns] bl unfolding xs' by auto
      done
    moreover have \<open>stamp (xs' ! ay) < stamp (xs' ! ax)\<close>
      using stamp unfolding axs xs' by (auto simp: b_le_xs b_ay)
    ultimately show ?thesis
      unfolding axs xs' by fast
  qed
qed

lemma vmtf_ns_append_rebuild:
  assumes
    \<open>(vmtf_ns (axs @ [ax]) an ns) \<close> and
    \<open>vmtf_ns (ay # azs) (stamp (ns!ay)) ns\<close> and
    \<open>stamp (ns!ax) > stamp (ns!ay)\<close> and
    \<open>distinct (axs @ [ax, ay] @ azs)\<close>
  shows \<open>vmtf_ns (axs @ [ax, ay] @ azs) an
    (ns[ax := VMTF_Node (stamp (ns!ax)) (get_prev (ns!ax)) (Some ay) ,
       ay := VMTF_Node (stamp (ns!ay)) (Some ax) (get_next (ns!ay))])\<close>
  using assms
proof (induction \<open>axs @ [ax]\<close> an ns arbitrary: axs ax ay azs rule: vmtf_ns.induct)
  case (Nil st xs)
  then show ?case by simp
next
  case (Cons1 a xs m n) note a_le_xs = this(1) and nm = this(2) and xs_a = this(3) and a = this(4)
    and vmtf_ns = this(5) and stamp = this(6) and dist = this(7)
  have a_ax: \<open>ax = a\<close>
    using a by simp

  have vmtf_ns_ay': \<open>vmtf_ns (ay # azs) (stamp (xs ! ay)) (xs[ax := VMTF_Node n None (Some ay)])\<close>
    apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_ns])
    subgoal using dist a_ax a_le_xs by auto
    subgoal using vmtf_ns vmtf_ns_le_length by auto
    done

  then have \<open>vmtf_ns (ax # ay # azs) m (xs[ax := VMTF_Node n None (Some ay),
      ay := VMTF_Node (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    apply (rule vmtf_ns.Cons[of _ _ _ _ _ \<open>stamp (xs ! a)\<close>])
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
  case (Cons b l m xs a n xs' n') note vmtf_ns = this(1) and IH = this(2) and a_le_y = this(3) and
    zs_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10) and vmtf_ns_ay = this(11) and stamp = this(12) and
    dist = this(13)

  have dist_b: \<open>distinct ((a # b # l) @ ay # azs)\<close>
    using dist unfolding decomp by auto
  then have b_ay: \<open>b \<noteq> ay\<close>
    by auto
  have b_le_xs: \<open>b < length xs\<close>
    using vmtf_ns vmtf_ns_le_length by auto
  have a_ax: \<open>a \<noteq> ax\<close> and a_ay: \<open>a \<noteq> ay\<close>
    using dist_b decomp dist by (cases axs; auto)+
  have vmtf_ns_ay': \<open>vmtf_ns (ay # azs) (stamp (xs ! ay)) xs\<close>
    apply (rule vmtf_ns_eq_iffI[of _ _ xs'])
    subgoal using xs' b_ay dist_b b_le_xs by auto
    subgoal using vmtf_ns_le_length[OF vmtf_ns_ay] xs' by auto
    subgoal using xs' b_ay dist_b b_le_xs vmtf_ns_ay xs' by auto
    done

  have \<open>vmtf_ns (tl axs @ [ax, ay] @ azs) m
          (xs[ax := VMTF_Node (stamp (xs ! ax)) (get_prev (xs ! ax)) (Some ay),
              ay := VMTF_Node (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    apply (rule IH)
    subgoal using decomp by (cases axs) auto
    subgoal using vmtf_ns_ay' .
    subgoal using stamp xs' b_ay b_le_xs by (cases \<open>ax = b\<close>) auto
    subgoal using dist by (cases axs) auto
    done
  moreover have \<open>tl axs @ [ax, ay] @ azs = b # l @ ay # azs\<close>
    using decomp by (cases axs) auto
  ultimately have vmtf_ns_tl_axs: \<open>vmtf_ns (b # l @ ay # azs) m
          (xs[ax := VMTF_Node (stamp (xs ! ax)) (get_prev (xs ! ax)) (Some ay),
              ay := VMTF_Node (stamp (xs ! ay)) (Some ax) (get_next (xs ! ay))])\<close>
    by metis

  then have \<open>vmtf_ns (a # b # l @ ay # azs) n'
     (xs'[ax := VMTF_Node (stamp (xs' ! ax)) (get_prev (xs' ! ax)) (Some ay),
          ay := VMTF_Node (stamp (xs' ! ay)) (Some ax) (get_next (xs' ! ay))])\<close>
    apply (rule vmtf_ns.Cons[of _ _ _ _ _ \<open>stamp (xs ! a)\<close>])
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
definition ns_vmtf_dequeue :: \<open>nat \<Rightarrow> nat_vmtf_node list \<Rightarrow> nat_vmtf_node list\<close> where
\<open>ns_vmtf_dequeue y xs =
  (let x = xs ! y;
   u_prev =
      (case get_prev x of None \<Rightarrow> xs
      | Some a \<Rightarrow> xs[a:= VMTF_Node (stamp (xs!a)) (get_prev (xs!a)) (get_next x)]);
   u_next =
      (case get_next x of None \<Rightarrow> u_prev
      | Some a \<Rightarrow> u_prev[a:= VMTF_Node (stamp (u_prev!a)) (get_prev x) (get_next (u_prev!a))]);
    u_x = u_next[y:= VMTF_Node (stamp (u_next!y)) None None]
    in
   u_x)
  \<close>

lemma vmtf_ns_different_same_neq: \<open>vmtf_ns (b # c # l') m xs \<Longrightarrow> vmtf_ns (c # l') m xs \<Longrightarrow> False\<close>
  apply (cases l')
  subgoal by (force elim: vmtf_nsE)
  subgoal for x xs
    apply (subst (asm) vmtf_ns.simps)
    apply (subst (asm)(2) vmtf_ns.simps)
    by (metis (no_types, lifting) vmtf_node.inject length_list_update list.discI list_tail_coinc
        nth_list_update_eq nth_list_update_neq option.discI)
  done

lemma vmtf_ns_last_next:
  \<open>vmtf_ns (xs @ [x]) m ns \<Longrightarrow> get_next (ns ! x) = None\<close>
  apply (induction "xs @ [x]" m ns arbitrary: xs x rule: vmtf_ns.induct)
  subgoal by auto
  subgoal by auto
  subgoal for b l m xs a n xs' n' xsa x
    by (cases \<open>xs ! b\<close>; cases \<open>x = b\<close>; cases xsa)
       (force simp: vmtf_ns_le_length)+
  done

lemma vmtf_ns_last_mid_get_next:
  \<open>vmtf_ns (xs @ [x, y] @ zs) m ns \<Longrightarrow> get_next (ns ! x) = Some y\<close>
  apply (induction "xs @ [x, y] @ zs" m ns arbitrary: xs x rule: vmtf_ns.induct)
  subgoal by auto
  subgoal by auto
  subgoal for b l m xs a n xs' n' xsa x
    by (cases \<open>xs ! b\<close>; cases \<open>x = b\<close>; cases xsa)
       (force simp: vmtf_ns_le_length)+
  done

lemma vmtf_ns_last_mid_get_next_option_hd:
  \<open>vmtf_ns (xs @ x # zs) m ns \<Longrightarrow> get_next (ns ! x) = option_hd zs\<close>
  using vmtf_ns_last_mid_get_next[of xs x \<open>hd zs\<close> \<open>tl zs\<close> m ns]
  vmtf_ns_last_next[of xs x]
  by (cases zs) auto

lemma vmtf_ns_last_mid_get_prev:
  assumes \<open>vmtf_ns (xs @ [x, y] @ zs) m ns\<close>
  shows \<open>get_prev (ns ! y) = Some x\<close>
    using assms
proof (induction "xs @ [x, y] @ zs" m ns arbitrary: xs x rule: vmtf_ns.induct)
  case (Nil st xs)
  then show ?case by auto
next
  case (Cons1 a xs m n)
  then show ?case by auto
next
  case (Cons b l m xxs a n xxs' n') note vmtf_ns = this(1) and IH = this(2) and a_le_y = this(3) and
    zs_a = this(4) and ab = this(5) and a_l = this(6) and mn = this(7) and xs' = this(8) and
    nn' = this(9) and decomp = this(10)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Cons vmtf_ns_le_length by auto
  next
    case (Cons aaxs axs')
    then have b_l: \<open>b # l = tl xs @ [x, y] @ zs\<close>
      using decomp by auto
    then have \<open>get_prev (xxs ! y) = Some x\<close>
      by (rule IH)
    moreover have \<open>x \<noteq> y\<close>
      using vmtf_ns_distinct[OF vmtf_ns] b_l by auto
    moreover have \<open>b \<noteq> y\<close>
      using vmtf_ns_distinct[OF vmtf_ns] decomp by (cases axs') (auto simp add: Cons)
    moreover have \<open>y < length xxs\<close> \<open>b < length xxs\<close>
      using vmtf_ns_le_length[OF vmtf_ns, unfolded b_l] vmtf_ns_le_length[OF vmtf_ns] by auto
    ultimately show ?thesis
      unfolding xs' by auto
  qed
qed

lemma vmtf_ns_last_mid_get_prev_option_last:
  \<open>vmtf_ns (xs @ x # zs) m ns \<Longrightarrow> get_prev (ns ! x) = option_last xs\<close>
  using vmtf_ns_last_mid_get_prev[of \<open>butlast xs\<close> \<open>last xs\<close> \<open>x\<close> \<open>zs\<close> m ns]
  by (cases xs rule: rev_cases) (auto elim: vmtf_nsE)

lemma length_ns_vmtf_dequeue[simp]: \<open>length (ns_vmtf_dequeue x ns) = length ns\<close>
  unfolding ns_vmtf_dequeue_def by (auto simp: Let_def split: option.splits)

lemma vmtf_ns_skip_fst:
  assumes vmtf_ns: \<open>vmtf_ns (x # y' # zs') m ns\<close>
  shows \<open>\<exists>n. vmtf_ns (y' # zs') n (ns[y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))]) \<and>
     m \<ge> n\<close>
  using assms
proof (rule vmtf_nsE, goal_cases)
  case 1
  then show ?case by simp
next
  case (2 a n)
  then show ?case by simp
next
  case (3 b l m xs a n)
  moreover have \<open>get_prev (xs ! b) = None\<close>
    using 3(3) by (fastforce elim: vmtf_nsE)
  moreover have \<open>b < length xs\<close>
    using 3(3) vmtf_ns_le_length by auto
  ultimately show ?case
    by (cases \<open>xs ! b\<close>) (auto simp: eq_commute[of \<open>xs ! b\<close>])
qed

definition vmtf_ns_notin where
  \<open>vmtf_ns_notin l m xs \<longleftrightarrow> (\<forall>i<length xs. i\<notin>set l \<longrightarrow> (get_prev (xs ! i) = None \<and>
      get_next (xs ! i) = None))\<close>

lemma vmtf_ns_notinI:
  \<open>(\<And>i. i <length xs \<Longrightarrow> i\<notin>set l \<Longrightarrow> get_prev (xs ! i) = None \<and>
      get_next (xs ! i) = None) \<Longrightarrow> vmtf_ns_notin l m xs\<close>
  by (auto simp: vmtf_ns_notin_def)

lemma stamp_ns_vmtf_dequeue:
  \<open>axs < length zs \<Longrightarrow> stamp (ns_vmtf_dequeue x zs ! axs) = stamp (zs ! axs)\<close>
  by (cases \<open>zs ! (the (get_next (zs ! x)))\<close>; cases \<open>(the (get_next (zs ! x))) = axs\<close>;
      cases \<open>(the (get_prev (zs ! x))) = axs\<close>; cases \<open>zs ! x\<close>)
    (auto simp: nth_list_update' ns_vmtf_dequeue_def Let_def split: option.splits)

lemma sorted_many_eq_append: \<open>sorted (xs @ [x, y]) \<longleftrightarrow> sorted (xs @ [x]) \<and> x \<le> y\<close>
  using sorted_append[of \<open>xs @ [x]\<close> \<open>[y]\<close>] sorted_append[of xs \<open>[x]\<close>]
  by force

lemma vmtf_ns_stamp_sorted:
  assumes \<open>vmtf_ns l m ns\<close>
  shows \<open>sorted (map (\<lambda>a. stamp (ns!a)) (rev l)) \<and> (\<forall>a \<in> set l. stamp (ns!a) \<le> m)\<close>
  using assms
proof (induction rule: vmtf_ns.induct)
  case (Cons b l m xs a n xs' n') note vmtf_ns = this(1) and IH = this(9) and a_le_y = this(2) and
    zs_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8)
  have H:
  \<open>map (\<lambda>aa. stamp (xs[b := VMTF_Node (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! aa)) (rev l) =
     map (\<lambda>a. stamp (xs ! a)) (rev l)\<close>
    apply (rule map_cong)
    subgoal by auto
    subgoal using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] by auto
    done
  have [simp]: \<open>stamp (xs[b := VMTF_Node (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! b) =
     stamp (xs ! b)\<close>
    using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] by (cases \<open>xs ! b\<close>) auto
  have \<open>stamp (xs[b := VMTF_Node (stamp (xs ! b)) (Some a) (get_next (xs ! b))] ! aa) \<le> n'\<close>
    if \<open>aa \<in> set l\<close> for aa
    apply (cases \<open>aa = b\<close>)
    subgoal using Cons by auto
    subgoal using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] IH nn' mn that by auto
    done
  then show ?case
    using Cons by (auto simp: H sorted_many_eq_append)
qed auto

lemma vmtf_ns_ns_vmtf_dequeue:
  assumes vmtf_ns: \<open>vmtf_ns l m ns\<close> and notin: \<open>vmtf_ns_notin l m ns\<close> and valid: \<open>x < length ns\<close>
  shows \<open>vmtf_ns (remove1 x l) m (ns_vmtf_dequeue x ns)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  have
      \<open>get_prev (ns ! x) = None \<close> and
      \<open>get_next (ns ! x) = None\<close>
    using notin False valid unfolding vmtf_ns_notin_def by auto
  then have vmtf_ns_eq: \<open>(ns_vmtf_dequeue x ns) ! a = ns ! a\<close> if \<open>a \<in> set l\<close> for a
    using that False valid unfolding vmtf_ns_notin_def ns_vmtf_dequeue_def
    by (cases \<open>ns ! (the (get_prev (ns ! x)))\<close>; cases \<open>ns ! (the (get_next (ns ! x)))\<close>)
      (auto simp: Let_def split: option.splits)
  show ?thesis
    unfolding H
    apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_ns])
    subgoal using vmtf_ns_eq by blast
    subgoal using vmtf_ns_le_length[OF vmtf_ns] by auto
    done
next
  case True
  then obtain xs zs where
    l: \<open>l = xs @ x # zs\<close>
    by (meson split_list)
  have r_l: \<open>remove1 x l = xs @ zs\<close>
    using vmtf_ns_distinct[OF vmtf_ns] unfolding l by (simp add: remove1_append)
  have dist: \<open>distinct l\<close>
    using vmtf_ns_distinct[OF vmtf_ns] .
  have le_length: \<open>i \<in> set l \<Longrightarrow> i < length ns\<close> for i
    using vmtf_ns_le_length[OF vmtf_ns] .
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
      using vmtf_ns by (auto simp: r_l intro: vmtf_ns.intros)
  next
    case xs_empty_zs_nempty note xs = this(1) and zs = this(2)
    have [simp]: \<open>x \<noteq> y'\<close> \<open>y' \<noteq> x\<close> \<open>x \<notin> set zs'\<close>
      using dist unfolding l xs zs by auto
    have prev_next: \<open>get_prev (ns ! x) = None\<close> \<open>get_next (ns ! x) = option_hd zs\<close>
      using vmtf_ns unfolding l xs zs
      by (cases zs; auto 5 5 simp: option_hd_def elim: vmtf_nsE; fail)+
    then have vmtf': \<open>vmtf_ns (y' # zs') m (ns[y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))])\<close>
      using vmtf_ns unfolding r_l unfolding l xs zs
      by (auto simp: ns_vmtf_dequeue_def Let_def nth_list_update' zs
          split: option.splits
          intro: vmtf_ns.intros vmtf_ns_stamp_increase dest: vmtf_ns_skip_fst)
    show ?thesis
      apply (rule vmtf_ns_eq_iffI[of _ _
            \<open>(ns[y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))])\<close> m])
      subgoal
        using prev_next unfolding r_l unfolding l xs zs
        by (cases \<open>ns ! x\<close>) (auto simp: ns_vmtf_dequeue_def Let_def nth_list_update')
      subgoal
        using prev_next le_length unfolding r_l unfolding l xs zs
        by (cases \<open>ns ! x\<close>) auto
      subgoal
        using vmtf' unfolding r_l unfolding l xs zs by auto
      done
  next
    case xs_nempty_zs_empty note xs = this(1) and zs = this(2)
    have [simp]: \<open>x \<noteq> x'\<close> \<open>x' \<noteq> x\<close> \<open>x' \<notin> set xs'\<close> \<open>x \<notin> set xs'\<close>
      using dist unfolding l xs zs by auto
    have prev_next: \<open>get_prev (ns ! x) = Some x'\<close> \<open>get_next (ns ! x) = None\<close>
      using vmtf_ns vmtf_ns_append_decomp[of xs' x' x zs m ns] unfolding l xs zs
      by (auto simp: vmtf_ns_single_iff intro: vmtf_ns_last_mid_get_prev)
    then have vmtf': \<open>vmtf_ns (xs' @ [x']) m (ns[x' := VMTF_Node (stamp (ns ! x')) (get_prev (ns ! x')) None])\<close>
      using vmtf_ns unfolding r_l unfolding l xs zs
      by (auto simp: ns_vmtf_dequeue_def Let_def vmtf_ns_append_decomp split: option.splits
          intro: vmtf_ns.intros)
    show ?thesis
      apply (rule vmtf_ns_eq_iffI[of _ _
            \<open>(ns[x' := VMTF_Node (stamp (ns ! x')) (get_prev (ns ! x')) None])\<close> m])
      subgoal
        using prev_next unfolding r_l unfolding l xs zs
        by (cases \<open>ns ! x'\<close>) (auto simp: ns_vmtf_dequeue_def Let_def nth_list_update')
      subgoal
        using prev_next le_length unfolding r_l unfolding l xs zs
        by (cases \<open>ns ! x\<close>) auto
      subgoal
        using vmtf' unfolding r_l unfolding l xs zs by auto
      done
  next
    case xs_zs_nempty note xs = this(1) and zs = this(2)
    have vmtf_ns_x'_x: \<open>vmtf_ns (xs' @ [x', x] @ (y' #  zs')) m ns\<close> and
      vmtf_ns_x_y: \<open>vmtf_ns ((xs' @ [x']) @ [x, y'] @ zs') m ns\<close>
      using vmtf_ns unfolding l xs zs by simp_all
    from vmtf_ns_append_decomp[OF vmtf_ns_x'_x] have
      vmtf_ns_xs: \<open>vmtf_ns (xs' @ [x']) m (ns[x' := VMTF_Node (stamp (ns ! x')) (get_prev (ns ! x')) None])\<close> and
      vmtf_ns_zs: \<open>vmtf_ns (x # y' # zs') (stamp (ns ! x)) (ns[x := VMTF_Node (stamp (ns ! x)) None (get_next (ns ! x))])\<close> and
      stamp: \<open>stamp (ns ! x) < stamp (ns ! x')\<close>
      by fast+
    have [simp]: \<open>y' < length ns\<close> \<open>x < length ns\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> \<open>x' < length ns\<close> \<open>y' \<noteq> x'\<close>
      \<open>x' \<noteq> x\<close> \<open>x \<noteq> x'\<close> \<open>y' \<noteq> x\<close>
      and x_zs': \<open>x \<notin> set zs'\<close> \<open>x \<notin> set xs'\<close> and x'_zs': \<open>x' \<notin> set zs'\<close> and y'_xs': \<open>y' \<notin> set xs'\<close>
      using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] unfolding l xs zs
      by auto
    obtain n where
      vmtf_ns_zs': \<open>vmtf_ns (y' # zs') n (ns[x := VMTF_Node (stamp (ns ! x)) None (get_next (ns ! x)),
          y' := VMTF_Node (stamp (ns[x := VMTF_Node (stamp (ns ! x)) None (get_next (ns ! x))] ! y')) None
       (get_next (ns[x := VMTF_Node (stamp (ns ! x)) None (get_next (ns ! x))] ! y'))])\<close> and
      \<open>n \<le> stamp (ns ! x)\<close>
      using vmtf_ns_skip_fst[OF vmtf_ns_zs] by blast
    then have vmtf_ns_y'_zs'_x_y': \<open>vmtf_ns (y' # zs') n (ns[x := VMTF_Node (stamp (ns ! x)) None (get_next (ns ! x)),
          y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))])\<close>
      by auto

    define ns' where \<open>ns' = ns[x' := VMTF_Node (stamp (ns ! x')) (get_prev (ns ! x')) None,
         y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))]\<close>
    have vmtf_ns_y'_zs'_y': \<open>vmtf_ns (y' # zs') n (ns[y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))])\<close>
      apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_ns_y'_zs'_x_y'])
      subgoal using x_zs' by auto
      subgoal using vmtf_ns_le_length[OF vmtf_ns] unfolding l xs zs by auto
      done
    moreover have stamp_y'_n: \<open>stamp (ns[x' := VMTF_Node (stamp (ns ! x')) (get_prev (ns ! x')) None] ! y') \<le> n\<close>
      using vmtf_ns_stamp_sorted[OF vmtf_ns_y'_zs'_y'] stamp unfolding l xs zs
      by (auto simp: sorted_append)
    ultimately have vmtf_ns_y'_zs'_y': \<open>vmtf_ns (y' # zs') (stamp (ns' ! y'))
       (ns[y' := VMTF_Node (stamp (ns ! y')) None (get_next (ns ! y'))])\<close>
      using l vmtf_ns vmtf_ns_append_decomp xs_zs_nempty(2) ns'_def by auto
    have vmtf_ns_y'_zs'_x'_y': \<open>vmtf_ns (y' # zs') (stamp (ns' ! y')) ns'\<close>
      apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_ns_y'_zs'_y'])
      subgoal using dist le_length x'_zs' ns'_def unfolding l xs zs by auto
      subgoal using dist le_length x'_zs' ns'_def unfolding l xs zs by auto
      done
    have vmtf_ns_xs': \<open>vmtf_ns (xs' @ [x']) m ns'\<close>
      apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_ns_xs])
      subgoal using y'_xs' ns'_def by auto
      subgoal using vmtf_ns_le_length[OF vmtf_ns_xs] ns'_def by auto
      done
    have vmtf_x'_y': \<open>vmtf_ns (xs' @ [x', y'] @ zs') m
       (ns'[x' := VMTF_Node (stamp (ns' ! x')) (get_prev (ns' ! x')) (Some y'),
         y' := VMTF_Node (stamp (ns' ! y')) (Some x') (get_next (ns' ! y'))])\<close>
      apply (rule vmtf_ns_append_rebuild[OF vmtf_ns_xs' vmtf_ns_y'_zs'_x'_y'])
      subgoal using stamp_y'_n vmtf_ns_xs vmtf_ns_zs stamp \<open>n \<le> stamp (ns ! x)\<close>
        unfolding ns'_def by auto
      subgoal by (metis append.assoc append_Cons distinct_remove1 r_l self_append_conv2 vmtf_ns
            vmtf_ns_distinct xs zs)
      done
    have \<open>vmtf_ns (xs' @ [x', y'] @ zs') m
       (ns'[x' := VMTF_Node (stamp (ns' ! x')) (get_prev (ns' ! x')) (Some y'),
         y' := VMTF_Node (stamp (ns' ! y')) (Some x') (get_next (ns' ! y')),
         x := VMTF_Node (stamp (ns' ! x)) None None])\<close>
      apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf_x'_y'])
      subgoal
        using vmtf_ns_last_mid_get_next[OF vmtf_ns_x_y] vmtf_ns_last_mid_get_prev[OF vmtf_ns_x'_x] x_zs'
        by (cases \<open>ns!x\<close>; auto simp: nth_list_update' ns'_def)
      subgoal using le_length unfolding l xs zs ns'_def by auto
      done
    moreover have \<open>xs' @ [x', y'] @ zs' = remove1 x l\<close>
      unfolding r_l xs zs by auto
    moreover have \<open>ns'[x' := VMTF_Node (stamp (ns' ! x')) (get_prev (ns' ! x')) (Some y'),
         y' := VMTF_Node (stamp (ns' ! y')) (Some x') (get_next (ns' ! y')),
         x := VMTF_Node (stamp (ns' ! x)) None None] = ns_vmtf_dequeue x ns\<close>
      using vmtf_ns_last_mid_get_next[OF vmtf_ns_x_y] vmtf_ns_last_mid_get_prev[OF vmtf_ns_x'_x]
      list_update_swap[of x' y' _ \<open>_ :: nat_vmtf_node\<close>]
      unfolding ns'_def ns_vmtf_dequeue_def
      by (auto simp: Let_def)
    ultimately show ?thesis
      by force
  qed
qed

lemma vmtf_ns_hd_next:
   \<open>vmtf_ns (x # a # list) m ns \<Longrightarrow> get_next (ns ! x) = Some a\<close>
  by (auto 5 5 elim: vmtf_nsE)

lemma vmtf_ns_notin_dequeue:
  assumes vmtf_ns: \<open>vmtf_ns l m ns\<close> and notin: \<open>vmtf_ns_notin l m ns\<close> and valid: \<open>x < length ns\<close>
  shows \<open>vmtf_ns_notin (remove1 x l) m (ns_vmtf_dequeue x ns)\<close>
proof (cases \<open>x \<in> set l\<close>)
  case False
  then have H: \<open>remove1 x l = l\<close>
    by (simp add: remove1_idem)
  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  have
    \<open>get_prev (ns ! x) = None\<close> and
    \<open>get_next (ns ! x) = None\<close>
    using notin False valid unfolding vmtf_ns_notin_def by auto
  show ?thesis
    using notin valid False unfolding vmtf_ns_notin_def
    by (auto simp: vmtf_ns_notin_def ns_vmtf_dequeue_def Let_def H split: option.splits)
next
  case True
  then obtain xs zs where
    l: \<open>l = xs @ x # zs\<close>
    by (meson split_list)
  have r_l: \<open>remove1 x l = xs @ zs\<close>
    using vmtf_ns_distinct[OF vmtf_ns] unfolding l by (simp add: remove1_append)

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
      using notin vmtf_ns unfolding l apply (cases \<open>ns ! x\<close>)
        by (auto simp: vmtf_ns_notin_def ns_vmtf_dequeue_def Let_def vmtf_ns_single_iff
           split: option.splits)
  next
    case xs_empty_zs_nempty note xs = this(1) and zs = this(1)
    have prev_next: \<open>get_prev (ns ! x) = None\<close> \<open>get_next (ns ! x) = option_hd zs\<close>
      using vmtf_ns unfolding l xs zs
      by (cases zs; auto simp: option_hd_def elim: vmtf_nsE dest: vmtf_ns_hd_next)+
    show ?thesis
      apply (rule vmtf_ns_notinI)
      apply (case_tac \<open>i = x\<close>)
      subgoal
        using vmtf_ns prev_next unfolding r_l unfolding l xs zs
        by (cases zs) (auto simp: ns_vmtf_dequeue_def Let_def
            vmtf_ns_notin_def vmtf_ns_single_iff
            split: option.splits)
      subgoal
        using vmtf_ns notin prev_next unfolding r_l unfolding l xs zs
        by (auto simp: ns_vmtf_dequeue_def Let_def
            vmtf_ns_notin_def vmtf_ns_single_iff
            split: option.splits
            intro: vmtf_ns.intros vmtf_ns_stamp_increase dest: vmtf_ns_skip_fst)
       done
  next
    case xs_nempty_zs_empty note xs = this(1) and zs = this(2)
    have prev_next: \<open>get_prev (ns ! x) = Some x'\<close> \<open>get_next (ns ! x) = None\<close>
      using vmtf_ns vmtf_ns_append_decomp[of xs' x' x zs m ns] unfolding l xs zs
      by (auto simp: vmtf_ns_single_iff intro: vmtf_ns_last_mid_get_prev)
    then show ?thesis
      using vmtf_ns notin unfolding r_l unfolding l xs zs
      by (auto simp: ns_vmtf_dequeue_def Let_def vmtf_ns_append_decomp vmtf_ns_notin_def
          split: option.splits
          intro: vmtf_ns.intros)
  next
    case xs_zs_nempty note xs = this(1) and zs = this(2)
    have vmtf_ns_x'_x: \<open>vmtf_ns (xs' @ [x', x] @ (y' #  zs')) m ns\<close> and
      vmtf_ns_x_y: \<open>vmtf_ns ((xs' @ [x']) @ [x, y'] @ zs') m ns\<close>
      using vmtf_ns unfolding l xs zs by simp_all
    have [simp]: \<open>y' < length ns\<close> \<open>x < length ns\<close> \<open>x \<noteq> y'\<close> \<open>x' \<noteq> y'\<close> \<open>x' < length ns\<close> \<open>y' \<noteq> x'\<close>
      \<open>y' \<noteq> x\<close> \<open>y' \<notin> set xs\<close>  \<open>y' \<notin> set zs'\<close>
      and x_zs': \<open>x \<notin> set zs'\<close> and x'_zs': \<open>x' \<notin> set zs'\<close> and y'_xs': \<open>y' \<notin> set xs'\<close>
      using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] unfolding l xs zs
      by auto
    have \<open>get_next (ns!x) = Some y'\<close> \<open>get_prev (ns!x) = Some x'\<close>
      using vmtf_ns_last_mid_get_prev[OF vmtf_ns_x'_x] vmtf_ns_last_mid_get_next[OF vmtf_ns_x_y]
      by fast+
    then show ?thesis
      using notin x_zs' x'_zs' y'_xs' unfolding l xs zs
      by (auto simp: vmtf_ns_notin_def ns_vmtf_dequeue_def)
  qed
qed

lemma vmtf_ns_stamp_distinct:
  assumes \<open>vmtf_ns l m ns\<close>
  shows \<open>distinct (map (\<lambda>a. stamp (ns!a)) l)\<close>
  using assms
proof (induction rule: vmtf_ns.induct)
  case (Cons b l m xs a n xs' n') note vmtf_ns = this(1) and IH = this(9) and a_le_y = this(2) and
    zs_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8)
  have [simp]: \<open>map (\<lambda>aa. stamp
                 (if b = aa
                  then VMTF_Node (stamp (xs ! aa)) (Some a) (get_next (xs ! aa))
                  else xs ! aa)) l =
        map (\<lambda>aa. stamp (xs ! aa)) l
       \<close> for a
    apply (rule map_cong)
    subgoal ..
    subgoal using vmtf_ns_distinct[OF vmtf_ns] by auto
    done
  show ?case
    using Cons vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns]
    by (auto simp: sorted_many_eq_append leD vmtf_ns_stamp_sorted cong: if_cong)
qed auto

lemma vmtf_ns_thighten_stamp:
  assumes vmtf_ns: \<open>vmtf_ns l m xs\<close> and n: \<open>\<forall>a\<in>set l. stamp (xs ! a) \<le> n\<close>
  shows \<open>vmtf_ns l n xs\<close>
proof -
  consider
    (empty) \<open>l = []\<close> |
    (single) x where \<open>l = [x]\<close> |
    (more_than_two) x y ys where \<open>l = x # y # ys\<close>
    by (cases l; cases \<open>tl l\<close>) auto
  then show ?thesis
  proof cases
    case empty
    then show ?thesis by (auto intro: vmtf_ns.intros)
  next
    case (single x)
    then show ?thesis using n vmtf_ns by (auto simp: vmtf_ns_single_iff)
  next
    case (more_than_two x y ys) note l = this
    then have vmtf_ns': \<open>vmtf_ns ([] @ [x, y] @ ys) m xs\<close>
      using vmtf_ns by auto
    from vmtf_ns_append_decomp[OF this] have
      \<open>vmtf_ns ([x]) m (xs[x := VMTF_Node (stamp (xs ! x)) (get_prev (xs ! x)) None])\<close> and
      vmtf_ns_y_ys: \<open>vmtf_ns (y # ys) (stamp (xs ! y))
        (xs[y := VMTF_Node (stamp (xs ! y)) None (get_next (xs ! y))])\<close> and
      \<open>stamp (xs ! y) < stamp (xs ! x)\<close>
      by auto
    have [simp]: \<open>x \<noteq> y\<close> \<open>x \<notin> set ys\<close> \<open>x < length xs\<close> \<open>y < length xs\<close>
      using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] unfolding l by auto
    show ?thesis
      unfolding l
      apply (rule vmtf_ns.Cons[OF vmtf_ns_y_ys, of _ \<open>stamp (xs ! x)\<close>])
      subgoal using vmtf_ns_le_length[OF vmtf_ns] unfolding l by auto
      subgoal using vmtf_ns unfolding l by (cases \<open>xs ! x\<close>) (auto elim: vmtf_nsE)
      subgoal by simp
      subgoal by simp
      subgoal using vmtf_ns_stamp_sorted[OF vmtf_ns] vmtf_ns_stamp_distinct[OF vmtf_ns]
       by (auto simp: l sorted_many_eq_append)
      subgoal
        using vmtf_ns vmtf_ns_last_mid_get_prev[OF vmtf_ns']
        apply (cases \<open>xs ! y\<close>)
        by simp (auto simp: l eq_commute[of \<open>xs ! y\<close>])
      subgoal using n unfolding l by auto
      done
  qed
qed

lemma vmtf_ns_rescale:
  assumes
    \<open>vmtf_ns l m xs\<close> and
    \<open>sorted (map (\<lambda>a. st ! a) (rev l))\<close> and \<open>distinct (map (\<lambda>a. st ! a) l)\<close>
    \<open>\<forall>a \<in> set l. get_prev (zs ! a) = get_prev (xs ! a)\<close> and
    \<open>\<forall>a \<in> set l. get_next (zs ! a) = get_next (xs ! a)\<close> and
    \<open>\<forall>a \<in> set l. stamp (zs ! a) = st ! a\<close> and
    \<open>length xs \<le> length zs\<close> and
    \<open>\<forall>a\<in>set l. a < length st\<close>
  shows \<open>vmtf_ns l (Max (set st)) zs\<close>
  using assms
proof (induction arbitrary: zs rule: vmtf_ns.induct)
  case (Nil st xs)
  then show ?case by (auto intro: vmtf_ns.intros)
next
  case (Cons1 a xs m n)
  then show ?case by (cases \<open>zs ! a\<close>) (auto simp: vmtf_ns_single_iff intro!: Max_ge nth_mem)
next
  case (Cons b l m xs a n xs' n' zs) note vmtf_ns = this(1) and a_le_y = this(2) and
    zs_a = this(3) and ab = this(4) and a_l = this(5) and mn = this(6) and xs' = this(7) and
    nn' = this(8) and IH = this(9) and H = this(10-)
  have [simp]: \<open>b < length xs\<close> \<open>b \<noteq> a\<close> \<open>a \<noteq> b\<close> \<open>b \<notin> set l\<close> \<open>b < length zs\<close> \<open>a < length zs\<close>
    using vmtf_ns_distinct[OF vmtf_ns] vmtf_ns_le_length[OF vmtf_ns] ab H(6) a_le_y unfolding xs'
    by force+

  have simp_is_stupid[simp]: \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> a \<noteq> x\<close> \<open>a \<in> set l \<Longrightarrow> x \<notin> set l \<Longrightarrow> x \<noteq> a\<close>  for a x
    by auto
  define zs' where \<open>zs' \<equiv> (zs[b := VMTF_Node (st ! b) (get_prev (xs ! b)) (get_next (xs ! b)),
          a := VMTF_Node (st ! a) None (Some b)])\<close>
  have zs_upd_zs: \<open>zs = zs
    [b := VMTF_Node (st ! b) (get_prev (xs ! b)) (get_next (xs ! b)),
     a := VMTF_Node (st ! a) None (Some b),
     b := VMTF_Node (st ! b) (Some a) (get_next (xs ! b))]
    \<close>
    using H(2-5) xs' zs_a \<open>b < length xs\<close>
    by (metis list.set_intros(1) list.set_intros(2) list_update_id list_update_overwrite
      nth_list_update_eq nth_list_update_neq vmtf_node.collapse vmtf_node.sel(2,3))

  have vtmf_b_l: \<open>vmtf_ns (b # l) (Max (set st)) zs'\<close>
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
  then have \<open>vmtf_ns (b # l) (stamp (zs' ! b)) zs'\<close>
    by (rule vmtf_ns_thighten_stamp)
      (use vmtf_ns_stamp_sorted[OF vtmf_b_l] in \<open>auto simp: sorted_append\<close>)

  then show ?case
    apply (rule vmtf_ns.Cons[of _ _ _ _ _ \<open>st ! a\<close>])
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

lemma vmtf_ns_last_prev:
  assumes vmtf: \<open>vmtf_ns (xs @ [x]) m ns\<close>
  shows \<open>get_prev (ns ! x) = option_last xs\<close>
proof (cases xs rule: rev_cases)
  case Nil
  then show ?thesis using vmtf by (cases \<open>ns!x\<close>) (auto simp: vmtf_ns_single_iff)
next
  case (snoc xs' y')
  then show ?thesis
    using vmtf_ns_last_mid_get_prev[of xs' y' x \<open>[]\<close> m ns] vmtf by auto
qed


context isasat_input_bounded_nempty
begin

paragraph \<open>Abstract Invariants\<close>

text \<open>
  Invariants
  \<^item> The atoms of \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close> are always disjoint.
  \<^item> The atoms of \<^term>\<open>ys\<close> are \<^emph>\<open>always\<close> set.
  \<^item> The atoms of \<^term>\<open>xs\<close> \<^emph>\<open>can\<close> be set but do not have to.
  \<^item> The atoms of \<^term>\<open>zs\<close> are either in \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close>.
\<close>

definition (in isasat_input_ops) vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf_ns_remove \<Rightarrow> bool\<close> where
\<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M \<equiv> \<lambda>((xs, ys), zs).
  (\<forall>L\<in>ys. L \<in> atm_of ` lits_of_l M) \<and>
  xs \<inter> ys = {} \<and>
  zs \<subseteq> xs \<union> ys \<and>
  xs \<union> ys = atms_of \<L>\<^sub>a\<^sub>l\<^sub>l
  \<close>

abbreviation abs_vmtf_ns_inv :: \<open>(nat, nat) ann_lits \<Rightarrow> nat abs_vmtf_ns \<Rightarrow> bool\<close> where
\<open>abs_vmtf_ns_inv M vm \<equiv> vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M (vm, {})\<close>


subsubsection \<open>Implementation\<close>

type_synonym (in -) vmtf = \<open>nat_vmtf_node list \<times> nat \<times> nat \<times> nat \<times> nat option\<close>
type_synonym (in -) vmtf_remove_int = \<open>vmtf \<times> nat list\<close>

text \<open>
  We use the opposite direction of the VMTF paper: The latest added element \<^term>\<open>fst_As\<close> is at
  the beginning.
\<close>

definition (in isasat_input_ops) vmtf :: \<open>(nat, nat) ann_lits \<Rightarrow> vmtf_remove_int set\<close> where
\<open>vmtf M = {((ns, m, fst_As, lst_As, next_search), to_remove).
   (\<exists>xs' ys'.
     vmtf_ns (ys' @ xs') m ns \<and> fst_As = hd (ys' @ xs') \<and> lst_As = last (ys' @ xs')
   \<and> next_search = option_hd xs'
   \<and> vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove) \<and> vmtf_ns_notin (ys' @ xs') m ns
   \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns) \<and> (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)
  )}\<close>

lemma (in isasat_input_ops) vmtf_consD:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf M\<close>
  shows \<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf (L # M)\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (L # M) ((set xs', set ys'), set remove)\<close>
    using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  ultimately have \<open>vmtf_ns (ys' @ xs') m ns \<and>
       fst_As = hd (ys' @ xs') \<and>
       lst_As = last (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (L # M) ((set xs', set ys'), set remove) \<and>
       vmtf_ns_notin (ys' @ xs') m ns \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
      by fast
  then show ?thesis
    unfolding vmtf_def by fast
qed

type_synonym (in -) vmtf_option_fst_As = \<open>nat_vmtf_node list \<times> nat \<times> nat option \<times> nat option \<times> nat option\<close>

definition (in -) vmtf_dequeue :: \<open>nat \<Rightarrow> vmtf \<Rightarrow> vmtf_option_fst_As\<close> where
\<open>vmtf_dequeue \<equiv> (\<lambda>L (ns, m, fst_As, lst_As, next_search).
  (let fst_As' = (if fst_As = L then get_next (ns ! L) else Some fst_As);
       next_search' = if next_search = Some L then get_next (ns ! L) else next_search;
       lst_As' = if lst_As = L then get_prev (ns ! L) else Some lst_As in
   (ns_vmtf_dequeue L ns, m, fst_As', lst_As', next_search')))\<close>

text \<open>It would be better to distinguish whether L is set in M or not.\<close>
definition (in -) vmtf_enqueue :: \<open>nat \<Rightarrow> vmtf_option_fst_As \<Rightarrow>  vmtf\<close> where
\<open>vmtf_enqueue = (\<lambda>L (ns, m, fst_As, lst_As, next_search).
  (case fst_As of
    None \<Rightarrow> (ns[L := VMTF_Node m fst_As None], m+1, L, L, Some L)
  | Some fst_As \<Rightarrow>
     let fst_As' = VMTF_Node (stamp (ns!fst_As)) (Some L) (get_next (ns!fst_As)) in
      (ns[L := VMTF_Node (m+1) None (Some fst_As), fst_As := fst_As'],
          m+1, L, the lst_As, Some L)))\<close>

definition (in -) vmtf_en_dequeue :: \<open>nat \<Rightarrow> vmtf \<Rightarrow>  vmtf\<close> where
\<open>vmtf_en_dequeue = (\<lambda>L vm. vmtf_enqueue L (vmtf_dequeue L vm))\<close>

lemma abs_vmtf_ns_bump_vmtf_dequeue:
  fixes M
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close>  and
    L: \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    dequeue: \<open>(ns', m', fst_As', lst_As', next_search') = vmtf_dequeue L (ns, m, fst_As, lst_As, next_search)\<close>
  shows \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m' ns' \<and> fst_As' = option_hd (ys' @ xs')
   \<and> lst_As' = option_last (ys' @ xs')
   \<and> next_search' = option_hd xs' \<and> vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((insert L (set xs'), set ys'), set to_remove)
   \<and> vmtf_ns_notin (ys' @ xs') m' ns' \<and>
   L \<notin> set (ys' @ xs') \<and> (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
  unfolding vmtf_def
proof -
  have ns': \<open>ns' = ns_vmtf_dequeue L ns\<close> and
    fst_As': \<open>fst_As' = (if fst_As = L then get_next (ns ! L) else Some fst_As)\<close> and
    lst_As': \<open>lst_As' = (if lst_As = L then get_prev (ns ! L) else Some lst_As)\<close> and
    m'm: \<open>m' = m\<close>
    using dequeue unfolding vmtf_dequeue_def by auto
  obtain xs ys where
    vmtf: \<open>vmtf_ns (ys @ xs) m ns\<close> and
    notin: \<open>vmtf_ns_notin (ys @ xs) m ns\<close> and
    next_search: \<open>next_search = option_hd xs\<close> and
    abs_inv: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs, set ys), set to_remove)\<close> and
    fst_As: \<open>fst_As = hd (ys @ xs)\<close> and
    lst_As: \<open>lst_As = last (ys @ xs)\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    L_ys_xs: \<open>\<forall>L\<in>set (ys @ xs). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by auto
  have [dest]: \<open>xs = [] \<Longrightarrow> ys = [] \<Longrightarrow> False\<close>
    using abs_inv \<A>\<^sub>i\<^sub>n_nempty unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by auto
  let ?ys = \<open>ys\<close>
  let ?xs = \<open>xs\<close>
  have dist: \<open>distinct (xs @ ys)\<close>
    using vmtf_ns_distinct[OF vmtf] by auto
  have xs_ys: \<open>remove1 L ys @ remove1 L xs = remove1 L (ys @ xs)\<close>
    using dist by (auto simp: remove1_append remove1_idem disjoint_iff_not_equal
        intro!: remove1_idem)
  have atm_L_A: \<open>L < length ns\<close>
    using atm_A L by blast

  have \<open>vmtf_ns (remove1 L ys @ remove1 L xs) m' ns'\<close>
    using vmtf_ns_ns_vmtf_dequeue[OF vmtf notin, of L] dequeue dist atm_L_A
    unfolding vmtf_dequeue_def by (auto split: if_splits simp: xs_ys)
  moreover have next_search': \<open>next_search' = option_hd (remove1 L xs)\<close>
  proof -
    have \<open>[hd xs, hd (tl xs)] @ tl (tl xs) = xs\<close>
      if \<open>xs \<noteq> []\<close> \<open>tl xs \<noteq> []\<close>
      apply (cases xs; cases \<open>tl xs\<close>)
       using that by (auto simp: tl_append split: list.splits)
    then have [simp]: \<open>get_next (ns ! hd xs) = option_hd (remove1 (hd xs) xs)\<close> if \<open>xs \<noteq> []\<close>
      using vmtf_ns_last_mid_get_next[of \<open>?ys\<close> \<open>hd ?xs\<close>
          \<open>hd (tl ?xs)\<close> \<open>tl (tl ?xs)\<close> m ns] vmtf vmtf_ns_distinct[OF vmtf] that
        distinct_remove1_last_butlast[of xs]
      by (cases xs; cases \<open>tl xs\<close>)
        (auto simp: tl_append vmtf_ns_last_next split: list.splits elim: vmtf_nsE)
    have \<open>xs \<noteq> [] \<Longrightarrow> xs \<noteq> [L] \<Longrightarrow>  L \<noteq> hd xs \<Longrightarrow> hd xs = hd (remove1 L xs)\<close>
      by (induction xs) (auto simp: remove1_Nil_iff)
    then have [simp]: \<open>option_hd xs = option_hd (remove1 L xs)\<close> if \<open>L \<noteq> hd xs\<close>
      using that vmtf_ns_distinct[OF vmtf]
      by (auto simp: option_hd_def remove1_Nil_iff)
    show ?thesis
      using dequeue dist atm_L_A next_search next_search unfolding vmtf_dequeue_def
      by (auto split: if_splits simp: xs_ys dest: last_in_set)
    qed
  moreover {
    have \<open>[hd ys, hd (tl ys)] @ tl (tl ys) = ys\<close>
      if \<open>ys \<noteq> []\<close> \<open>tl ys \<noteq> []\<close>
       using that by (auto simp: tl_append split: list.splits)
    then have \<open>get_next (ns ! hd (ys @ xs)) = option_hd (remove1 (hd (ys @ xs)) (ys @ xs))\<close>
      if \<open>ys @ xs \<noteq> []\<close>
      using vmtf_ns_last_next[of \<open>?xs @ butlast ?ys\<close> \<open>last ?ys\<close>] that
      using vmtf_ns_last_next[of \<open>butlast ?xs\<close> \<open>last ?xs\<close>]  vmtf dist
        distinct_remove1_last_butlast[of \<open>?ys @ ?xs\<close>]
      by (cases ys; cases \<open>tl ys\<close>)
       (auto simp: tl_append vmtf_ns_last_prev remove1_append hd_append remove1_Nil_iff
          split: list.splits if_splits elim: vmtf_nsE)
    moreover have \<open>hd ys \<notin> set xs\<close> if \<open>ys \<noteq> []\<close>
      using vmtf_ns_distinct[OF vmtf] that by (cases ys) auto
    ultimately have \<open>fst_As' = option_hd (remove1 L (ys @ xs))\<close>
      using dequeue dist atm_L_A fst_As vmtf_ns_distinct[OF vmtf] vmtf
      unfolding vmtf_dequeue_def
      apply (cases ys)
      subgoal by (cases xs) (auto simp: remove1_append option_hd_def remove1_Nil_iff split: if_splits)
      subgoal by (auto simp: remove1_append option_hd_def remove1_Nil_iff)
      done
  }
  moreover have \<open>lst_As' = option_last (remove1 L (ys @ xs))\<close>
    apply (cases \<open>ys @ xs\<close> rule: rev_cases)
    using lst_As vmtf_ns_distinct[OF vmtf] vmtf_ns_last_prev vmtf
    by (auto simp: lst_As' remove1_append simp del: distinct_append) auto
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((insert L (set (remove1 L xs)), set (remove1 L ys)),
    set to_remove)\<close>
    using abs_inv L dist
    unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto dest: in_set_remove1D)
  moreover have \<open>vmtf_ns_notin (remove1 L ?ys @ remove1 L ?xs) m' ns'\<close>
    unfolding xs_ys ns'
    apply (rule vmtf_ns_notin_dequeue)
    subgoal using vmtf unfolding m'm .
    subgoal using notin unfolding m'm .
    subgoal using atm_L_A .
    done
  moreover have \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns'\<close>
    using atm_A unfolding ns' by auto
  moreover have \<open>L \<notin> set (remove1 L ys @ remove1 L xs)\<close>
    using dist by auto
  moreover have \<open>\<forall>L\<in>set (remove1 L (ys @ xs)). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using L_ys_xs by (auto dest: in_set_remove1D)
  ultimately show ?thesis
    apply -
    apply (rule exI[of _ \<open>remove1 L xs\<close>])
    apply (rule exI[of _ \<open>remove1 L ys\<close>])
    unfolding xs_ys
    by blast
qed

lemma vmtf_ns_get_prev_not_itself:
  \<open>vmtf_ns xs m ns \<Longrightarrow> L \<in> set xs \<Longrightarrow> L < length ns \<Longrightarrow> get_prev (ns ! L) \<noteq> Some L\<close>
  apply (induction rule: vmtf_ns.induct)
  subgoal by auto
  subgoal by (auto simp: vmtf_ns_single_iff)
  subgoal by auto
  done

lemma vmtf_ns_get_next_not_itself:
  \<open>vmtf_ns xs m ns \<Longrightarrow> L \<in> set xs \<Longrightarrow> L < length ns \<Longrightarrow> get_next (ns ! L) \<noteq> Some L\<close>
  apply (induction rule: vmtf_ns.induct)
  subgoal by auto
  subgoal by (auto simp: vmtf_ns_single_iff)
  subgoal by auto
  done

lemma abs_vmtf_ns_bump_vmtf_en_dequeue:
  fixes M
  assumes
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close> and
    L: \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    to_remove: \<open>mset to_remove' \<subseteq># remove1_mset L (mset to_remove)\<close>
  shows \<open>(vmtf_en_dequeue L (ns, m, fst_As, lst_As, next_search), to_remove') \<in> vmtf M\<close>
  unfolding vmtf_def
proof clarify
  fix xxs yys zzs ns' m' fst_As' lst_As' next_search'
  assume dequeue: \<open>(ns', m', fst_As', lst_As', next_search') = vmtf_en_dequeue L (ns, m, fst_As, lst_As, next_search)\<close>
  obtain xs ys where
    vmtf_ns: \<open>vmtf_ns (ys @ xs) m ns\<close> and
    notin: \<open>vmtf_ns_notin (ys @ xs) m ns\<close> and
    next_search: \<open>next_search = option_hd xs\<close> and
    abs_inv: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs, set ys), set to_remove)\<close> and
    fst_As: \<open>fst_As = hd (ys @ xs)\<close> and
    lst_As: \<open>lst_As = last (ys @ xs)\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys @ xs). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using assms unfolding vmtf_def by auto
  have atm_L_A: \<open>L < length ns\<close>
    using atm_A L by blast
  text \<open>d stands for dequeue\<close>
  obtain nsd md fst_Asd lst_Asd next_searchd where
    de: \<open>vmtf_dequeue L (ns, m, fst_As, lst_As, next_search) = (nsd, md, fst_Asd, lst_Asd, next_searchd) \<close>
    by (cases \<open>vmtf_dequeue L (ns, m, fst_As, lst_As, next_search)\<close>)
  obtain xs' ys' where
    vmtf_ns': \<open>vmtf_ns (ys' @ xs') md nsd\<close> and
    fst_Asd: \<open>fst_Asd = option_hd (ys' @ xs')\<close> and
    lst_Asd: \<open>lst_Asd = option_last (ys' @ xs')\<close> and
    \<open>next_searchd = option_hd xs'\<close> and
    abs_l: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((insert L (set xs'), set ys'), set to_remove)\<close>  and
    not_in: \<open>vmtf_ns_notin (ys' @ xs') md nsd\<close> and
    L_xs'_ys': \<open>L \<notin> set (ys' @ xs')\<close> and
    L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using abs_vmtf_ns_bump_vmtf_dequeue[OF vmtf L de[symmetric]] by blast

  have fst_As': \<open>fst_As' = L\<close> and m': \<open>m' = md + 1\<close> and next_search': \<open>next_search' = Some L\<close> and
    lst_As': \<open>fst_Asd \<noteq> None \<longrightarrow> lst_As' = the (lst_Asd)\<close>
      \<open>fst_Asd = None \<longrightarrow> lst_As' = L\<close>
    using dequeue unfolding vmtf_en_dequeue_def comp_def de
    by (auto simp add: vmtf_enqueue_def split: option.splits)
  have abs': \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set (L # ys' @ xs'), set []), set to_remove')\<close>
    using abs_l to_remove unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto 5 5 dest: in_diffD)
  have [simp]: \<open>length ns' = length ns\<close>  \<open>length nsd = length ns\<close>
    using dequeue de unfolding vmtf_en_dequeue_def comp_def vmtf_dequeue_def
    by (auto simp add: vmtf_enqueue_def split: option.splits)
  have nsd: \<open>nsd = ns_vmtf_dequeue L ns\<close>
    using de unfolding vmtf_dequeue_def by auto
  have [simp]: \<open>fst_As = L\<close> if \<open>ys' = []\<close> and \<open>xs' = []\<close>
  proof -
    have 1: \<open>set_mset \<A>\<^sub>i\<^sub>n = {L}\<close>
      using abs_l unfolding that vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    show ?thesis
      using vmtf_ns_distinct[OF vmtf_ns] ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l abs_inv vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n 1 fst_As
      by (cases \<open>ys @ xs\<close>)  auto
  qed
  have \<open>lst_As = L\<close> if \<open>ys' = []\<close> and \<open>xs' = []\<close>
  proof -
    have 1: \<open>set_mset \<A>\<^sub>i\<^sub>n = {L}\<close>
      using abs_l unfolding that vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    then have \<open>set (ys @ xs) = {L} \<close>
      using vmtf_ns_distinct[OF vmtf_ns] ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l abs_inv vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n 1 fst_As
      by auto
    then have \<open>ys @ xs = [L]\<close>
      using vmtf_ns_distinct[OF vmtf_ns] ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l abs_inv vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n 1 fst_As
      by (cases \<open>ys @ xs\<close> rule: rev_cases) (auto simp del: set_append distinct_append
          simp: set_append[symmetric], auto)
    then show ?thesis
      using vmtf_ns_distinct[OF vmtf_ns] ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l abs_inv vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n 1 lst_As
      by (auto simp del: set_append distinct_append simp: set_append[symmetric])
  qed
  then have [simp]: \<open>lst_As' = L\<close>  if \<open>ys' = []\<close> and \<open>xs' = []\<close>
    using lst_As' fst_Asd unfolding that by auto
  have [simp]: \<open>lst_As' = last (ys' @ xs')\<close>  if \<open>ys' \<noteq> [] \<or> xs' \<noteq> []\<close>
    using lst_As' fst_Asd that lst_Asd by auto

  have \<open>get_prev (nsd ! i) \<noteq> Some L\<close>  (is ?prev) and
    \<open>get_next (nsd ! i) \<noteq> Some L\<close> (is ?next)
    if
     i_le_A: \<open>i < length ns\<close> and
     i_L: \<open>i \<noteq> L\<close> and
     i_ys': \<open>i \<notin> set ys'\<close> and
     i_xs': \<open>i \<notin> set xs'\<close>
     for i
  proof -
    have \<open>i \<notin> set xs\<close> \<open>i \<notin> set ys\<close> and L_xs_ys: \<open>L \<in> set xs \<or> L \<in> set ys\<close>
      using i_ys' i_xs' abs_l abs_inv i_L unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by auto
    then have
      \<open>get_next (ns ! i) = None\<close>
      \<open>get_prev (ns ! i) = None\<close>
      using notin i_le_A unfolding nsd vmtf_ns_notin_def ns_vmtf_dequeue_def
      by (auto simp: Let_def split: option.splits)
    moreover have \<open>get_prev (ns ! L) \<noteq> Some L\<close> and \<open>get_next (ns ! L) \<noteq> Some L\<close>
      using vmtf_ns_get_prev_not_itself[OF vmtf_ns, of L] L_xs_ys atm_L_A
      vmtf_ns_get_next_not_itself[OF vmtf_ns, of L] by auto
    ultimately show ?next and ?prev
      using i_le_A L_xs_ys unfolding nsd ns_vmtf_dequeue_def vmtf_ns_notin_def
      by (auto simp: Let_def split: option.splits)
  qed
  then have vmtf_ns_notin': \<open>vmtf_ns_notin (L # ys' @ xs') m' ns'\<close>
    using not_in dequeue fst_Asd unfolding vmtf_en_dequeue_def comp_def de vmtf_ns_notin_def
      ns_vmtf_dequeue_def
    by (auto simp add: vmtf_enqueue_def hd_append split: option.splits if_splits)
  have vmtf_ns: \<open>vmtf_ns (L # (ys' @ xs')) m' ns'\<close>
  proof (cases \<open>ys' @ xs'\<close>)
    case Nil
    then have \<open>fst_Asd = None\<close>
      using fst_Asd by auto
    then show ?thesis
      using atm_L_A dequeue Nil unfolding Nil vmtf_en_dequeue_def comp_def de nsd
      by (auto simp: vmtf_ns_single_iff vmtf_enqueue_def split: option.splits)
  next
    case (Cons z zs)
    let ?m = \<open>(stamp (nsd!z))\<close>
    let ?Ad = \<open>nsd[L := VMTF_Node m' None (Some z)]\<close>
    have L_z_zs: \<open>L \<notin> set (z # zs)\<close>
      using L_xs'_ys' atm_L_A unfolding Cons
      by simp
    have vmtf_ns_z: \<open>vmtf_ns (z # zs) md nsd\<close>
      using vmtf_ns' unfolding Cons .

    have vmtf_ns_A: \<open>vmtf_ns (z # zs) md ?Ad\<close>
      apply (rule vmtf_ns_eq_iffI[of _ _ nsd])
      subgoal using L_z_zs atm_L_A by auto
      subgoal using vmtf_ns_le_length[OF vmtf_ns_z] by auto
      subgoal using vmtf_ns_z .
      done
    have [simp]: \<open>fst_Asd = Some z\<close>
      using fst_Asd unfolding Cons by simp
    show ?thesis
      unfolding Cons
      apply (rule vmtf_ns.Cons[of _ _ md ?Ad _ m'])
      subgoal using vmtf_ns_A .
      subgoal using atm_L_A by simp
      subgoal using atm_L_A by simp
      subgoal using L_z_zs by simp
      subgoal using L_z_zs by simp
      subgoal using m' by simp_all
      subgoal
        using atm_L_A dequeue L_z_zs unfolding Nil vmtf_en_dequeue_def comp_def de nsd
        apply (cases \<open>ns_vmtf_dequeue z ns ! z\<close>)
        by (auto simp: vmtf_ns_single_iff vmtf_enqueue_def split: option.splits)
        subgoal by linarith
      done
  qed
  have L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l': \<open>\<forall>L'\<in>set ([] @ L # ys' @ xs'). L' \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using L L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
  show \<open>\<exists>xs' ys'.
       vmtf_ns (ys' @ xs') m' ns' \<and>
       fst_As' = hd (ys' @ xs') \<and>
       lst_As' = last (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove') \<and>
       vmtf_ns_notin (ys' @ xs') m' ns' \<and>
       (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    apply (rule exI[of _ \<open>L # ys' @ xs'\<close>])
    apply (rule exI[of _ \<open>[]\<close>])
    using fst_As' next_search' abs' atm_A vmtf_ns_notin' vmtf_ns ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l'
    by simp
qed

definition (in -) vmtf_unset :: \<open>nat \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int\<close> where
\<open>vmtf_unset = (\<lambda>L ((ns, m, fst_As, lst_As, next_search), to_remove).
  (if next_search = None \<or> stamp (ns ! (the next_search)) < stamp (ns ! L)
  then ((ns, m, fst_As, lst_As, Some L), to_remove)
  else ((ns, m, fst_As, lst_As, next_search), to_remove)))\<close>

lemma vmtf_atm_of_ys_iff:
  assumes
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    L: \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>L \<in> set ys' \<longleftrightarrow> next_search = None \<or> stamp (ns ! (the next_search)) < stamp (ns ! L)\<close>
proof -
  let ?xs' = \<open>set xs'\<close>
  let ?ys' = \<open>set ys'\<close>
  have L_xs_ys: \<open>L \<in> ?xs' \<union> ?ys'\<close>
    using abs_vmtf L unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have dist: \<open>distinct (xs' @ ys')\<close>
    using vmtf_ns_distinct[OF vmtf_ns] by auto

  have sorted: \<open>sorted (map (\<lambda>a. stamp (ns ! a)) (rev xs' @ rev ys'))\<close> and
    distinct: \<open>distinct (map (\<lambda>a. stamp (ns ! a)) (xs' @ ys'))\<close>
    using vmtf_ns_stamp_sorted[OF vmtf_ns] vmtf_ns_stamp_distinct[OF vmtf_ns]
    by (auto simp: rev_map[symmetric])
  have next_search_xs: \<open>?xs' = {} \<longleftrightarrow> next_search = None\<close>
    using next_search by auto

  have \<open>stamp (ns ! (the next_search)) < stamp (ns ! L) \<Longrightarrow> L \<notin> ?xs'\<close>
    if \<open>xs' \<noteq> []\<close>
    using that sorted distinct L_xs_ys unfolding next_search
    by (cases xs') (auto simp: sorted_append)
  moreover have \<open>stamp (ns ! (the next_search)) < stamp (ns ! L)\<close> (is \<open>?n < ?L\<close>)
    if xs': \<open>xs' \<noteq> []\<close> and \<open>L \<in> ?ys'\<close>
  proof -
    have \<open>?n \<le> ?L\<close>
      using vmtf_ns_stamp_sorted[OF vmtf_ns] that last_in_set[OF xs']
      by (cases xs')
         (auto simp: rev_map[symmetric] next_search sorted_append sorted2)
    moreover have \<open>?n \<noteq> ?L\<close>
      using vmtf_ns_stamp_distinct[OF vmtf_ns] that last_in_set[OF xs']
      by (cases xs') (auto simp: rev_map[symmetric] next_search)
    ultimately show ?thesis
      by arith
  qed
  ultimately show ?thesis
    using H L_xs_ys next_search_xs dist by auto
qed

lemma vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_to_remove_mono:
  assumes
    \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((a, b), to_remove)\<close> and
    \<open>to_remove' \<subseteq> to_remove\<close>
  shows \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((a, b), to_remove')\<close>
  using assms unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: mset_subset_eqD)

lemma abs_vmtf_ns_unset_vmtf_unset:
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close> and L_N: \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    to_remove: \<open>mset to_remove' \<subseteq># mset to_remove\<close>
  shows \<open>(vmtf_unset L ((ns, m, fst_As, lst_As, next_search), to_remove')) \<in> vmtf M\<close> (is \<open>?S \<in> _\<close>)
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  obtain ns' m' fst_As' next_search' to_remove'' lst_As' where
    S: \<open>?S = ((ns', m', fst_As', lst_As', next_search'), to_remove'')\<close>
    by (cases ?S) auto
  have L_ys'_iff: \<open>L \<in> set ys' \<longleftrightarrow> (next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L))\<close>
    using vmtf_atm_of_ys_iff[OF vmtf_ns next_search abs_vmtf L_N] .
  have \<open>L \<in> set (xs' @ ys')\<close>
    using abs_vmtf L_N unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  then have L_ys'_xs': \<open>L \<in> set ys' \<longleftrightarrow> L \<notin> set xs'\<close>
    using vmtf_ns_distinct[OF vmtf_ns] by auto
  have \<open>\<exists>xs' ys'.
       vmtf_ns (ys' @ xs') m' ns' \<and>
       fst_As' = hd (ys' @ xs') \<and>
       lst_As' = last (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove'') \<and>
       vmtf_ns_notin (ys' @ xs') m' ns' \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
  proof (cases \<open>L \<in> set xs'\<close>)
    case True
    then have C: \<open>\<not>(next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L))\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove'')\<close>
    apply (rule vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_to_remove_mono)
    apply (rule abs_vmtf)
    using to_remove S unfolding vmtf_unset_def by (auto simp: C)
    show ?thesis
      using S True unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      apply -
      apply (simp add: C)
      using vmtf_ns fst_As next_search abs_vmtf notin atm_A to_remove L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l lst_As
      by auto
  next
    case False
    then have C: \<open>next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L)\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have L_ys: \<open>L \<in> set ys'\<close>
      by (use False L_ys'_xs' in auto)
    define y_ys where \<open>y_ys \<equiv> takeWhile ((\<noteq>) L) ys'\<close>
    define x_ys where \<open>x_ys \<equiv> drop (length y_ys) ys'\<close>
    let ?ys' = \<open>y_ys\<close>
    let ?xs' = \<open>x_ys @ xs'\<close>
    have x_ys_take_ys': \<open>y_ys = take (length y_ys) ys'\<close>
        unfolding y_ys_def
        by (subst take_length_takeWhile_eq_takeWhile[of \<open>(\<noteq>) L\<close> \<open>ys'\<close>, symmetric]) standard
    have ys'_y_x: \<open>ys' = y_ys @ x_ys\<close>
      by (subst x_ys_take_ys') (auto simp: x_ys_def)
    have y_ys_le_ys': \<open>length y_ys < length ys'\<close>
      using L_ys by (metis (full_types) append_eq_conv_conj append_self_conv le_antisym
        length_takeWhile_le not_less takeWhile_eq_all_conv x_ys_take_ys' y_ys_def)
    from nth_length_takeWhile[OF this[unfolded y_ys_def]] have [simp]: \<open>x_ys \<noteq> []\<close> \<open>hd x_ys = L\<close>
      using y_ys_le_ys' unfolding x_ys_def y_ys_def
      by (auto simp: x_ys_def y_ys_def hd_drop_conv_nth)
    have [simp]: \<open>ns' = ns\<close> \<open>m' = m\<close> \<open>fst_As' = fst_As\<close> \<open>next_search' = Some L\<close> \<open>to_remove'' = to_remove'\<close>
      \<open>lst_As' = lst_As\<close>
      using S unfolding vmtf_unset_def by (auto simp: C)

    have \<open>vmtf_ns (?ys' @ ?xs') m ns\<close>
      using vmtf_ns unfolding ys'_y_x by simp
    moreover have \<open>fst_As' = hd (?ys' @ ?xs')\<close>
      using fst_As unfolding ys'_y_x by simp
    moreover have \<open>lst_As' = last (?ys' @ ?xs')\<close>
      using lst_As unfolding ys'_y_x by simp
    moreover have \<open>next_search' = option_hd ?xs'\<close>
      by auto
    moreover {
      have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set ?xs', set ?ys'), set to_remove)\<close>
        using abs_vmtf vmtf_ns_distinct[OF vmtf_ns] unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def ys'_y_x
        by auto
      then have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set ?xs', set ?ys'), set to_remove')\<close>
        by (rule vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_to_remove_mono) (use to_remove in auto)
      }
    moreover have \<open>vmtf_ns_notin (?ys' @ ?xs') m ns\<close>
      using notin unfolding ys'_y_x by simp
    moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding ys'_y_x by auto
    ultimately show ?thesis
      using S False atm_A unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      by (fastforce simp add: C)
  qed
  then show ?thesis
    unfolding vmtf_def S
    by fast
qed


definition (in -) vmtf_dequeue_pre where
  \<open>vmtf_dequeue_pre = (\<lambda>(L,ns). L < length ns \<and>
          (get_next (ns!L) \<noteq> None \<longrightarrow> the (get_next (ns!L)) < length ns) \<and>
          (get_prev (ns!L) \<noteq> None \<longrightarrow> the (get_prev (ns!L)) < length ns))\<close>

lemma (in -) vmtf_dequeue_pre_alt_def:
  \<open>vmtf_dequeue_pre = (\<lambda>(L, ns). L < length ns \<and>
          (\<forall>a. Some a = get_next (ns!L) \<longrightarrow> a < length ns) \<and>
          (\<forall>a. Some a = get_prev (ns!L) \<longrightarrow> a < length ns))\<close>
  apply (intro ext, rename_tac x)
  subgoal for x
    by (cases \<open>get_next ((snd x)!(fst x))\<close>; cases \<open>get_prev ((snd x)!(fst x))\<close>)
      (auto simp: vmtf_dequeue_pre_def intro!: ext)
  done

definition (in -) vmtf_en_dequeue_pre :: \<open>nat \<times> vmtf \<Rightarrow> bool\<close> where
  \<open>vmtf_en_dequeue_pre = (\<lambda>(L,(ns,m,fst_As, lst_As, next_search)). L < length ns \<and> vmtf_dequeue_pre (L, ns) \<and>
       fst_As < length ns \<and> (get_next (ns ! fst_As) \<noteq> None \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None) \<and>
       (get_next (ns ! fst_As) = None \<longrightarrow> fst_As = lst_As))\<close>

definition (in -) vmtf_flush :: \<open>vmtf_remove_int \<Rightarrow> vmtf_remove_int nres\<close> where
\<open>vmtf_flush \<equiv> (\<lambda>(vm, to_remove). do {
    to_remove' \<leftarrow> reorder_remove vm to_remove;
    (_, vm) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm). i \<le> length to_remove' \<and>
          (i < length to_remove' \<longrightarrow> vmtf_en_dequeue_pre (to_remove'!i, vm))\<^esup>
      (\<lambda>(i, vm). i < length to_remove')
      (\<lambda>(i, vm). do {
         ASSERT(i < length to_remove');
         RETURN (i+1, vmtf_en_dequeue (to_remove'!i) vm)})
      (0, vm);
    RETURN (vm, [])
  })\<close>

lemma (in -) id_reorder_remove:
   \<open>(RETURN o id, reorder_remove vm) \<in> \<langle>nat_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>nat_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding reorder_remove_def by (intro frefI nres_relI) auto

lemma vmtf_swap_to_remove:
  assumes
    vmtf: \<open>((ns, m, fst_As, next_search), to_remove) \<in> vmtf M\<close> and
    mset: \<open>mset to_remove = mset to_remove'\<close>
  shows \<open>((ns, m, fst_As, next_search), to_remove') \<in> vmtf M\<close>
  using assms unfolding vmtf_def by (fastforce dest: mset_eq_setD)

lemma vmtf_vmtf_en_dequeue_pre_to_remove:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close> and i: \<open>i < length to_remove\<close>
  shows \<open>vmtf_en_dequeue_pre (to_remove ! i, (ns, m, fst_As, lst_As, next_search))\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  have [dest]: False if \<open>ys' = []\<close> and \<open>xs' = []\<close>
  proof -
    have 1: \<open>set_mset \<A>\<^sub>i\<^sub>n = {}\<close>
      using abs_vmtf unfolding that vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    then show ?thesis
      using \<A>\<^sub>i\<^sub>n_nempty by auto
  qed

  have to_remove_i: \<open>to_remove ! i \<in> set to_remove\<close>
    using i by simp
  then have \<open>to_remove ! i \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  then have remove_i_le_A: \<open>to_remove ! i < length ns\<close>
    using atm_A by auto
  moreover have \<open>fst_As < length ns\<close>
    using fst_As atm_A L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l by (cases ys'; cases xs') auto
  moreover have \<open>get_prev (ns ! lst_As) \<noteq> None\<close> if \<open>get_next (ns ! fst_As) \<noteq> None\<close>
    using that vmtf_ns_hd_next[of \<open>hd (ys' @ xs')\<close> \<open>hd (tl (ys' @ xs'))\<close> \<open>tl (tl (ys' @ xs'))\<close>]
      vmtf_ns vmtf_ns_last_prev[of \<open>butlast (ys' @ xs')\<close> \<open>last (ys' @ xs')\<close>]
      vmtf_ns_last_next[of \<open>butlast (ys' @ xs')\<close> \<open>last (ys' @ xs')\<close>]
    by (cases \<open>ys' @ xs'\<close>; cases \<open>tl (ys' @ xs')\<close>)
       (auto simp: fst_As lst_As)
  moreover have \<open>vmtf_dequeue_pre (to_remove ! i, ns)\<close>
  proof -
    have \<open>to_remove ! i < length ns\<close>
      using to_remove_i abs_vmtf atm_A unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
    moreover have \<open>y < length ns\<close> if get_next: \<open>get_next (ns ! (to_remove ! i)) = Some y\<close> for y
    proof (cases \<open>to_remove ! i \<in> set (ys' @ xs')\<close>)
      case False
      then show ?thesis
        using notin get_next remove_i_le_A by (auto simp: vmtf_ns_notin_def)
    next
      case True
      then obtain zs zs' where zs: \<open>ys' @ xs' = zs' @ [to_remove ! i] @ zs\<close>
        using split_list by fastforce
      moreover have \<open>set (ys' @ xs') = atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
      ultimately show ?thesis
        using vmtf_ns_last_mid_get_next_option_hd[of zs' \<open>to_remove!i\<close> zs m ns] vmtf_ns atm_A get_next
          L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding zs by force
    qed
    moreover have \<open>y < length ns\<close> if get_prev: \<open>get_prev (ns ! (to_remove ! i)) = Some y\<close> for y
    proof (cases \<open>to_remove ! i \<in> set (ys' @ xs')\<close>)
      case False
      then show ?thesis
        using notin get_prev remove_i_le_A by (auto simp: vmtf_ns_notin_def)
    next
      case True
      then obtain zs zs' where zs: \<open>ys' @ xs' = zs' @ [to_remove ! i] @ zs\<close>
        using split_list by fastforce
      moreover have \<open>set (ys' @ xs') = atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
      ultimately show ?thesis
        using vmtf_ns_last_mid_get_prev_option_last[of zs' \<open>to_remove!i\<close> zs m ns] vmtf_ns atm_A get_prev
          L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding zs by force
    qed
    ultimately show ?thesis
      unfolding vmtf_dequeue_pre_def by auto
  qed
  moreover have \<open>get_next (ns ! fst_As) = None \<longrightarrow> fst_As = lst_As\<close>
    using vmtf_ns_hd_next[of \<open>hd (ys' @ xs')\<close> \<open>hd (tl (ys' @ xs'))\<close> \<open>tl (tl (ys' @ xs'))\<close>]
      vmtf_ns vmtf_ns_last_prev[of \<open>butlast (ys' @ xs')\<close> \<open>last (ys' @ xs')\<close>]
      vmtf_ns_last_next[of \<open>butlast (ys' @ xs')\<close> \<open>last (ys' @ xs')\<close>]
    by (cases \<open>ys' @ xs'\<close>; cases \<open>tl (ys' @ xs')\<close>)
       (auto simp: fst_As lst_As)
  ultimately show ?thesis
    unfolding vmtf_en_dequeue_pre_def by auto
qed

lemma vmtf_change_to_remove_order:
  assumes
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close> and
    mset: \<open>mset to_remove = mset to_remove'\<close>
  shows \<open>vmtf_flush ((ns, m, fst_As, lst_As, next_search), to_remove') \<le> \<Down> Id (RES (vmtf M))\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close>
    using vmtf unfolding vmtf_def by fast
  have \<open>set to_remove = set to_remove'\<close>
    using mset by (metis set_mset_mset)
  have H': \<open>(x2, drop j to_remove') \<in> vmtf M\<close> (is ?G1) and
    H'': \<open>to_remove' ! i \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> (is ?G2)
    if
      s: \<open>case s of (i, vm) \<Rightarrow> i \<le> length to_remove' \<and> (vm, drop i to_remove') \<in> vmtf M\<close> and
      i: \<open>case s of (i, vm) \<Rightarrow> i < length to_remove'\<close> and
      \<open>s = (i, vm')\<close> and
      i_le_rem: \<open>i < length to_remove'\<close> and
      \<open>(i + 1, vmtf_en_dequeue (to_remove' ! i) vm') = (j, x2)\<close> and
      mset_to_remove': \<open>mset to_remove = mset to_remove'\<close>
    for s i j x2 vm' to_remove'
  proof -
    have vmtf_ns: \<open>(vm', drop i to_remove') \<in> vmtf M\<close>
      using s that by auto
    have \<open>to_remove' ! i \<in> set to_remove'\<close>
      using i_le_rem by auto
    then have L: \<open>to_remove' ! i \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using vmtf mset set_mset_mset[of to_remove, unfolded mset_to_remove']
      unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by auto
    have mset: \<open>mset (drop (Suc i) to_remove') \<subseteq># remove1_mset (to_remove' ! i) (mset (drop i to_remove'))\<close>
      by (cases \<open>drop i to_remove'\<close>) (auto simp: drop_eq_ConsD nth_via_drop)
    have \<open>(vmtf_en_dequeue (to_remove' ! i) vm', drop (Suc i) to_remove') \<in> vmtf M\<close>
      apply (cases vm')
      using vmtf_ns L mset by (auto intro!: abs_vmtf_ns_bump_vmtf_en_dequeue)
    then show ?G1 ?G2
      using that L by auto
  qed
  have a: \<open>a < length to_remove' \<Longrightarrow> to_remove' ! a \<in> set (drop a to_remove')\<close> for a
    using in_set_drop_conv_nth by fastforce
  have to_remove_le: \<open>((aa, ab, ac, bc), drop a to_remove') \<in> vmtf M \<Longrightarrow> a < length to_remove' \<Longrightarrow> to_remove' ! a < length aa\<close>
    for a aa ab ac bc
    using a[of a] by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
  have vmtf_en_dequeue:  \<open>vmtf_en_dequeue_pre (to_remove'' ! x1, x2)\<close>
    if
       I: \<open>case s of (i, vm) \<Rightarrow> i \<le> length to_remove'' \<and>
           (i < length to_remove'' \<longrightarrow> vmtf_en_dequeue_pre (to_remove'' ! i, vm))\<close> and
       I': \<open>case s of (i, vm) \<Rightarrow> (vm, drop i to_remove'') \<in> vmtf M \<and> mset to_remove'' = mset to_remove'\<close> and
       \<open>case s of (i, vm) \<Rightarrow> i < length to_remove''\<close> and
       s: \<open>s = (a, vm')\<close> and
       le: \<open>a < length to_remove''\<close> and
       de: \<open>(a + 1, vmtf_en_dequeue (to_remove'' ! a) vm') = (x1, x2)\<close>
       \<open>x1 < length to_remove''\<close>
     for to_remove'' x1 x1a x1b a x2 and vm vm' :: \<open>nat_vmtf_node list \<times> nat \<times> nat \<times> nat \<times> nat option\<close> and s
  proof -
    have to_remove_i: \<open>to_remove'' ! a \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      apply (rule H'')
      using that mset by auto
    have m: \<open>mset (drop (Suc a) to_remove'') \<subseteq># remove1_mset (to_remove'' ! a) (mset (drop a to_remove''))\<close>
      by (metis Cons_nth_drop_Suc insert_subset_eq_iff mset.simps(2) subset_mset.order_refl that(5))
    have vmtf: \<open>(vmtf_en_dequeue (to_remove'' ! a) vm', drop (Suc a) to_remove'') \<in> vmtf M\<close>
      apply (cases vm')
      using s I' le to_remove_i m by (auto intro: abs_vmtf_ns_bump_vmtf_en_dequeue)
    have R: \<open>to_remove'' ! x1 = (drop (Suc a) to_remove'') ! 0\<close>
      using de I' by auto
    show ?thesis
      unfolding R
      apply (cases x2)
      apply clarify
      apply (rule vmtf_vmtf_en_dequeue_pre_to_remove[of _ _ _ _ _ _ M])
      using de vmtf s I' by (auto intro: vmtf_swap_to_remove)
  qed
  have H: \<open>do {
      WHILE\<^sub>T\<^bsup>\<lambda>(i, vm). i \<le> length to_remove'' \<and>
            (i < length to_remove'' \<longrightarrow> vmtf_en_dequeue_pre (to_remove'' ! i, vm))\<^esup>
        (\<lambda>(i, vm). i < length to_remove'')
        (\<lambda>(i, vm). do {
          ASSERT(i < length to_remove'');
          RETURN (i+1, vmtf_en_dequeue (to_remove''!i) vm)})
        (0, (ns, m, fst_As, lst_As, next_search))
    } \<le> (RES ({(length to_remove'', a)|a. (a, []) \<in> vmtf M}))\<close>
    if \<open>mset to_remove'' = mset to_remove'\<close>
    for to_remove''
  proof -
    have vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove'') \<in> vmtf M\<close>
        using vmtf mset that by (auto intro: vmtf_swap_to_remove)
    show ?thesis
      unfolding vmtf_flush_def
      apply (refine_vcg
         WHILEIT_rule_stronger_inv
            [where R = \<open>measure (\<lambda>(i, vm). Suc (length to_remove'') - i)\<close> and
             I' = \<open>\<lambda>(i, vm). (vm, drop i to_remove'') \<in> vmtf M \<and>
                mset to_remove'' = mset to_remove'\<close>])
      subgoal by auto
      subgoal using vmtf by auto
      subgoal using vmtf by (auto intro!: vmtf_vmtf_en_dequeue_pre_to_remove)
      subgoal using vmtf mset that by (auto intro: vmtf_swap_to_remove)
      subgoal using that by simp
      subgoal by (simp add: to_remove_le)
      subgoal by (auto simp: vmtf_en_dequeue_pre_def)
      subgoal by (rule vmtf_en_dequeue) assumption+
      subgoal
        apply (rule H'; assumption?)
        using mset by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
  qed
  have RES: \<open>RES (vmtf M) = do {
        to_remove' \<leftarrow> SPEC (\<lambda>to_remove''. mset to_remove'' = mset to_remove');
        a \<leftarrow> RES (vmtf M);
        RETURN a}\<close>
    by (subst unused_bind_RES_ne) auto
  have K: \<open>SPEC (\<lambda>uu. \<exists>a. uu = (length to_remove', a) \<and> (a, []) \<in> vmtf M) \<le>
      \<Down> {(a', a). snd a' = fst a \<and> fst a'= length to_remove' \<and> snd a = []} (RES (vmtf M))\<close>
    for to_remove'
    by (force intro!: RES_refine)
  show ?thesis
    unfolding vmtf_flush_def
    apply (subst RES)
    apply clarify
    apply (refine_rcg H[THEN order_trans] K)
    subgoal unfolding reorder_remove_def by auto
    subgoal using mset by auto
    subgoal for r r' a a' x1 x2
      by (cases a') auto
    done
qed

lemma wf_vmtf_get_next:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close>
  shows \<open>wf {(get_next (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l}\<close> (is \<open>wf ?R\<close>)
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain f where
    f: \<open>(f (Suc i), f i) \<in> ?R\<close> for i
    unfolding wf_iff_no_infinite_down_chain by blast

  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close>
    using vmtf unfolding vmtf_def by fast
  let ?f0 = \<open>the (f 0)\<close>
  have f_None: \<open>f i \<noteq> None\<close> for i
    using f[of i] by fast
  have f_Suc : \<open>f (Suc n) = get_next (ns ! the (f n))\<close> for n
    using f[of n] by auto
  have f0_length: \<open>?f0 < length ns\<close>
    using f[of 0] atm_A
    by auto
  have \<open>?f0 \<in> set (ys' @ xs')\<close>
    apply (rule ccontr)
    using notin f_Suc[of 0] f0_length unfolding vmtf_ns_notin_def
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
        using vmtf_ns_last_next[of \<open>butlast (ys' @ xs')\<close> \<open>the (f n')\<close> m ns] vmtf_ns
         f_Suc[of n'] by (auto simp: f_None)
    qed
    have get_next: \<open>get_next (ns ! ((ys' @ xs') ! (i0 + n'))) = Some ((ys' @ xs') ! (i0 + n' + 1))\<close>
      apply(rule vmtf_ns_last_mid_get_next[of \<open>take (i0 + n') (ys' @ xs')\<close>
        \<open>(ys' @ xs') ! (i0 + n')\<close>
        \<open>(ys' @ xs') ! ((i0 + n') + 1)\<close>
        \<open>drop ((i0 + n') + 2) (ys' @ xs')\<close>
        m ns])
      apply (subst H[symmetric])
      subgoal using i0_le .
      subgoal using vmtf_ns by simp
      done
    then show ?case
      using f_Suc[of n'] Suc i0_le by auto
  qed
  then show False
    by blast
qed

lemma vmtf_next_search_take_next:
  assumes
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close> and
    n: \<open>next_search \<noteq> None\<close> and
    def_n: \<open>defined_lit M (Pos (the next_search))\<close>
  shows \<open>((ns, m, fst_As, lst_As, get_next (ns!the next_search)), to_remove) \<in> vmtf M\<close>
  unfolding vmtf_def
proof clarify
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  let ?xs' = \<open>tl xs'\<close>
  let ?ys' = \<open>ys' @ [hd xs']\<close>
  have [simp]: \<open>xs' \<noteq> []\<close>
    using next_search n by auto
  have \<open>vmtf_ns (?ys' @ ?xs') m ns\<close>
    using vmtf_ns by (cases xs') auto
  moreover have \<open>fst_As = hd (?ys' @ ?xs')\<close>
    using fst_As by auto
  moreover have \<open>lst_As = last (?ys' @ ?xs')\<close>
    using lst_As by auto
  moreover have \<open>get_next (ns ! the next_search) = option_hd ?xs'\<close>
    using next_search n vmtf_ns
    by (cases xs') (auto dest: vmtf_ns_last_mid_get_next_option_hd)
  moreover {
    have [dest]: \<open>defined_lit M (Pos a) \<Longrightarrow> a \<in> atm_of ` lits_of_l M\<close> for a
      by (auto simp: defined_lit_map lits_of_def)
    have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set ?xs', set ?ys'), set to_remove)\<close>
      using abs_vmtf def_n next_search n vmtf_ns_distinct[OF vmtf_ns]
      unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by (cases xs') auto }
  moreover have \<open>vmtf_ns_notin (?ys' @ ?xs') m ns\<close>
    using notin by auto
  moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
  ultimately show \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m ns \<and>
          fst_As = hd (ys' @ xs') \<and>
          lst_As = last (ys' @ xs') \<and>
          get_next (ns ! the next_search) = option_hd xs' \<and>
          vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove) \<and>
          vmtf_ns_notin (ys' @ xs') m ns \<and>
          (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns) \<and>
          (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    using atm_A by blast
qed


definition (in isasat_input_ops) vmtf_find_next_undef :: \<open>vmtf_remove_int \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat option) nres\<close> where
\<open>vmtf_find_next_undef \<equiv> (\<lambda>((ns, m, fst_As, lst_As, next_search), to_remove) M. do {
    WHILE\<^sub>T\<^bsup>\<lambda>next_search. ((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M \<and>
         (next_search \<noteq> None \<longrightarrow> Pos (the next_search) \<in> snd ` D\<^sub>0)\<^esup>
      (\<lambda>next_search. next_search \<noteq> None \<and> defined_lit M (Pos (the next_search)))
      (\<lambda>next_search. do {
         ASSERT(next_search \<noteq> None);
         let n = the next_search;
         ASSERT(Pos n \<in> snd ` D\<^sub>0);
         ASSERT (n < length ns);
         RETURN (get_next (ns!n))
        }
      )
      next_search
  })\<close>

lemma vmtf_find_next_undef_ref:
  assumes
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close>
  shows \<open>vmtf_find_next_undef ((ns, m, fst_As, lst_As, next_search), to_remove) M
     \<le> \<Down> Id (SPEC (\<lambda>L. ((ns, m, fst_As, lst_As, L), to_remove) \<in> vmtf M \<and>
        (L = None \<longrightarrow> (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. defined_lit M L)) \<and>
        (L \<noteq> None \<longrightarrow> Pos (the L) \<in> snd ` D\<^sub>0 \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close>
    using vmtf unfolding vmtf_def by fast
  have [simp]: \<open>index xs' (hd xs') = 0\<close> if \<open>xs' \<noteq> []\<close> for xs' :: \<open>'a list\<close>
    using that by (cases xs') auto
  have no_next_search_all_defined:
    \<open>((ns', m', fst_As', lst_As', None), remove) \<in> vmtf M \<Longrightarrow>  x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> defined_lit M x\<close>
    for x ns' m' fst_As' lst_As' remove
    by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  have next_search_\<L>\<^sub>a\<^sub>l\<^sub>l:
    \<open>((ns', m', fst_As', lst_As', Some y), remove) \<in> vmtf M \<Longrightarrow> y \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for ns' m' fst_As' remove y lst_As'
    by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  have next_search_le_A':
    \<open>((ns', m', fst_As', lst_As', Some y), remove) \<in> vmtf M \<Longrightarrow> y < length ns'\<close>
    for ns' m' fst_As' remove y lst_As'
    by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  show ?thesis
    unfolding vmtf_find_next_undef_def
    apply (refine_vcg
       WHILEIT_rule[where R=\<open>{(get_next (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l}\<close>])
    subgoal using vmtf by (rule wf_vmtf_get_next)
    subgoal using next_search vmtf by auto
    subgoal using vmtf by (auto dest!: next_search_\<L>\<^sub>a\<^sub>l\<^sub>l simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    subgoal using vmtf by auto
    subgoal using vmtf by auto
    subgoal using vmtf by (auto dest: next_search_le_A')
    subgoal by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
        (metis next_search_\<L>\<^sub>a\<^sub>l\<^sub>l option.distinct(1) option.sel vmtf_next_search_take_next)
    subgoal by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
        (metis next_search_\<L>\<^sub>a\<^sub>l\<^sub>l option.distinct(1) option.sel vmtf_next_search_take_next)
    subgoal by (auto dest: no_next_search_all_defined next_search_\<L>\<^sub>a\<^sub>l\<^sub>l)
    subgoal by (auto dest: next_search_le_A')
    subgoal for x1 ns' x2 m' x2a fst_As' next_search' x2c s
      by (auto dest: no_next_search_all_defined next_search_\<L>\<^sub>a\<^sub>l\<^sub>l)
    subgoal by (auto dest: vmtf_next_search_take_next)
    subgoal by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    done
qed

definition (in isasat_input_ops) vmtf_mark_to_rescore
  :: \<open>nat \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int\<close>
where
  \<open>vmtf_mark_to_rescore L = (\<lambda>((ns, m, fst_As, next_search), to_remove).
     ((ns, m, fst_As, next_search), to_remove @ [L]))\<close>

lemma vmtf_mark_to_rescore:
  assumes L: \<open>L \<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close>
  shows \<open>vmtf_mark_to_rescore L ((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf M\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set (to_remove @ [L]))\<close>
    using abs_vmtf L unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by auto
  ultimately show ?thesis
    unfolding vmtf_def vmtf_mark_to_rescore_def by fast
qed

lemma vmtf_unset_vmtf_tl:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf M\<close> and
    L_N: \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>(vmtf_unset L ((ns, m, fst_As, lst_As, next_search), remove)) \<in> vmtf (tl M)\<close>
     (is \<open>?S \<in> _\<close>)
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  obtain ns' m' fst_As' next_search' remove'' lst_As' where
    S: \<open>?S = ((ns', m', fst_As', lst_As', next_search'), remove'')\<close>
    by (cases ?S) auto
  have L_ys'_iff: \<open>L \<in> set ys' \<longleftrightarrow> (next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L))\<close>
    using vmtf_atm_of_ys_iff[OF vmtf_ns next_search abs_vmtf L_N] .
  have dist: \<open>distinct (ys' @ xs')\<close>
    using vmtf_ns_distinct[OF vmtf_ns] .
  have \<open>L \<in> set (xs' @ ys')\<close>
    using abs_vmtf L_N unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  then have L_ys'_xs': \<open>L \<in> set ys' \<longleftrightarrow> L \<notin> set xs'\<close>
    using dist by auto
  have [simp]: \<open>remove'' = remove\<close>
    using S unfolding vmtf_unset_def by (auto split: if_splits)
  have \<open>\<exists>xs' ys'.
       vmtf_ns (ys' @ xs') m' ns' \<and>
       fst_As' = hd (ys' @ xs') \<and>
       lst_As' = last (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (tl M) ((set xs', set ys'), set remove'') \<and>
       vmtf_ns_notin (ys' @ xs') m' ns' \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
  proof (cases \<open>L \<in> set xs'\<close>)
    case True
    then have C[unfolded L_def]: \<open>\<not>(next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L))\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (tl M) ((set xs', set ys'), set remove)\<close>
      using S abs_vmtf dist L_ys'_xs' True unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def vmtf_unset_def
      by (cases M) (auto simp: C)
    show ?thesis
      using S True unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      apply -
      apply (simp add: C)
      using vmtf_ns fst_As next_search abs_vmtf notin atm_A ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l lst_As
      by auto
  next
    case False
    then have C[unfolded L_def]: \<open>next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L)\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have L_ys: \<open>L \<in> set ys'\<close>
      by (use False L_ys'_xs' in auto)
    define y_ys where \<open>y_ys \<equiv> takeWhile ((\<noteq>) L) ys'\<close>
    define x_ys where \<open>x_ys \<equiv> drop (length y_ys) ys'\<close>
    let ?ys' = \<open>y_ys\<close>
    let ?xs' = \<open>x_ys @ xs'\<close>
    have x_ys_take_ys': \<open>y_ys = take (length y_ys) ys'\<close>
        unfolding y_ys_def
        by (subst take_length_takeWhile_eq_takeWhile[of \<open>(\<noteq>) L\<close> \<open>ys'\<close>, symmetric]) standard
    have ys'_y_x: \<open>ys' = y_ys @ x_ys\<close>
      by (subst x_ys_take_ys') (auto simp: x_ys_def)
    have y_ys_le_ys': \<open>length y_ys < length ys'\<close>
      using L_ys by (metis (full_types) append_eq_conv_conj append_self_conv le_antisym
        length_takeWhile_le not_less takeWhile_eq_all_conv x_ys_take_ys' y_ys_def)
    from nth_length_takeWhile[OF this[unfolded y_ys_def]] have [simp]: \<open>x_ys \<noteq> []\<close> \<open>hd x_ys = L\<close>
      using y_ys_le_ys' unfolding x_ys_def y_ys_def
      by (auto simp: x_ys_def y_ys_def hd_drop_conv_nth)
    have [simp]: \<open>ns' = ns\<close> \<open>m' = m\<close> \<open>fst_As' = fst_As\<close> \<open>next_search' = Some (atm_of (lit_of (hd M)))\<close>
      \<open>lst_As' = lst_As\<close>
      using S unfolding vmtf_unset_def by (auto simp: C)
    have L_y_ys: \<open>L \<notin> set y_ys\<close>
       unfolding y_ys_def by (metis (full_types) takeWhile_eq_all_conv takeWhile_idem)
    have \<open>vmtf_ns (?ys' @ ?xs') m ns\<close>
      using vmtf_ns unfolding ys'_y_x by simp
    moreover have \<open>fst_As' = hd (?ys' @ ?xs')\<close>
      using fst_As unfolding ys'_y_x by simp
    moreover have \<open>lst_As' = last (?ys' @ ?xs')\<close>
      using lst_As unfolding ys'_y_x by simp
    moreover have \<open>next_search' = option_hd ?xs'\<close>
      by auto
    moreover {
      have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set ?xs', set ?ys'), set remove)\<close>
        using abs_vmtf dist unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def ys'_y_x
        by auto
      then have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l (tl M) ((set ?xs', set ?ys'), set remove)\<close>
        using dist L_y_ys unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def ys'_y_x ys'_y_x
        by (cases M) auto
      }
    moreover have \<open>vmtf_ns_notin (?ys' @ ?xs') m ns\<close>
      using notin unfolding ys'_y_x by simp
    moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding ys'_y_x by simp
    ultimately show ?thesis
      using S False atm_A unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      by (fastforce simp add: C)
  qed
  then show ?thesis
    unfolding vmtf_def S
    by fast
qed

definition (in isasat_input_ops) vmtf_mark_to_rescore_and_unset  :: \<open>nat \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int\<close> where
  \<open>vmtf_mark_to_rescore_and_unset L M = vmtf_mark_to_rescore L (vmtf_unset L M)\<close>

lemma vmtf_append_remove_iff:
  \<open>((ns, m, fst_As, lst_As, next_search), b @ [L]) \<in> vmtf M \<longleftrightarrow>
     L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<and> ((ns, m, fst_As, lst_As, next_search), b) \<in> vmtf M\<close>
  (is \<open>?A \<longleftrightarrow> ?L \<and> ?B\<close>)
proof
  assume vmtf: ?A
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set (b @ [L]))\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set b)\<close> and L: ?L
    using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  ultimately have \<open>vmtf_ns (ys' @ xs') m ns \<and>
       fst_As = hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       lst_As = last (ys' @ xs') \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set b) \<and>
       vmtf_ns_notin (ys' @ xs') m ns \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
      by fast
  then show \<open>?L \<and> ?B\<close>
    using L unfolding vmtf_def by fast
next
  assume vmtf: \<open>?L \<and> ?B\<close>
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set b)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set (b @ [L]))\<close>
    using vmtf abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  ultimately have \<open>vmtf_ns (ys' @ xs') m ns \<and>
       fst_As = hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       lst_As = last (ys' @ xs') \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set (b @ [L])) \<and>
       vmtf_ns_notin (ys' @ xs') m ns \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
      by fast
  then show \<open>?A\<close>
    unfolding vmtf_def by fast
qed

lemma vmtf_append_remove_iff':
  \<open>(vm, b @ [L]) \<in> vmtf M \<longleftrightarrow>
     L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<and> (vm, b) \<in> vmtf M\<close>
  by (cases vm) (auto simp: vmtf_append_remove_iff)

lemma vmtf_mark_to_rescore_unset:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf M\<close> and
    L_N: \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>(vmtf_mark_to_rescore_and_unset L ((ns, m, fst_As, lst_As, next_search), remove)) \<in> vmtf (tl M)\<close>
     (is \<open>?S \<in> _\<close>)
  using vmtf_unset_vmtf_tl[OF assms(2-)[unfolded assms(1)]] L_N
  unfolding vmtf_mark_to_rescore_and_unset_def vmtf_mark_to_rescore_def
  by (cases \<open>vmtf_unset (atm_of (lit_of (hd M))) ((ns, m, fst_As, lst_As, next_search), remove)\<close>)
     (auto simp: vmtf_append_remove_iff)


lemma vmtf_insert_sort_nth_code_preD:
  assumes vmtf: \<open>vm \<in> vmtf M\<close>
  shows \<open>\<forall>x\<in>set (snd vm). x < length (fst (fst vm))\<close>
proof -
  obtain ns m fst_As lst_As next_search remove where
    vm: \<open>vm = ((ns, m, fst_As, lst_As, next_search), remove)\<close>
    by (cases vm) auto

  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using vmtf unfolding vmtf_def vm by fast
  show ?thesis
    using atm_A abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: vm)
qed

end


lemma vmtf_ns_Cons:
  assumes
    vmtf: \<open>vmtf_ns (b # l) m xs\<close> and
    a_xs: \<open>a < length xs\<close> and
    ab: \<open>a \<noteq> b\<close> and
    a_l: \<open>a \<notin> set l\<close> and
    nm: \<open>n > m\<close> and
    xs': \<open>xs' = xs[a := VMTF_Node n None (Some b),
         b := VMTF_Node (stamp (xs!b)) (Some a) (get_next (xs!b))]\<close> and
    nn': \<open>n' \<ge> n\<close>
  shows \<open>vmtf_ns (a # b # l) n' xs'\<close>
proof -
  have \<open>vmtf_ns (b # l) m (xs[a := VMTF_Node n None (Some b)])\<close>
    apply (rule vmtf_ns_eq_iffI[OF _ _ vmtf])
    subgoal using ab a_l a_xs by auto
    subgoal using a_xs vmtf_ns_le_length[OF vmtf] by auto
    done
  then show ?thesis
    apply (rule vmtf_ns.Cons[of _ _ _ _ _ n])
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
\<open>vmtf_cons ns L cnext st =
  (let
    ns = ns[L := VMTF_Node (Suc st) None cnext];
    ns = (case cnext of None \<Rightarrow> ns
        | Some cnext \<Rightarrow> ns[cnext := VMTF_Node (stamp (ns!cnext)) (Some L) (get_next (ns!cnext))]) in
  ns)
\<close>

lemma vmtf_notin_vmtf_cons:
  assumes
    vmtf_ns: \<open>vmtf_ns_notin xs m ns\<close> and
    cnext: \<open>cnext = option_hd xs\<close> and
    L_xs: \<open>L \<notin> set xs\<close>
  shows
    \<open>vmtf_ns_notin (L # xs) (Suc m) (vmtf_cons ns L cnext m)\<close>
proof (cases xs)
  case Nil
  then show ?thesis
    using assms by (auto simp: vmtf_ns_notin_def vmtf_cons_def elim: vmtf_nsE)
next
  case (Cons L' xs') note xs = this
  show ?thesis
    using assms unfolding xs vmtf_ns_notin_def xs vmtf_cons_def by auto
qed

lemma vmtf_cons:
  assumes
    vmtf_ns: \<open>vmtf_ns xs m ns\<close> and
    cnext: \<open>cnext = option_hd xs\<close> and
    L_A: \<open>L < length ns\<close> and
    L_xs: \<open>L \<notin> set xs\<close>
  shows
    \<open>vmtf_ns (L # xs) (Suc m) (vmtf_cons ns L cnext m)\<close>
proof (cases xs)
  case Nil
  then show ?thesis
    using assms by (auto simp: vmtf_ns_single_iff vmtf_cons_def elim: vmtf_nsE)
next
  case (Cons L' xs') note xs = this
  show ?thesis
    unfolding xs
    apply (rule vmtf_ns_Cons[OF vmtf_ns[unfolded xs], of _ \<open>Suc m\<close>])
    subgoal using L_A .
    subgoal using L_xs unfolding xs by simp
    subgoal using L_xs unfolding xs by simp
    subgoal by simp
    subgoal using cnext L_xs
      by (auto simp: vmtf_cons_def Let_def xs)
    subgoal by linarith
    done
qed

lemma length_vmtf_cons[simp]: \<open>length (vmtf_cons ns L n m) = length ns\<close>
  by (auto simp: vmtf_cons_def Let_def split: option.splits)


subsection \<open>Phase saving\<close>

type_synonym phase_saver = \<open>bool list\<close>

definition (in isasat_input_ops) phase_saving :: \<open>phase_saver \<Rightarrow> bool\<close> where
\<open>phase_saving \<phi> \<longleftrightarrow> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length \<phi>)\<close>

text \<open>Save phase as given (e.g. for literals in the trail):\<close>
definition (in isasat_input_ops) save_phase :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase L \<phi> = \<phi>[atm_of L := is_pos L]\<close>

text \<open>Save opposite of the phase (e.g. for literals in the conflict clause):\<close>
definition  (in isasat_input_ops) save_phase_inv :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase_inv L \<phi> = \<phi>[atm_of L := \<not>is_pos L]\<close>


type_synonym vmtf_assn = \<open>(uint32, nat) vmtf_node array \<times> nat \<times> uint32 \<times> uint32 \<times> uint32 option\<close>
type_synonym vmtf_remove_assn = \<open>vmtf_assn \<times> uint32 array_list\<close>

type_synonym phase_saver_assn = \<open>bool array\<close>

instance vmtf_node :: (heap, heap) heap
proof intro_classes
  let ?to_pair = \<open>\<lambda>x::('a, 'b) vmtf_node. (stamp x, get_prev x, get_next x)\<close>
  have inj': \<open>inj ?to_pair\<close>
    unfolding inj_def by (intro allI) (case_tac x; case_tac y; auto)
  obtain to_nat :: \<open>'b \<times> 'a option \<times> 'a option \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o ?to_pair)\<close>
    using inj' by (blast intro: inj_comp)
  then show \<open>\<exists>to_nat :: ('a, 'b) vmtf_node \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed


definition (in -) nat_vmtf_node_rel where
\<open>nat_vmtf_node_rel = {(a', a). stamp a = stamp a' \<and>
   (get_prev a', get_prev a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel \<and>
   (get_next a', get_next a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel}\<close>

abbreviation (in -)nat_vmtf_node_assn where
\<open>nat_vmtf_node_assn \<equiv> pure nat_vmtf_node_rel\<close>

lemma VMTF_Node_ref[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo VMTF_Node), uncurry2 (RETURN ooo VMTF_Node)) \<in>
    nat_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a
    nat_vmtf_node_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: nat_vmtf_node_rel_def uint32_nat_rel_def br_def option_assn_alt_def
     split: option.splits)

lemma stamp_ref[sepref_fr_rules]: \<open>(return o stamp, RETURN o stamp) \<in> nat_vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare
    (auto simp: ex_assn_move_out(2)[symmetric] return_cons_rule ent_ex_up_swap nat_vmtf_node_rel_def
      simp del: ex_assn_move_out)

lemma get_next_ref[sepref_fr_rules]: \<open>(return o get_next, RETURN o get_next) \<in> nat_vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule nat_vmtf_node_rel_def)

lemma get_prev_ref[sepref_fr_rules]: \<open>(return o get_prev, RETURN o get_prev) \<in> nat_vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule nat_vmtf_node_rel_def)

abbreviation vmtf_conc where
  \<open>vmtf_conc \<equiv> (array_assn nat_vmtf_node_assn *a nat_assn *a uint32_nat_assn *a uint32_nat_assn
    *a option_assn uint32_nat_assn)\<close>


abbreviation vmtf_remove_conc :: \<open>vmtf_remove_int \<Rightarrow> vmtf_remove_assn \<Rightarrow> assn\<close> where
  \<open>vmtf_remove_conc \<equiv> vmtf_conc *a arl_assn uint32_nat_assn\<close>

definition update_next_search where
  \<open>update_next_search L = (\<lambda>((ns, m, fst_As, lst_As, next_search), to_remove). ((ns, m, fst_As, lst_As, L), to_remove))\<close>

lemma update_next_search_ref[sepref_fr_rules]:
  \<open>(uncurry (return oo update_next_search), uncurry (RETURN oo update_next_search)) \<in>
      (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: update_next_search_def)

sepref_definition (in -)ns_vmtf_dequeue_code
   is \<open>uncurry (RETURN oo ns_vmtf_dequeue)\<close>
   :: \<open>[vmtf_dequeue_pre]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a (array_assn nat_vmtf_node_assn)\<^sup>d \<rightarrow> array_assn nat_vmtf_node_assn\<close>
  supply [[goals_limit = 1]]
  supply option.splits[split]
  unfolding ns_vmtf_dequeue_def vmtf_dequeue_pre_alt_def
  by sepref

declare ns_vmtf_dequeue_code.refine[sepref_fr_rules]

abbreviation vmtf_conc_option_fst_As where
  \<open>vmtf_conc_option_fst_As \<equiv> (array_assn nat_vmtf_node_assn *a nat_assn *a option_assn uint32_nat_assn
    *a option_assn uint32_nat_assn
    *a option_assn uint32_nat_assn)\<close>

sepref_definition vmtf_dequeue_code
   is \<open>uncurry (RETURN oo vmtf_dequeue)\<close>
   :: \<open>[\<lambda>(L,(ns,m,fst_As,next_search)). L < length ns \<and> vmtf_dequeue_pre (L, ns)]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc_option_fst_As\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_dequeue_def
  by sepref

declare vmtf_dequeue_code.refine[sepref_fr_rules]

definition vmtf_enqueue_pre where
  \<open>vmtf_enqueue_pre =
     (\<lambda>(L,(ns,m,fst_As,lst_As, next_search)). L < length ns \<and>
       (fst_As \<noteq> None \<longrightarrow> the fst_As < length ns) \<and>
       (fst_As \<noteq> None \<longrightarrow> lst_As \<noteq> None))\<close>

sepref_definition vmtf_enqueue_code
   is \<open>uncurry (RETURN oo vmtf_enqueue)\<close>
   :: \<open>[vmtf_enqueue_pre]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc_option_fst_As\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_enqueue_def vmtf_enqueue_pre_def
  by sepref

declare vmtf_enqueue_code.refine[sepref_fr_rules]

definition insert_sort_inner_nth :: \<open>nat_vmtf_node list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>insert_sort_inner_nth ns = insert_sort_inner (\<lambda>remove n. stamp (ns ! (remove ! n)))\<close>

definition insert_sort_nth :: \<open>nat_vmtf_node list \<times> 'c \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>insert_sort_nth = (\<lambda>(ns, _). insert_sort (\<lambda>remove n. stamp (ns ! (remove ! n))))\<close>


lemma insert_sort_inner_nth_code_helper:
  assumes \<open>\<forall>x\<in>set ba. x < length a\<close>  and
      \<open>b < length ba\<close> and
     mset: \<open>mset ba = mset a2'\<close>  and
      \<open>a1' < length a2'\<close>
  shows \<open>a2' ! b < length a\<close>
  using nth_mem[of b a2'] mset_eq_setD[OF mset] mset_eq_length[OF mset] assms
  by (auto simp del: nth_mem)

sepref_definition (in -) insert_sort_inner_nth_code
   is \<open>uncurry2 insert_sort_inner_nth\<close>
   :: \<open>[\<lambda>((xs, remove), n). (\<forall>x\<in>#mset remove. x < length xs) \<and> n < length remove]\<^sub>a
  (array_assn nat_vmtf_node_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
  arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_inner_nth_def insert_sort_inner_def fast_minus_def[symmetric]
    short_circuit_conv
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]  insert_sort_inner_nth_code_helper[intro]
    if_splits[split]
  by sepref

declare insert_sort_inner_nth_code.refine[sepref_fr_rules]

sepref_definition (in -) insert_sort_nth_code
   is \<open>uncurry insert_sort_nth\<close>
   :: \<open>[\<lambda>(vm, remove). (\<forall>x\<in>#mset remove. x < length (fst vm))]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_nth_def insert_sort_def insert_sort_inner_nth_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare insert_sort_nth_code.refine[sepref_fr_rules]
term vmtf_en_dequeue_pre

lemma vmtf_en_dequeue_pre_vmtf_enqueue_pre:
   \<open>vmtf_en_dequeue_pre (L, a, st, fst_As, lst_As, next_search) \<Longrightarrow>
       vmtf_enqueue_pre (L, vmtf_dequeue L (a, st, fst_As, lst_As, next_search))\<close>
  unfolding vmtf_enqueue_pre_def
  apply clarify
  apply (intro conjI)
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        ns_vmtf_dequeue_def Let_def vmtf_en_dequeue_pre_def split: option.splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
          vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        Let_def vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  done

lemma vmtf_en_dequeue_preD:
  assumes \<open>vmtf_en_dequeue_pre (ah, a, aa, ab, ac, b)\<close>
  shows \<open>ah < length a\<close> and \<open>vmtf_dequeue_pre (ah, a)\<close>
  using assms by (auto simp: vmtf_en_dequeue_pre_def)
sepref_definition vmtf_en_dequeue_code
   is \<open>uncurry (RETURN oo vmtf_en_dequeue)\<close>
   :: \<open>[vmtf_en_dequeue_pre]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_preD[dest] vmtf_en_dequeue_pre_vmtf_enqueue_pre[dest]
  unfolding vmtf_en_dequeue_def
  by sepref

declare vmtf_en_dequeue_code.refine[sepref_fr_rules]

lemma insert_sort_nth_reorder:
   \<open>(uncurry insert_sort_nth, uncurry reorder_remove) \<in>
      Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  using insert_sort_reorder_remove[unfolded fref_def nres_rel_def]
  by (intro frefI nres_relI) (fastforce simp: insert_sort_nth_def)

lemma (in -) insert_sort_nth_code_reorder_remove[sepref_fr_rules]:
   \<open>(uncurry insert_sort_nth_code, uncurry reorder_remove) \<in>
      [\<lambda>((a, _), b). \<forall>x\<in>set b. x < length a]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d \<rightarrow> arl_assn uint32_nat_assn\<close>
  using insert_sort_nth_code.refine[FCOMP insert_sort_nth_reorder]
  by auto

context isasat_input_bounded_nempty
begin

sepref_thm vmtf_flush_code
   is \<open>vmtf_flush\<close>
   :: \<open>[\<lambda>a. \<exists>M. a \<in> vmtf M]\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp] vmtf_insert_sort_nth_code_preD[dest]
  unfolding vmtf_flush_def
  apply (rewrite
        at \<open>[]\<close> in \<open>\<lambda>(_, to_remove). do {to_remove' \<leftarrow> _; (vm, _) \<leftarrow> _; RETURN (_, \<hole>)}\<close>
        to \<open>emptied_list to_remove'\<close>
          emptied_list_def[symmetric]
     )
  by sepref


concrete_definition (in -) vmtf_flush_code
   uses isasat_input_bounded_nempty.vmtf_flush_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_code_def

lemmas trail_dump_code_refine[sepref_fr_rules] =
   vmtf_flush_code.refine[OF isasat_input_bounded_nempty_axioms]

declare vmtf_flush_code.refine[sepref_fr_rules]

sepref_thm vmtf_mark_to_rescore_and_unset_code
  is \<open>uncurry (RETURN oo vmtf_mark_to_rescore_and_unset)\<close>
  :: \<open>[\<lambda>(L, ((ns, m, fst_As, lst_As, next_search), _)).
      L < length ns \<and> (next_search \<noteq> None \<longrightarrow> the next_search < length ns)]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  unfolding vmtf_mark_to_rescore_and_unset_def vmtf_mark_to_rescore_def
   vmtf_unset_def save_phase_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

concrete_definition (in -) vmtf_mark_to_rescore_and_unset_code
  uses isasat_input_bounded_nempty.vmtf_mark_to_rescore_and_unset_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_mark_to_rescore_and_unset_code_def

lemmas vmtf_mark_to_rescore_and_unset_hnr[sepref_fr_rules] =
   vmtf_mark_to_rescore_and_unset_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm vmtf_unset_code
  is \<open>uncurry (RETURN oo vmtf_unset)\<close>
  :: \<open>[\<lambda>(L, vm). \<exists>M. L = atm_of(lit_of (hd M)) \<and> vm \<in> vmtf M \<and> M \<noteq> [] \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding vmtf_unset_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

concrete_definition (in -) vmtf_unset_code
   uses isasat_input_bounded_nempty.vmtf_unset_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_unset_code_def

lemmas vmtf_unset_code_code[sepref_fr_rules] =
   vmtf_unset_code.refine[OF isasat_input_bounded_nempty_axioms]

end

end
