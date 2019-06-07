theory Watched_Literals_VMTF
  imports IsaSAT_Literals
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
  option_last_Some_iff[iff]:
    \<open>option_last l = Some a \<longleftrightarrow> l \<noteq> [] \<and> a = last l\<close>
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

lemma vmtf_ns_hd_prev:
  \<open>vmtf_ns (x # xs) m ns \<Longrightarrow> get_prev (ns ! x) = None\<close>
  apply (induction "x # xs" m ns arbitrary: xs x rule: vmtf_ns.induct)
  subgoal by auto
  subgoal by auto
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
    \<open>\<forall>a\<in>set l. a < length st\<close> and
    m': \<open>\<forall>a \<in> set l. st ! a < m'\<close>
  shows \<open>vmtf_ns l m' zs\<close>
  using assms
proof (induction arbitrary: zs m' rule: vmtf_ns.induct)
  case (Nil st xs)
  then show ?case by (auto intro: vmtf_ns.intros)
next
  case (Cons1 a xs m n)
  then show ?case by (cases \<open>zs ! a\<close>) (auto simp: vmtf_ns_single_iff intro!: Max_ge nth_mem)
next
  case (Cons b l m xs a n xs' n' zs m') note vmtf_ns = this(1) and a_le_y = this(2) and
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

  have vtmf_b_l: \<open>vmtf_ns (b # l) m' zs'\<close>
    unfolding zs'_def
    apply (rule IH)
    subgoal using H(1) by (simp add: sorted_many_eq_append)
    subgoal using H(2) by auto
    subgoal using H(3,4,5) xs' zs_a a_l ab by (auto split: if_splits)
    subgoal using H(4) xs' zs_a a_l ab by auto
    subgoal using H(5) xs' a_l ab by auto
    subgoal using H(6) xs' by auto
    subgoal using H(7) xs' by auto
    subgoal using H(8) by auto
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


paragraph \<open>Abstract Invariants\<close>

text \<open>
  Invariants
  \<^item> The atoms of \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close> are always disjoint.
  \<^item> The atoms of \<^term>\<open>ys\<close> are \<^emph>\<open>always\<close> set.
  \<^item> The atoms of \<^term>\<open>xs\<close> \<^emph>\<open>can\<close> be set but do not have to.
  \<^item> The atoms of \<^term>\<open>zs\<close> are either in \<^term>\<open>xs\<close> and \<^term>\<open>ys\<close>.
\<close>

definition vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat abs_vmtf_ns_remove \<Rightarrow> bool\<close> where
\<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M \<equiv> \<lambda>((xs, ys), zs).
  (\<forall>L\<in>ys. L \<in> atm_of ` lits_of_l M) \<and>
  xs \<inter> ys = {} \<and>
  zs \<subseteq> xs \<union> ys \<and>
  xs \<union> ys = atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)
  \<close>

abbreviation abs_vmtf_ns_inv :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat abs_vmtf_ns \<Rightarrow> bool\<close> where
\<open>abs_vmtf_ns_inv \<A> M vm \<equiv> vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M (vm, {})\<close>


subsubsection \<open>Implementation\<close>

type_synonym (in -) vmtf = \<open>nat_vmtf_node list \<times> nat \<times> nat \<times> nat \<times> nat option\<close>
type_synonym (in -) vmtf_remove_int = \<open>vmtf \<times> nat set\<close>

text \<open>
  We use the opposite direction of the VMTF paper: The latest added element \<^term>\<open>fst_As\<close> is at
  the beginning.
\<close>

definition vmtf :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> vmtf_remove_int set\<close> where
\<open>vmtf \<A> M = {((ns, m, fst_As, lst_As, next_search), to_remove).
   (\<exists>xs' ys'.
     vmtf_ns (ys' @ xs') m ns \<and> fst_As = hd (ys' @ xs') \<and> lst_As = last (ys' @ xs')
   \<and> next_search = option_hd xs'
   \<and> vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)
   \<and> vmtf_ns_notin (ys' @ xs') m ns
   \<and> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns) \<and> (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))
  )}\<close>

lemma vmtf_consD:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf \<A> M\<close>
  shows \<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf \<A> (L # M)\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (L # M) ((set xs', set ys'), remove)\<close>
    using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  ultimately have \<open>vmtf_ns (ys' @ xs') m ns \<and>
       fst_As = hd (ys' @ xs') \<and>
       lst_As = last (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (L # M) ((set xs', set ys'), remove) \<and>
       vmtf_ns_notin (ys' @ xs') m ns \<and> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
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
definition vmtf_enqueue :: \<open>(nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> vmtf_option_fst_As \<Rightarrow> vmtf\<close> where
\<open>vmtf_enqueue = (\<lambda>M L (ns, m, fst_As, lst_As, next_search).
  (case fst_As of
    None \<Rightarrow> (ns[L := VMTF_Node m fst_As None], m+1, L, L,
         (if defined_lit M (Pos L) then None else Some L))
  | Some fst_As \<Rightarrow>
     let fst_As' = VMTF_Node (stamp (ns!fst_As)) (Some L) (get_next (ns!fst_As)) in
      (ns[L := VMTF_Node (m+1) None (Some fst_As), fst_As := fst_As'],
          m+1, L, the lst_As, (if defined_lit M (Pos L) then next_search else Some L))))\<close>

definition (in -) vmtf_en_dequeue :: \<open>(nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> vmtf \<Rightarrow>  vmtf\<close> where
\<open>vmtf_en_dequeue = (\<lambda>M L vm. vmtf_enqueue M L (vmtf_dequeue L vm))\<close>

lemma abs_vmtf_ns_bump_vmtf_dequeue:
  fixes M
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>  and
    L: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    dequeue: \<open>(ns', m', fst_As', lst_As', next_search') =
       vmtf_dequeue L (ns, m, fst_As, lst_As, next_search)\<close> and
    \<A>\<^sub>i\<^sub>n_nempty: \<open>isasat_input_nempty \<A>\<close>
  shows \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m' ns' \<and> fst_As' = option_hd (ys' @ xs')
   \<and> lst_As' = option_last (ys' @ xs')
   \<and> next_search' = option_hd xs'
   \<and> next_search' = (if next_search = Some L then get_next (ns!L) else next_search)
   \<and> vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((insert L (set xs'), set ys'), to_remove)
   \<and> vmtf_ns_notin (ys' @ xs') m' ns' \<and>
   L \<notin> set (ys' @ xs') \<and> (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
  unfolding vmtf_def
proof -
  have ns': \<open>ns' = ns_vmtf_dequeue L ns\<close> and
    fst_As': \<open>fst_As' = (if fst_As = L then get_next (ns ! L) else Some fst_As)\<close> and
    lst_As': \<open>lst_As' = (if lst_As = L then get_prev (ns ! L) else Some lst_As)\<close> and
    m'm: \<open>m' = m\<close> and
    next_search_L_next:
      \<open>next_search' = (if next_search = Some L then get_next (ns!L) else next_search)\<close>
    using dequeue unfolding vmtf_dequeue_def by auto
  obtain xs ys where
    vmtf: \<open>vmtf_ns (ys @ xs) m ns\<close> and
    notin: \<open>vmtf_ns_notin (ys @ xs) m ns\<close> and
    next_search: \<open>next_search = option_hd xs\<close> and
    abs_inv: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs, set ys), to_remove)\<close> and
    fst_As: \<open>fst_As = hd (ys @ xs)\<close> and
    lst_As: \<open>lst_As = last (ys @ xs)\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    L_ys_xs: \<open>\<forall>L\<in>set (ys @ xs). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((insert L (set (remove1 L xs)), set (remove1 L ys)),
    to_remove)\<close>
    using abs_inv L dist
    unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto dest: in_set_remove1D)
  moreover have \<open>vmtf_ns_notin (remove1 L ?ys @ remove1 L ?xs) m' ns'\<close>
    unfolding xs_ys ns'
    apply (rule vmtf_ns_notin_dequeue)
    subgoal using vmtf unfolding m'm .
    subgoal using notin unfolding m'm .
    subgoal using atm_L_A .
    done
  moreover have \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns'\<close>
    using atm_A unfolding ns' by auto
  moreover have \<open>L \<notin> set (remove1 L ys @ remove1 L xs)\<close>
    using dist by auto
  moreover have \<open>\<forall>L\<in>set (remove1 L (ys @ xs)). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using L_ys_xs by (auto dest: in_set_remove1D)
  ultimately show ?thesis
    using next_search_L_next
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
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    L: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    to_remove: \<open>to_remove' \<subseteq> to_remove - {L}\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<close>
  shows \<open>(vmtf_en_dequeue M L (ns, m, fst_As, lst_As, next_search), to_remove') \<in> vmtf \<A> M\<close>
  unfolding vmtf_def
proof clarify
  fix xxs yys zzs ns' m' fst_As' lst_As' next_search'
  assume dequeue: \<open>(ns', m', fst_As', lst_As', next_search') =
     vmtf_en_dequeue M L (ns, m, fst_As, lst_As, next_search)\<close>
  obtain xs ys where
    vmtf_ns: \<open>vmtf_ns (ys @ xs) m ns\<close> and
    notin: \<open>vmtf_ns_notin (ys @ xs) m ns\<close> and
    next_search: \<open>next_search = option_hd xs\<close> and
    abs_inv: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs, set ys), to_remove)\<close> and
    fst_As: \<open>fst_As = hd (ys @ xs)\<close> and
    lst_As: \<open>lst_As = last (ys @ xs)\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys @ xs). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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
    next_searchd_hd: \<open>next_searchd = option_hd xs'\<close> and
    next_searchd_L_next:
      \<open>next_searchd = (if next_search = Some L then get_next (ns!L) else next_search)\<close> and
    abs_l: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((insert L (set xs'), set ys'), to_remove)\<close>  and
    not_in: \<open>vmtf_ns_notin (ys' @ xs') md nsd\<close> and
    L_xs'_ys': \<open>L \<notin> set (ys' @ xs')\<close> and
    L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using abs_vmtf_ns_bump_vmtf_dequeue[OF vmtf L de[symmetric] nempty] by blast

  have [simp]: \<open>length ns' = length ns\<close>  \<open>length nsd = length ns\<close>
    using dequeue de unfolding vmtf_en_dequeue_def comp_def vmtf_dequeue_def
    by (auto simp add: vmtf_enqueue_def split: option.splits)
  have nsd: \<open>nsd = ns_vmtf_dequeue L ns\<close>
    using de unfolding vmtf_dequeue_def by auto
  have [simp]: \<open>fst_As = L\<close> if \<open>ys' = []\<close> and \<open>xs' = []\<close>
    proof -
      have 1: \<open>set_mset \<A> = {L}\<close>
        using abs_l unfolding that vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
      show ?thesis
        using vmtf_ns_distinct[OF vmtf_ns] ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l abs_inv
        unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n 1 fst_As vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
        by (cases \<open>ys @ xs\<close>)  auto
    qed
    have fst_As': \<open>fst_As' = L\<close> and m': \<open>m' = md + 1\<close> and
      lst_As': \<open>fst_Asd \<noteq> None \<longrightarrow> lst_As' = the (lst_Asd)\<close>
      \<open>fst_Asd = None \<longrightarrow> lst_As' = L\<close>
      using dequeue unfolding vmtf_en_dequeue_def comp_def de
      by (auto simp add: vmtf_enqueue_def split: option.splits)
    have \<open>lst_As = L\<close> if \<open>ys' = []\<close> and \<open>xs' = []\<close>
    proof -
      have 1: \<open>set_mset \<A> = {L}\<close>
        using abs_l unfolding that vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
      then have \<open>set (ys @ xs) = {L} \<close>
        using vmtf_ns_distinct[OF vmtf_ns] ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l abs_inv
        unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n 1 fst_As vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
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

  consider
     (defined) \<open>defined_lit M (Pos L)\<close> |
     (undef) \<open>undefined_lit M (Pos L)\<close>
    by blast
  then show \<open>\<exists>xs' ys'.
       vmtf_ns (ys' @ xs') m' ns' \<and>
       fst_As' = hd (ys' @ xs') \<and>
       lst_As' = last (ys' @ xs') \<and>
       next_search' = option_hd xs' \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove') \<and>
       vmtf_ns_notin (ys' @ xs') m' ns' \<and>
       (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
  proof cases
    case defined
    have L_in_M: \<open>L \<in> atm_of ` lits_of_l M\<close>
      using defined by (auto simp: defined_lit_map lits_of_def)
    have next_search': \<open>fst_Asd \<noteq> None \<longrightarrow> next_search' = next_searchd\<close>
      \<open>fst_Asd = None \<longrightarrow> next_search' = None\<close>
      using dequeue defined unfolding vmtf_en_dequeue_def comp_def de
      by (auto simp add: vmtf_enqueue_def split: option.splits)
    have next_searchd:
      \<open>next_searchd = (if next_search = Some L then get_next (ns ! L) else next_search)\<close>
      using de by (auto simp: vmtf_dequeue_def)
    have abs': \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M  ((set xs', insert L (set ys')), to_remove')\<close>
      using abs_l to_remove L_in_M L_xs'_ys' unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by (auto 5 5 dest: in_diffD)

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
    have L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l': \<open>\<forall>L'\<in>set ((L # ys') @ xs'). L' \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
      using L L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
    have next_search'_xs': \<open>next_search' = option_hd xs'\<close>
      using next_searchd_L_next next_search' next_searchd_hd lst_As' fst_Asd
      by (auto split: if_splits)
    show ?thesis
      apply (rule exI[of _ \<open>xs'\<close>])
      apply (rule exI[of _ \<open>L # ys'\<close>])
      using fst_As' next_search' abs' atm_A vmtf_ns_notin' vmtf_ns ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l'
        next_searchd next_search'_xs'
      by simp
  next
    case undef
    have next_search': \<open>next_search' = Some L\<close>
      using dequeue undef unfolding vmtf_en_dequeue_def comp_def de
      by (auto simp add: vmtf_enqueue_def split: option.splits)
    have next_searchd:
      \<open>next_searchd = (if next_search = Some L then get_next (ns ! L) else next_search)\<close>
      using de by (auto simp: vmtf_dequeue_def)
    have abs': \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M  ((insert L (set (ys' @ xs')), set []), to_remove')\<close>
      using abs_l to_remove L_xs'_ys' unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by (auto 5 5 dest: in_diffD)

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
    have L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l': \<open>\<forall>L'\<in>set ((L # ys') @ xs'). L' \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
      using L L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
    show ?thesis
      apply (rule exI[of _ \<open>(L # ys') @ xs'\<close>])
      apply (rule exI[of _ \<open>[]\<close>])
      using fst_As' next_search' abs' atm_A vmtf_ns_notin' vmtf_ns ys_xs_\<L>\<^sub>a\<^sub>l\<^sub>l L_xs'_ys'_\<L>\<^sub>a\<^sub>l\<^sub>l'
        next_searchd
      by simp
  qed
qed


lemma abs_vmtf_ns_bump_vmtf_en_dequeue':
  fixes M
  assumes
    vmtf: \<open>(vm, to_remove) \<in> vmtf \<A> M\<close> and
    L: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    to_remove: \<open>to_remove' \<subseteq> to_remove - {L}\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<close>
  shows \<open>(vmtf_en_dequeue M L vm, to_remove') \<in> vmtf \<A> M\<close>
  using abs_vmtf_ns_bump_vmtf_en_dequeue assms by (cases vm) blast

definition (in -) vmtf_unset :: \<open>nat \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int\<close> where
\<open>vmtf_unset = (\<lambda>L ((ns, m, fst_As, lst_As, next_search), to_remove).
  (if next_search = None \<or> stamp (ns ! (the next_search)) < stamp (ns ! L)
  then ((ns, m, fst_As, lst_As, Some L), to_remove)
  else ((ns, m, fst_As, lst_As, next_search), to_remove)))\<close>

lemma vmtf_atm_of_ys_iff:
  assumes
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    L: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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
    using L_xs_ys next_search_xs dist by auto
qed

lemma vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_to_remove_mono:
  assumes
    \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((a, b), to_remove)\<close> and
    \<open>to_remove' \<subseteq> to_remove\<close>
  shows \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((a, b), to_remove')\<close>
  using assms unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: mset_subset_eqD)

lemma abs_vmtf_ns_unset_vmtf_unset:
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
  L_N: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    to_remove: \<open>to_remove' \<subseteq> to_remove\<close>
  shows \<open>(vmtf_unset L ((ns, m, fst_As, lst_As, next_search), to_remove')) \<in> vmtf \<A> M\<close> (is \<open>?S \<in> _\<close>)
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove'') \<and>
       vmtf_ns_notin (ys' @ xs') m' ns' \<and> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
  proof (cases \<open>L \<in> set xs'\<close>)
    case True
    then have C: \<open>\<not>(next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L))\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove'')\<close>
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
      have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set ?xs', set ?ys'), to_remove)\<close>
        using abs_vmtf vmtf_ns_distinct[OF vmtf_ns] unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def ys'_y_x
        by auto
      then have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set ?xs', set ?ys'), to_remove')\<close>
        by (rule vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_to_remove_mono) (use to_remove in auto)
      }
    moreover have \<open>vmtf_ns_notin (?ys' @ ?xs') m ns\<close>
      using notin unfolding ys'_y_x by simp
    moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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

definition vmtf_en_dequeue_pre :: \<open>nat multiset \<Rightarrow> ((nat, nat) ann_lits \<times> nat) \<times> vmtf \<Rightarrow> bool\<close> where
  \<open>vmtf_en_dequeue_pre \<A> = (\<lambda>((M, L),(ns,m,fst_As, lst_As, next_search)).
       L < length ns \<and> vmtf_dequeue_pre (L, ns) \<and>
       fst_As < length ns \<and> (get_next (ns ! fst_As) \<noteq> None \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None) \<and>
       (get_next (ns ! fst_As) = None \<longrightarrow> fst_As = lst_As) \<and>
       m+1 \<le> uint64_max \<and>
       Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>

lemma (in -) id_reorder_remove:
   \<open>(RETURN o id, reorder_remove vm) \<in> \<langle>nat_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>nat_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding reorder_remove_def by (intro frefI nres_relI) auto

lemma vmtf_vmtf_en_dequeue_pre_to_remove:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    i: \<open>A \<in> to_remove\<close> and
    m_le:  \<open>m + 1 \<le> uint64_max\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<close>
  shows \<open>vmtf_en_dequeue_pre \<A> ((M, A), (ns, m, fst_As, lst_As, next_search))\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def by fast
  have [dest]: False if \<open>ys' = []\<close> and \<open>xs' = []\<close>
  proof -
    have 1: \<open>set_mset \<A> = {}\<close>
      using abs_vmtf unfolding that vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    then show ?thesis
      using nempty by auto
  qed

  have \<open>A \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using abs_vmtf i unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  then have remove_i_le_A: \<open>A < length ns\<close> and
    i_L: \<open>Pos A \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
    using atm_A by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atms_of_def)
  moreover have \<open>fst_As < length ns\<close>
    using fst_As atm_A L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l by (cases ys'; cases xs') auto
  moreover have \<open>get_prev (ns ! lst_As) \<noteq> None\<close> if \<open>get_next (ns ! fst_As) \<noteq> None\<close>
    using that vmtf_ns_hd_next[of \<open>hd (ys' @ xs')\<close> \<open>hd (tl (ys' @ xs'))\<close> \<open>tl (tl (ys' @ xs'))\<close>]
      vmtf_ns vmtf_ns_last_prev[of \<open>butlast (ys' @ xs')\<close> \<open>last (ys' @ xs')\<close>]
      vmtf_ns_last_next[of \<open>butlast (ys' @ xs')\<close> \<open>last (ys' @ xs')\<close>]
    by (cases \<open>ys' @ xs'\<close>; cases \<open>tl (ys' @ xs')\<close>)
       (auto simp: fst_As lst_As)
  moreover have \<open>vmtf_dequeue_pre (A, ns)\<close>
  proof -
    have \<open>A < length ns\<close>
      using i abs_vmtf atm_A unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
    moreover have \<open>y < length ns\<close> if get_next: \<open>get_next (ns ! (A)) = Some y\<close> for y
    proof (cases \<open>A \<in> set (ys' @ xs')\<close>)
      case False
      then show ?thesis
        using notin get_next remove_i_le_A by (auto simp: vmtf_ns_notin_def)
    next
      case True
      then obtain zs zs' where zs: \<open>ys' @ xs' = zs' @ [A] @ zs\<close>
        using split_list by fastforce
      moreover have \<open>set (ys' @ xs') = atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
        using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
      ultimately show ?thesis
        using vmtf_ns_last_mid_get_next_option_hd[of zs' A zs m ns] vmtf_ns atm_A get_next
          L_ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding zs by force
    qed
    moreover have \<open>y < length ns\<close> if get_prev: \<open>get_prev (ns ! (A)) = Some y\<close> for y
    proof (cases \<open>A \<in> set (ys' @ xs')\<close>)
      case False
      then show ?thesis
        using notin get_prev remove_i_le_A by (auto simp: vmtf_ns_notin_def)
    next
      case True
      then obtain zs zs' where zs: \<open>ys' @ xs' = zs' @ [A] @ zs\<close>
        using split_list by fastforce
      moreover have \<open>set (ys' @ xs') = atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
        using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
      ultimately show ?thesis
        using vmtf_ns_last_mid_get_prev_option_last[of zs' A zs m ns] vmtf_ns atm_A get_prev
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
    using m_le unfolding vmtf_en_dequeue_pre_def by auto
qed

lemma vmtf_vmtf_en_dequeue_pre_to_remove':
  assumes vmtf: \<open>(vm, to_remove) \<in> vmtf \<A> M\<close> and
    i: \<open>A \<in> to_remove\<close> and \<open>fst (snd vm) + 1 \<le> uint64_max\<close> and
    A: \<open>isasat_input_nempty \<A>\<close>
  shows \<open>vmtf_en_dequeue_pre \<A> ((M, A), vm)\<close>
  using vmtf_vmtf_en_dequeue_pre_to_remove assms
  by (cases vm) auto

lemma wf_vmtf_get_next:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
  shows \<open>wf {(get_next (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}\<close> (is \<open>wf ?R\<close>)
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
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close>
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
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close> and
    n: \<open>next_search \<noteq> None\<close> and
    def_n: \<open>defined_lit M (Pos (the next_search))\<close>
  shows \<open>((ns, m, fst_As, lst_As, get_next (ns!the next_search)), to_remove) \<in> vmtf \<A> M\<close>
  unfolding vmtf_def
proof clarify
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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
    have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set ?xs', set ?ys'), to_remove)\<close>
      using abs_vmtf def_n next_search n vmtf_ns_distinct[OF vmtf_ns]
      unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by (cases xs') auto }
  moreover have \<open>vmtf_ns_notin (?ys' @ ?xs') m ns\<close>
    using notin by auto
  moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
  ultimately show \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m ns \<and>
          fst_As = hd (ys' @ xs') \<and>
          lst_As = last (ys' @ xs') \<and>
          get_next (ns ! the next_search) = option_hd xs' \<and>
          vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove) \<and>
          vmtf_ns_notin (ys' @ xs') m ns \<and>
          (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns) \<and>
          (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
    using atm_A by blast
qed


definition vmtf_find_next_undef :: \<open>nat multiset \<Rightarrow> vmtf_remove_int \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat option) nres\<close> where
\<open>vmtf_find_next_undef \<A> = (\<lambda>((ns, m, fst_As, lst_As, next_search), to_remove) M. do {
    WHILE\<^sub>T\<^bsup>\<lambda>next_search. ((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M \<and>
         (next_search \<noteq> None \<longrightarrow> Pos (the next_search) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<^esup>
      (\<lambda>next_search. next_search \<noteq> None \<and> defined_lit M (Pos (the next_search)))
      (\<lambda>next_search. do {
         ASSERT(next_search \<noteq> None);
         let n = the next_search;
         ASSERT(Pos n \<in># \<L>\<^sub>a\<^sub>l\<^sub>l  \<A>);
         ASSERT (n < length ns);
         RETURN (get_next (ns!n))
        }
      )
      next_search
  })\<close>

lemma vmtf_find_next_undef_ref:
  assumes
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
  shows \<open>vmtf_find_next_undef \<A> ((ns, m, fst_As, lst_As, next_search), to_remove) M
     \<le> \<Down> Id (SPEC (\<lambda>L. ((ns, m, fst_As, lst_As, L), to_remove) \<in> vmtf \<A> M \<and>
        (L = None \<longrightarrow> (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M L)) \<and>
        (L \<noteq> None \<longrightarrow> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close>
    using vmtf unfolding vmtf_def by fast
  have [simp]: \<open>index xs' (hd xs') = 0\<close> if \<open>xs' \<noteq> []\<close> for xs' :: \<open>'a list\<close>
    using that by (cases xs') auto
  have no_next_search_all_defined:
    \<open>((ns', m', fst_As', lst_As', None), remove) \<in> vmtf \<A> M \<Longrightarrow> x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> defined_lit M x\<close>
    for x ns' m' fst_As' lst_As' remove
    by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  have next_search_\<L>\<^sub>a\<^sub>l\<^sub>l:
    \<open>((ns', m', fst_As', lst_As', Some y), remove) \<in> vmtf \<A> M \<Longrightarrow> y \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    for ns' m' fst_As' remove y lst_As'
    by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  have next_search_le_A':
    \<open>((ns', m', fst_As', lst_As', Some y), remove) \<in> vmtf \<A> M \<Longrightarrow> y < length ns'\<close>
    for ns' m' fst_As' remove y lst_As'
    by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        defined_lit_map lits_of_def)
  show ?thesis
    unfolding vmtf_find_next_undef_def
    apply (refine_vcg
       WHILEIT_rule[where R=\<open>{(get_next (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}\<close>])
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

definition vmtf_mark_to_rescore
  :: \<open>nat \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int\<close>
where
  \<open>vmtf_mark_to_rescore L = (\<lambda>((ns, m, fst_As, next_search), to_remove).
     ((ns, m, fst_As, next_search), insert L to_remove))\<close>

lemma vmtf_mark_to_rescore:
  assumes
    L: \<open>L \<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
  shows \<open>vmtf_mark_to_rescore L ((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), insert L to_remove)\<close>
    using abs_vmtf L unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by auto
  ultimately show ?thesis
    unfolding vmtf_def vmtf_mark_to_rescore_def by fast
qed

lemma vmtf_unset_vmtf_tl:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf \<A> M\<close> and
    L_N: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>(vmtf_unset L ((ns, m, fst_As, lst_As, next_search), remove)) \<in> vmtf \<A> (tl M)\<close>
     (is \<open>?S \<in> _\<close>)
proof -
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l  \<A>). L < length ns\<close> and
    ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
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
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (tl M) ((set xs', set ys'), remove'') \<and>
       vmtf_ns_notin (ys' @ xs') m' ns' \<and> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns') \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
  proof (cases \<open>L \<in> set xs'\<close>)
    case True
    then have C[unfolded L_def]: \<open>\<not>(next_search = None \<or> stamp (ns ! the next_search) < stamp (ns ! L))\<close>
      by (subst L_ys'_iff[symmetric]) (use L_ys'_xs' in auto)
    have abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (tl M) ((set xs', set ys'), remove)\<close>
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
      have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set ?xs', set ?ys'), remove)\<close>
        using abs_vmtf dist unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def ys'_y_x
        by auto
      then have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (tl M) ((set ?xs', set ?ys'), remove)\<close>
        using dist L_y_ys unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def ys'_y_x ys'_y_x
        by (cases M) auto
      }
    moreover have \<open>vmtf_ns_notin (?ys' @ ?xs') m ns\<close>
      using notin unfolding ys'_y_x by simp
    moreover have \<open>\<forall>L\<in>set (?ys' @ ?xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
      using ys'_xs'_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding ys'_y_x by simp
    ultimately show ?thesis
      using S False atm_A unfolding vmtf_unset_def L_ys'_xs'[symmetric]
      by (fastforce simp add: C)
  qed
  then show ?thesis
    unfolding vmtf_def S
    by fast
qed

definition vmtf_mark_to_rescore_and_unset :: \<open>nat \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int\<close> where
  \<open>vmtf_mark_to_rescore_and_unset L M = vmtf_mark_to_rescore L (vmtf_unset L M)\<close>

lemma vmtf_append_remove_iff:
  \<open>((ns, m, fst_As, lst_As, next_search), insert L b) \<in> vmtf \<A> M \<longleftrightarrow>
     L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and> ((ns, m, fst_As, lst_As, next_search), b) \<in> vmtf \<A> M\<close>
  (is \<open>?A \<longleftrightarrow> ?L \<and> ?B\<close>)
proof
  assume vmtf: ?A
  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), insert L b)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), b)\<close> and L: ?L
    using abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  ultimately have \<open>vmtf_ns (ys' @ xs') m ns \<and>
       fst_As = hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       lst_As = last (ys' @ xs') \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), b) \<and>
       vmtf_ns_notin (ys' @ xs') m ns \<and> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
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
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), b)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def by fast
  moreover have \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), insert L b)\<close>
    using vmtf abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  ultimately have \<open>vmtf_ns (ys' @ xs') m ns \<and>
       fst_As = hd (ys' @ xs') \<and>
       next_search = option_hd xs' \<and>
       lst_As = last (ys' @ xs') \<and>
       vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), insert L b) \<and>
       vmtf_ns_notin (ys' @ xs') m ns \<and> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns) \<and>
       (\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>))\<close>
      by fast
  then show ?A
    unfolding vmtf_def by fast
qed

lemma vmtf_append_remove_iff':
  \<open>(vm, insert L b) \<in> vmtf \<A> M \<longleftrightarrow>
     L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and> (vm, b) \<in> vmtf \<A> M\<close>
  by (cases vm) (auto simp: vmtf_append_remove_iff)

lemma vmtf_mark_to_rescore_unset:
  fixes M
  defines [simp]: \<open>L \<equiv> atm_of (lit_of (hd M))\<close>
  assumes vmtf:\<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> vmtf \<A> M\<close> and
    L_N: \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and [simp]: \<open>M \<noteq> []\<close>
  shows \<open>(vmtf_mark_to_rescore_and_unset L ((ns, m, fst_As, lst_As, next_search), remove)) \<in> vmtf \<A> (tl M)\<close>
     (is \<open>?S \<in> _\<close>)
  using vmtf_unset_vmtf_tl[OF assms(2-)[unfolded assms(1)]] L_N
  unfolding vmtf_mark_to_rescore_and_unset_def vmtf_mark_to_rescore_def
  by (cases \<open>vmtf_unset (atm_of (lit_of (hd M))) ((ns, m, fst_As, lst_As, next_search), remove)\<close>)
     (auto simp: vmtf_append_remove_iff)


lemma vmtf_insert_sort_nth_code_preD:
  assumes vmtf: \<open>vm \<in> vmtf \<A> M\<close>
  shows \<open>\<forall>x\<in>snd vm. x < length (fst (fst vm))\<close>
proof -
  obtain ns m fst_As lst_As next_search remove where
    vm: \<open>vm = ((ns, m, fst_As, lst_As, next_search), remove)\<close>
    by (cases vm) auto

  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def vm by fast
  show ?thesis
    using atm_A abs_vmtf unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: vm)
qed


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

lemma wf_vmtf_get_prev:
  assumes vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
  shows \<open>wf {(get_prev (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}\<close> (is \<open>wf ?R\<close>)
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
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close>
    using vmtf unfolding vmtf_def by fast
  let ?f0 = \<open>the (f 0)\<close>
  have f_None: \<open>f i \<noteq> None\<close> for i
    using f[of i] by fast
  have f_Suc : \<open>f (Suc n) = get_prev (ns ! the (f n))\<close> for n
    using f[of n] by auto
  have f0_length: \<open>?f0 < length ns\<close>
    using f[of 0] atm_A
    by auto
  have f0_in:  \<open>?f0 \<in> set (ys' @ xs')\<close>
    apply (rule ccontr)
    using notin f_Suc[of 0] f0_length unfolding vmtf_ns_notin_def
    by (auto simp: f_None)
  then obtain i0 where
    i0: \<open>(ys' @ xs') ! i0 = ?f0\<close> \<open>i0 < length (ys' @ xs')\<close>
    by (meson in_set_conv_nth)
  define zs where \<open>zs = ys' @ xs'\<close>
  have H: \<open>ys' @ xs' = take m (ys' @ xs') @ [(ys' @ xs') ! m, (ys' @ xs') ! (m+1)] @
     drop (m+2) (ys' @ xs')\<close>
    if \<open>m + 1 < length (ys' @ xs')\<close>
    for m
    using that
    unfolding zs_def[symmetric]
    apply -
    apply (subst id_take_nth_drop[of m])
    by (auto simp: take_Suc_conv_app_nth Cons_nth_drop_Suc  simp del: append_take_drop_id)

  have \<open>the (f n) = (ys' @ xs') ! (i0 - n) \<and> i0 - n \<ge> 0 \<and> n \<le> i0\<close> for n
  proof (induction n)
    case 0
    then show ?case using i0 by simp
  next
    case (Suc n')
    have i0_le: \<open>n' < i0\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>i0 = n'\<close>
        using Suc by auto
      then have \<open>ys' @ xs' = [the (f n')] @ tl (ys' @ xs')\<close>
        using Suc f0_in
        by (cases \<open>ys' @ xs'\<close>) auto
      then show False
        using vmtf_ns_hd_prev[of \<open>the (f n')\<close> \<open>tl (ys' @ xs')\<close> m ns] vmtf_ns
         f_Suc[of n'] by (auto simp: f_None)
    qed
    have get_prev: \<open>get_prev (ns ! ((ys' @ xs') ! (i0 - (n' +1) + 1))) =
         Some ((ys' @ xs') ! ((i0 - (n' + 1))))\<close>
      apply (rule vmtf_ns_last_mid_get_prev[of \<open>take (i0 - (n' +1)) (ys' @ xs')\<close> _ _
        \<open>drop ((i0 - (n' + 1)) + 2) (ys' @ xs')\<close> m])
      apply (subst H[symmetric])
      subgoal using i0_le i0 by auto
      subgoal using vmtf_ns by simp
      done
    then show ?case
      using f_Suc[of n'] Suc i0_le by auto
  qed
  from this[of \<open>Suc i0\<close>] show False
    by auto
qed

fun update_stamp where
  \<open>update_stamp xs n a = xs[a := VMTF_Node n (get_prev (xs!a)) (get_next (xs!a))]\<close>

definition vmtf_rescale :: \<open>vmtf \<Rightarrow> vmtf nres\<close> where
\<open>vmtf_rescale = (\<lambda>(ns, m, fst_As, lst_As :: nat, next_search). do {
  (ns, m, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
     (\<lambda>(ns, n, lst_As). lst_As \<noteq>None)
     (\<lambda>(ns, n, a). do {
       ASSERT(a \<noteq> None);
       ASSERT(n+1 \<le> uint32_max);
       ASSERT(the a < length ns);
       RETURN (update_stamp ns n (the a), n+1, get_prev (ns ! the a))
     })
     (ns, 0, Some lst_As);
  RETURN ((ns, m, fst_As, lst_As, next_search))
  })
\<close>


lemma vmtf_rescale_vmtf:
  assumes vmtf: \<open>(vm, to_remove) \<in> vmtf \<A> M\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    \<open>vmtf_rescale vm \<le> SPEC (\<lambda>vm. (vm, to_remove) \<in> vmtf \<A> M \<and> fst (snd vm) \<le> uint32_max)\<close>
    (is \<open>?A \<le> ?R\<close>)
proof -
  obtain ns m fst_As lst_As next_search where
    vm: \<open>vm = ((ns, m, fst_As, lst_As, next_search))\<close>
    by (cases vm) auto

  obtain xs' ys' where
    vmtf_ns: \<open>vmtf_ns (ys' @ xs') m ns\<close> and
    fst_As: \<open>fst_As = hd (ys' @ xs')\<close> and
    lst_As: \<open>lst_As = last (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> M ((set xs', set ys'), to_remove)\<close> and
    notin: \<open>vmtf_ns_notin (ys' @ xs') m ns\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length ns\<close> and
    in_lall: \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    using vmtf unfolding vmtf_def vm by fast
  have [dest]: \<open>ys' = [] \<Longrightarrow> xs' = [] \<Longrightarrow> False\<close> and
    [simp]: \<open>ys' = [] \<longrightarrow> xs' \<noteq> []\<close>
    using abs_vmtf nempty unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
  have 1: \<open>RES (vmtf \<A> M) = do {
    a \<leftarrow> RETURN ();
    RES (vmtf \<A> M)
    }\<close>
    by auto
  define zs where \<open>zs \<equiv> ys' @ xs'\<close>

  define I' where
    \<open>I' \<equiv> \<lambda>(ns', n::nat, lst::nat option).
        map get_prev ns = map get_prev ns' \<and>
        map get_next ns = map get_next ns' \<and>
        (\<forall>i<n. stamp (ns' ! (rev zs ! i)) = i) \<and>
        (lst \<noteq> None \<longrightarrow> n < length (zs) \<and> the lst = zs ! (length zs - Suc n)) \<and>
        (lst = None \<longrightarrow> n = length zs) \<and>
          n \<le> length zs\<close>
  have [simp]: \<open>zs \<noteq> []\<close>
    unfolding zs_def by auto
  have I'0: \<open>I' (ns, 0, Some lst_As)\<close>
    using vmtf lst_As unfolding I'_def vm zs_def[symmetric] by (auto simp: last_conv_nth)


  have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (Pos `# mset zs)\<close> and
    dist: \<open>distinct zs\<close>
    using abs_vmtf vmtf_ns_distinct[OF vmtf_ns] unfolding vmtf_def zs_def
      vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def inj_on_def)
  have dist: \<open>distinct_mset (Pos `# mset zs)\<close>
    by (subst distinct_image_mset_inj)
      (use dist in \<open>auto simp: inj_on_def\<close>)
  have tauto: \<open>\<not> tautology (poss (mset zs))\<close>
    by (auto simp: tautology_decomp)

  have length_zs_le:  \<open>length zs < uint32_max\<close> using vmtf_ns_distinct[OF vmtf_ns]
      using simple_clss_size_upper_div2[OF bounded lits dist tauto]
      by (auto simp: uint32_max_def)

  have \<open>wf {(a, b). (a, b) \<in> {(get_prev (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}}\<close>
    by (rule wf_subset[OF wf_vmtf_get_prev[OF vmtf[unfolded vm]]]) auto
  from wf_snd_wf_pair[OF wf_snd_wf_pair[OF this]]
  have wf: \<open>wf {((_, _, a), (_, _, b)). (a, b) \<in> {(get_prev (ns ! the a), a) |a. a \<noteq> None \<and>
      the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}}\<close>
    by (rule wf_subset) auto
  have zs_lall: \<open>zs ! (length zs - Suc n) \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> for n
    using abs_vmtf nth_mem[of \<open>length zs - Suc n\<close> zs] unfolding zs_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by auto
  then have zs_le_ns[simp]: \<open>zs ! (length zs - Suc n) < length ns\<close> for n
    using atm_A by auto
  have loop_body:  \<open>(case s' of
        (ns, n, a) \<Rightarrow> do {
            ASSERT (a \<noteq> None);
            ASSERT (n + 1 \<le> uint_max);
            ASSERT(the a < length ns);
            RETURN (update_stamp ns n (the a), n + 1, get_prev (ns ! the a))
          })
        \<le> SPEC
          (\<lambda>s'a. True \<and>
                  I' s'a \<and>
                  (s'a, s')
                  \<in> {((_, _, a), _, _, b).
                    (a, b)
                    \<in> {(get_prev (ns ! the a), a) |a.
                        a \<noteq> None \<and> the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}})\<close>
    if
      I': \<open>I' s'\<close> and
      cond: \<open>case s' of (ns, n, lst_As) \<Rightarrow> lst_As \<noteq> None\<close>
    for s'
  proof -
    obtain ns' n' a' where s': \<open>s' = (ns', n' , a')\<close>
      by (cases s')
    have
      a[simp]: \<open>a' = Some (zs ! (length zs - Suc n'))\<close> and
      eq_prev: \<open>map get_prev ns = map get_prev ns'\<close> and
      eq_next: \<open>map get_next ns = map get_next ns'\<close> and
      eq_stamps: \<open>\<And>i. i<n' \<Longrightarrow> stamp (ns' ! (rev zs ! i)) = i\<close> and
      n'_le: \<open>n' < length zs\<close>
      using I' cond unfolding I'_def prod.simps s'
      by auto
    have [simp]: \<open>length ns' = length ns\<close>
      using arg_cong[OF eq_prev, of length] by auto
    have vmtf_as: \<open>vmtf_ns
      (take (length zs - (n' + 1)) zs @
       zs ! (length zs - (n' + 1)) #
       drop (Suc (length zs - (n' + 1))) zs)
      m ns\<close>
      apply (subst Cons_nth_drop_Suc)
      subgoal by auto
      apply (subst append_take_drop_id)
      using vmtf_ns unfolding zs_def[symmetric] .

    have \<open>get_prev (ns' ! the a') \<noteq> None \<longrightarrow>
        n' + 1 < length zs \<and>
        the (get_prev (ns' ! the a')) = zs ! (length zs - Suc (n' + 1))\<close>
      using n'_le vmtf_ns arg_cong[OF eq_prev, of \<open>\<lambda>xs. xs ! (zs ! (length zs - Suc n'))\<close>]
        vmtf_ns_last_mid_get_prev_option_last[OF vmtf_as]
      by (auto simp: last_conv_nth)
    moreover have \<open>map get_prev ns = map get_prev (update_stamp ns' n' (the a'))\<close>
      unfolding update_stamp.simps
      apply (subst map_update)
      apply (subst list_update_id')
      subgoal by auto
      subgoal using eq_prev .
      done
    moreover have \<open>map get_next ns = map get_next (update_stamp ns' n' (the a'))\<close>
      unfolding update_stamp.simps
      apply (subst map_update)
      apply (subst list_update_id')
      subgoal by auto
      subgoal using eq_next .
      done
    moreover have \<open>i<n' + 1 \<Longrightarrow> stamp (update_stamp ns' n' (the a') ! (rev zs ! i)) = i\<close> for i
      using eq_stamps[of i] vmtf_ns_distinct[OF vmtf_ns] n'_le
      unfolding zs_def[symmetric]
      by (cases \<open>i < n'\<close>)
        (auto simp: rev_nth nth_eq_iff_index_eq)
    moreover have \<open>n' + 1 \<le> length zs\<close>
     using n'_le by (auto simp: Suc_le_eq)
    moreover have \<open>get_prev (ns' ! the a') = None \<Longrightarrow> n' + 1 = length zs\<close>
      using n'_le vmtf_ns arg_cong[OF eq_prev, of \<open>\<lambda>xs. xs ! (zs ! (length zs - Suc n'))\<close>]
        vmtf_ns_last_mid_get_prev_option_last[OF vmtf_as]
      by auto
    ultimately have I'_f: \<open>I' (update_stamp ns' n' (the a'), n' + 1, get_prev (ns' ! the a'))\<close>
      using cond n'_le unfolding I'_def prod.simps s'
      by simp

    show ?thesis
      unfolding s' prod.case
      apply refine_vcg
      subgoal using cond by auto
      subgoal using length_zs_le n'_le by auto
      subgoal by auto
      subgoal by fast
      subgoal by (rule I'_f)
      subgoal
        using arg_cong[OF eq_prev, of \<open>\<lambda>xs. xs ! (zs ! (length zs - Suc n'))\<close>] zs_lall
        by auto
      done
  qed
  have loop_final: \<open>s \<in> {x. (case x of
                (ns, m, uua_) \<Rightarrow>
                  RETURN ((ns, m, fst_As, lst_As, next_search)))
                \<le> ?R}\<close>
    if
      \<open>True\<close> and
      \<open>I' s\<close> and
      \<open>\<not> (case s of (ns, n, lst_As) \<Rightarrow> lst_As \<noteq> None)\<close>
    for s
  proof -
    obtain ns' n' a' where s: \<open>s = (ns', n' , a')\<close>
      by (cases s)
    have
      [simp]:\<open>a' = None\<close> and
      eq_prev: \<open>map get_prev ns = map get_prev ns'\<close> and
      eq_next: \<open>map get_next ns = map get_next ns'\<close> and
      stamp: \<open>\<forall>i<n'. stamp (ns' ! (rev zs ! i)) = i\<close> and
      [simp]: \<open>n' = length zs\<close>
      using that unfolding I'_def s prod.case by auto
    have [simp]: \<open>length ns' = length ns\<close>
      using arg_cong[OF eq_prev, of length] by auto
    have [simp]: \<open>map ((!) (map stamp ns')) (rev zs) = [0..<length zs]\<close>
      apply (subst list_eq_iff_nth_eq, intro conjI)
      subgoal by auto
      subgoal using stamp by (auto simp: rev_nth)
      done
    then have stamps_zs[simp]: \<open>map ((!) (map stamp ns')) zs = rev [0..<length zs]\<close>
        unfolding rev_map[symmetric]
        using rev_swap by blast

    have \<open>sorted (map ((!) (map stamp ns')) (rev zs))\<close>
      by simp
    moreover have \<open>distinct (map ((!) (map stamp ns')) zs)\<close>
      by simp
    moreover have \<open>\<forall>a\<in>set zs. get_prev (ns' ! a) = get_prev (ns ! a)\<close>
      using eq_prev map_eq_nth_eq by fastforce
    moreover have \<open>\<forall>a\<in>set zs. get_next (ns' ! a) = get_next (ns ! a)\<close>
      using eq_next map_eq_nth_eq by fastforce
    moreover have \<open>\<forall>a\<in>set zs. stamp (ns' ! a) = map stamp ns' ! a\<close>
      using vmtf_ns vmtf_ns_le_length zs_def by auto
    moreover have \<open>length ns \<le> length ns'\<close>
     by simp
    moreover have \<open>\<forall>a\<in>set zs. a < length (map stamp ns')\<close>
      using vmtf_ns vmtf_ns_le_length zs_def by auto
    moreover have \<open>\<forall>a\<in>set zs. map stamp ns' ! a < n'\<close>
    proof
      fix a
      assume \<open>a \<in> set zs\<close>
      then have \<open>map stamp ns' ! a \<in> set (map ((!) (map stamp ns')) zs)\<close>
        by (metis in_set_conv_nth length_map nth_map)
      then show \<open>map stamp ns' ! a < n'\<close>
        unfolding stamps_zs by simp
    qed
    ultimately have \<open>vmtf_ns zs n' ns'\<close>
      using vmtf_ns_rescale[OF vmtf_ns, of \<open>map stamp ns'\<close> ns', unfolded zs_def[symmetric]]
      by fast
    moreover have \<open>vmtf_ns_notin zs (length zs) ns'\<close>
      using notin map_eq_nth_eq[OF eq_prev] map_eq_nth_eq[OF eq_next]
      unfolding zs_def[symmetric]
      by (auto simp: vmtf_ns_notin_def)
    ultimately have \<open>((ns', n', fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A> M\<close>
      using fst_As lst_As next_search abs_vmtf atm_A notin in_lall
      unfolding vmtf_def in_pair_collect_simp prod.case apply -
      apply (rule exI[of _ xs'])
      apply (rule exI[of _ ys'])
      unfolding zs_def[symmetric]
      by auto
    then show ?thesis
      using length_zs_le
      by (auto simp: s)
  qed

  have H: \<open>WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup> (\<lambda>(ns, n, lst_As). lst_As \<noteq> None)
     (\<lambda>(ns, n, a). do {
           _ \<leftarrow> ASSERT (a \<noteq> None);
           _ \<leftarrow> ASSERT (n + 1 \<le> uint_max);
           ASSERT(the a < length ns);
           RETURN (update_stamp ns n (the a), n + 1, get_prev (ns ! the a))
         })
     (ns, 0, Some lst_As)
    \<le> SPEC
       (\<lambda>x. (case x of
             (ns, m, uua_) \<Rightarrow>
               RETURN ((ns, m, fst_As, lst_As, next_search)))
            \<le> ?R)
  \<close>
  apply (rule WHILEIT_rule_stronger_inv_RES[where I' = I' and
      R = \<open>{((_, _, a), (_, _, b)). (a, b) \<in>
         {(get_prev (ns ! the a), a) |a. a \<noteq> None \<and> the a \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)}}\<close>])
  subgoal
   by (rule wf)
  subgoal by fast
  subgoal by (rule I'0)
  subgoal for s'
    by (rule loop_body)
  subgoal for s
    by (rule loop_final)
  done

  show ?thesis
    unfolding vmtf_rescale_def vm prod.case
    apply (subst bind_rule_complete_RES)
    apply (rule H)
    done
qed

definition vmtf_flush
   :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int nres\<close>
where
  \<open>vmtf_flush \<A>\<^sub>i\<^sub>n = (\<lambda>M (vm, to_remove). RES (vmtf \<A>\<^sub>i\<^sub>n M))\<close>

definition atoms_hash_rel :: \<open>nat multiset \<Rightarrow> (bool list \<times> nat set) set\<close> where
  \<open>atoms_hash_rel \<A> = {(C, D). (\<forall>L \<in> D. L < length C) \<and> (\<forall>L < length C. C ! L \<longleftrightarrow> L \<in> D) \<and>
    (\<forall>L \<in># \<A>. L < length C)}\<close>

definition distinct_hash_atoms_rel
  :: \<open>nat multiset \<Rightarrow> (('v list \<times> 'v set) \<times> 'v set) set\<close>
where
  \<open>distinct_hash_atoms_rel \<A> = {((C, h), D). set C = D \<and> h = D \<and> distinct C}\<close>

definition distinct_atoms_rel
  :: \<open>nat multiset \<Rightarrow> ((nat list \<times> bool list) \<times> nat set) set\<close>
where
  \<open>distinct_atoms_rel \<A> = (Id \<times>\<^sub>r atoms_hash_rel \<A>) O distinct_hash_atoms_rel \<A>\<close>

lemma distinct_atoms_rel_alt_def:
  \<open>distinct_atoms_rel \<A> = {((D', C), D). (\<forall>L \<in> D. L < length C) \<and> (\<forall>L < length C. C ! L \<longleftrightarrow> L \<in> D) \<and>
    (\<forall>L \<in># \<A>. L < length C) \<and> set D' = D \<and> distinct D'}\<close>
  unfolding distinct_atoms_rel_def atoms_hash_rel_def distinct_hash_atoms_rel_def prod_rel_def
  apply rule
  subgoal
    by auto
  subgoal
    by auto
  done

lemma distinct_atoms_rel_empty_hash_iff:
  \<open>(([], h), {}) \<in> distinct_atoms_rel \<A> \<longleftrightarrow>  (\<forall>L \<in># \<A>. L < length h) \<and> (\<forall>i\<in>set h. i = False)\<close>
  unfolding distinct_atoms_rel_alt_def all_set_conv_nth
  by auto

definition atoms_hash_del_pre where
  \<open>atoms_hash_del_pre i xs = (i < length xs)\<close>

definition atoms_hash_del where
\<open>atoms_hash_del i xs = xs[i := False]\<close>


definition vmtf_flush_int :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> _ \<Rightarrow> _ nres\<close> where
\<open>vmtf_flush_int \<A>\<^sub>i\<^sub>n = (\<lambda>M (vm, (to_remove, h)). do {
    ASSERT(\<forall>x\<in>set to_remove. x < length (fst vm));
    ASSERT(length to_remove \<le> uint32_max);
    to_remove' \<leftarrow> reorder_remove vm to_remove;
    ASSERT(length to_remove' \<le> uint32_max);
    vm \<leftarrow> (if length to_remove' + fst (snd vm) \<ge> uint64_max
      then vmtf_rescale vm else RETURN vm);
    ASSERT(length to_remove' + fst (snd vm) \<le> uint64_max);
    (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> length to_remove' \<and> fst (snd vm') = i + fst (snd vm) \<and>
          (i < length to_remove' \<longrightarrow> vmtf_en_dequeue_pre \<A>\<^sub>i\<^sub>n ((M, to_remove'!i), vm'))\<^esup>
      (\<lambda>(i, vm, h). i < length to_remove')
      (\<lambda>(i, vm, h). do {
         ASSERT(i < length to_remove');
         ASSERT(to_remove'!i \<in># \<A>\<^sub>i\<^sub>n);
         ASSERT(atoms_hash_del_pre (to_remove'!i) h);
         RETURN (i+1, vmtf_en_dequeue M (to_remove'!i) vm, atoms_hash_del (to_remove'!i) h)})
      (0, vm, h);
    RETURN (vm, (emptied_list to_remove', h))
  })\<close>


lemma vmtf_change_to_remove_order:
  assumes
    vmtf: \<open>((ns, m, fst_As, lst_As, next_search), to_remove) \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close> and
    CD_rem: \<open>((C, D), to_remove) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<^sub>i\<^sub>n\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close>
  shows \<open>vmtf_flush_int \<A>\<^sub>i\<^sub>n M ((ns, m, fst_As, lst_As, next_search), (C, D))
    \<le> \<Down>(Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n)
       (vmtf_flush \<A>\<^sub>i\<^sub>n M ((ns, m, fst_As, lst_As, next_search), to_remove))\<close>
proof -
  let ?vm = \<open>((ns, m, fst_As, lst_As, next_search), to_remove)\<close>
  have vmtf_flush_alt_def: \<open>vmtf_flush \<A>\<^sub>i\<^sub>n M ?vm = do {
     _ \<leftarrow> RETURN ();
     _ \<leftarrow> RETURN ();
     vm \<leftarrow> RES(vmtf \<A>\<^sub>i\<^sub>n M);
     RETURN (vm)
  }\<close>
    unfolding vmtf_flush_def by (auto simp: RES_RES_RETURN_RES RES_RETURN_RES vmtf)

  have pre_sort: \<open>\<forall>x\<in>set x1a. x < length (fst x1)\<close>
    if
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>((ns, m, fst_As, lst_As, next_search), C, D) = (x1, x2)\<close>
    for x1 x2 x1a x2a
  proof -
    show ?thesis
      using vmtf CD_rem that by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
        distinct_atoms_rel_alt_def)
  qed

  have length_le: \<open>length x1a \<le> uint32_max\<close>
    if
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>((ns, m, fst_As, lst_As, next_search), C, D) = (x1, x2)\<close> and
      \<open>\<forall>x\<in>set x1a. x < length (fst x1)\<close>
      for x1 x2 x1a x2a
  proof -
    have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (Pos `# mset x1a)\<close> and
      dist: \<open>distinct x1a\<close>
      using that vmtf CD_rem unfolding vmtf_def
        vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def distinct_atoms_rel_alt_def inj_on_def)
    have dist: \<open>distinct_mset (Pos `# mset x1a)\<close>
      by (subst distinct_image_mset_inj)
        (use dist in \<open>auto simp: inj_on_def\<close>)
    have tauto: \<open>\<not> tautology (poss (mset x1a))\<close>
      by (auto simp: tautology_decomp)

    show ?thesis
      using simple_clss_size_upper_div2[OF bounded lits dist tauto]
      by (auto simp: uint32_max_def)
  qed


  have [refine0]:
     \<open>reorder_remove x1 x1a \<le> SPEC (\<lambda>c. (c, ()) \<in>
        {(c, c'). ((c, D), to_remove) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n \<and> to_remove = set c \<and>
           length C = length c})\<close>
     (is \<open>_ \<le> SPEC(\<lambda>_. _ \<in> ?reorder_remove)\<close>)
    if
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>((ns, m, fst_As, lst_As, next_search), C, D) = (x1, x2)\<close>
    for x1 x2 x1a x2a
  proof -
    show ?thesis
      using that assms by (auto simp: reorder_remove_def distinct_atoms_rel_alt_def
        dest: mset_eq_setD same_mset_distinct_iff mset_eq_length)
  qed


  have [refine0]: \<open>(if uint64_max \<le> length to_remove' + fst (snd x1) then vmtf_rescale x1
      else RETURN x1)
      \<le> SPEC (\<lambda>c. (c, ()) \<in>
        {(vm ,vm'). uint64_max \<ge> length to_remove' + fst (snd vm) \<and>
          (vm, set to_remove') \<in> vmtf \<A>\<^sub>i\<^sub>n M}) \<close>
    (is \<open>_ \<le> SPEC(\<lambda>c. (c, ()) \<in> ?rescale)\<close> is \<open>_ \<le> ?H\<close>)
  if
    \<open>x2 = (x1a, x2a)\<close> and
    \<open>((ns, m, fst_As, lst_As, next_search), C, D) = (x1, x2)\<close> and
    \<open>\<forall>x\<in>set x1a. x < length (fst x1)\<close> and
    \<open>length x1a \<le> uint_max\<close> and
    \<open>(to_remove', uu) \<in> ?reorder_remove\<close> and
    \<open>length to_remove' \<le> uint_max\<close>
  for x1 x2 x1a x2a to_remove' uu
  proof -
    have \<open>vmtf_rescale x1 \<le> ?H\<close>
      apply (rule order_trans)
      apply (rule vmtf_rescale_vmtf[of _ to_remove \<A>\<^sub>i\<^sub>n M])
      subgoal using vmtf that by auto
      subgoal using nempty by fast
      subgoal using bounded by fast
      subgoal using that by (auto intro!: RES_refine simp: uint64_max_def uint32_max_def)
      done
    then show ?thesis
      using that vmtf
      by (auto intro!: RETURN_RES_refine)
  qed


  have loop_ref: \<open>WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h).
                  i \<le> length to_remove' \<and> fst (snd vm') = i + fst (snd x1) \<and>
                  (i < length to_remove' \<longrightarrow>
                    vmtf_en_dequeue_pre \<A>\<^sub>i\<^sub>n ((M, to_remove' ! i), vm'))\<^esup>
        (\<lambda>(i, vm, h). i < length to_remove')
        (\<lambda>(i, vm, h). do {
              ASSERT (i < length to_remove');
              ASSERT(to_remove'!i \<in># \<A>\<^sub>i\<^sub>n);
              ASSERT(atoms_hash_del_pre (to_remove'!i) h);
              RETURN
                (i + 1, vmtf_en_dequeue M (to_remove' ! i) vm,
                atoms_hash_del (to_remove'!i) h)
            })
        (0, x1, x2a)
        \<le> \<Down> {((i, vm::vmtf, h:: _), vm'). (vm, {}) = vm' \<and> (\<forall>i\<in>set h. i = False) \<and> i = length to_remove' \<and>
               ((drop i to_remove', h), set(drop i to_remove')) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n}
	    (RES (vmtf \<A>\<^sub>i\<^sub>n M))\<close>
    if
      x2: \<open>x2 = (x1a, x2a)\<close> and
      CD: \<open>((ns, m, fst_As, lst_As, next_search), C, D) = (x1', x2)\<close> and
      x1: \<open>(x1, u') \<in> ?rescale to_remove'\<close>
      \<open>(to_remove', u) \<in> ?reorder_remove\<close>
    for x1 x2 x1a x2a to_remove' u u' x1'
  proof -
    define I where \<open>I \<equiv> \<lambda>(i, vm'::vmtf, h::bool list).
                  i \<le> length to_remove' \<and> fst (snd vm') = i + fst (snd x1) \<and>
                  (i < length to_remove' \<longrightarrow>
                    vmtf_en_dequeue_pre \<A>\<^sub>i\<^sub>n ((M, to_remove' ! i), vm'))\<close>
    define I' where \<open>I' \<equiv> \<lambda>(i, vm::vmtf, h:: bool list).
       ((drop i to_remove', h), set(drop i to_remove')) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n \<and>
              (vm, set (drop i to_remove')) \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close>
    have [simp]:
        \<open>x2 = (C, D)\<close>
        \<open>x1' = (ns, m, fst_As, lst_As, next_search)\<close>
        \<open>x1a = C\<close>
        \<open>x2a = D\<close> and
      rel: \<open>((to_remove', D), to_remove) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<close> and
      to_rem: \<open>to_remove = set to_remove'\<close>
      using that by (auto simp: )
    have D: \<open>set to_remove' = to_remove\<close> and dist: \<open>distinct to_remove'\<close>
      using rel unfolding distinct_atoms_rel_alt_def by auto
    have in_lall: \<open>to_remove' ! x1 \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close> if le': \<open>x1 < length to_remove'\<close> for x1
      using vmtf to_rem nth_mem[OF le'] by (auto simp: vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    have bound: \<open>fst (snd x1) + 1 \<le> uint64_max\<close> if \<open>0 < length to_remove'\<close>
        using rel vmtf to_rem that x1 by (cases to_remove') auto
    have I_init: \<open>I (0, x1, x2a)\<close> (is ?A)
      for x1a x2 x1aa x2aa
    proof -
      have \<open>vmtf_en_dequeue_pre \<A>\<^sub>i\<^sub>n ((M, to_remove' ! 0), x1)\<close> if \<open>0 < length to_remove'\<close>
        apply (rule vmtf_vmtf_en_dequeue_pre_to_remove'[of _ \<open>set to_remove'\<close>])
        using rel vmtf to_rem that x1 bound nempty by auto
      then show ?A
        unfolding I_def by auto
    qed
    have I'_init: \<open>I' (0, x1, x2a)\<close> (is ?B)
      for x1a x2 x1aa x2aa
    proof -
      show ?B
        using rel to_rem CD_rem that vmtf by (auto simp: distinct_atoms_rel_def I'_def)
    qed
    have post_loop: \<open>do {
            ASSERT (x2 < length to_remove');
            ASSERT(to_remove' ! x2 \<in># \<A>\<^sub>i\<^sub>n);
            ASSERT(atoms_hash_del_pre (to_remove' ! x2) x2a');
            RETURN
              (x2 + 1, vmtf_en_dequeue M (to_remove' ! x2) x2aa,
                  atoms_hash_del (to_remove'!x2) x2a')
          } \<le> SPEC
              (\<lambda>s'. I s' \<and> I' s' \<and> (s', x1a) \<in> measure (\<lambda>(i, vm, h). Suc (length to_remove') - i))\<close>
      if
        I: \<open>I x1a\<close> and
        I': \<open>I' x1a\<close> and
        \<open>case x1a of (i, vm, h) \<Rightarrow> i < length to_remove'\<close> and
        x1aa: \<open>x1aa = (x2aa, x2a')\<close> \<open>x1a = (x2, x1aa)\<close>
      for s x2 x1a x2a x1a' x2a' x1aa x2aa
    proof -
      let ?x2a' = \<open>set (drop x2 to_remove')\<close>
      have le: \<open>x2 < length to_remove'\<close> and vm: \<open>(x2aa, set (drop x2 to_remove')) \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close> and
        x2a': \<open>fst (snd x2aa) = x2 + fst (snd x1)\<close>
        using that unfolding I_def I'_def by (auto simp: distinct_atoms_rel_alt_def)
      have 1: \<open>(vmtf_en_dequeue M (to_remove' ! x2) x2aa, ?x2a'- {to_remove' ! x2}) \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close>
        by (rule abs_vmtf_ns_bump_vmtf_en_dequeue'[OF vm in_lall[OF le]])
          (use nempty in auto)
      have 2: \<open>to_remove' ! Suc x2 \<in> ?x2a'- {to_remove' ! x2}\<close>
        if \<open>Suc x2 < length to_remove'\<close>
        using I I' le dist that x1aa unfolding I_def I'_def
         by (auto simp: distinct_atoms_rel_alt_def in_set_drop_conv_nth I'_def
             nth_eq_iff_index_eq x2 intro: bex_geI[of _ \<open>Suc x2\<close>])
      have 3: \<open>fst (snd x2aa) = fst (snd x1) + x2\<close>
        using I I' le dist that CD[unfolded x2] x2a' unfolding I_def I'_def x2 x2a' x1aa
         by (auto simp: distinct_atoms_rel_def in_set_drop_conv_nth I'_def
             nth_eq_iff_index_eq x2 intro: bex_geI[of _ \<open>Suc x2\<close>])
      then have 4: \<open>fst (snd (vmtf_en_dequeue M (to_remove' ! x2) x2aa)) + 1 \<le> uint64_max\<close>
        if \<open>Suc x2 < length to_remove'\<close>
        using x1 le that
        by (cases x2aa)
          (auto simp: vmtf_en_dequeue_def vmtf_enqueue_def vmtf_dequeue_def
          split: option.splits)
      have 1: \<open>vmtf_en_dequeue_pre \<A>\<^sub>i\<^sub>n
          ((M, to_remove' ! Suc x2), vmtf_en_dequeue M (to_remove' ! x2) x2aa)\<close>
        if \<open>Suc x2 < length to_remove'\<close>
        by (rule vmtf_vmtf_en_dequeue_pre_to_remove')
         (rule 1, rule 2, rule that, rule 4[OF that], rule nempty)
      have 3: \<open>(vmtf_en_dequeue M (to_remove' ! x2) x2aa, ?x2a' - {to_remove' ! x2}) \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close>
        by (rule abs_vmtf_ns_bump_vmtf_en_dequeue'[OF vm in_lall[OF le]]) (use nempty in auto)
      have 4: \<open>((drop (Suc x2) to_remove', atoms_hash_del (to_remove' ! x2) x2a'),
            set (drop (Suc x2) to_remove'))
        \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<close> and
        3: \<open>(vmtf_en_dequeue M (to_remove' ! x2) x2aa, set (drop (Suc x2) to_remove'))
         \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close>
        using 3 I' le to_rem that unfolding I'_def distinct_atoms_rel_alt_def atoms_hash_del_def
        by (auto simp: Cons_nth_drop_Suc[symmetric])

      have A: \<open>to_remove' ! x2 \<in> ?x2a'\<close>
        using I I' le dist that x1aa unfolding I_def I'_def
        by (auto simp: distinct_atoms_rel_def in_set_drop_conv_nth I'_def
             nth_eq_iff_index_eq x2 x2a' intro: bex_geI[of _ \<open>x2\<close>])
      moreover have \<open>I (Suc x2, vmtf_en_dequeue M (to_remove' ! x2) x2aa,
          atoms_hash_del (to_remove' ! x2) x2a')\<close>
        using that 1 unfolding I_def
        by (cases x2aa)
          (auto simp: vmtf_en_dequeue_def vmtf_enqueue_def vmtf_dequeue_def
          split: option.splits)
      moreover have \<open>length to_remove' - x2 < Suc (length to_remove') - x2\<close>
        using le by auto
      moreover have \<open>I' (Suc x2, vmtf_en_dequeue M (to_remove' ! x2) x2aa,
          atoms_hash_del (to_remove' ! x2) x2a')\<close>
        using that 3 4 I' unfolding I'_def
        by auto
      moreover have \<open>atoms_hash_del_pre (to_remove' ! x2) x2a'\<close>
        unfolding atoms_hash_del_pre_def
        using that le A unfolding I_def I'_def by (auto simp: distinct_atoms_rel_alt_def)
      ultimately show ?thesis
        using that in_lall[OF le]
        by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    qed
    have [simp]: \<open>\<forall>L<length ba. \<not> ba ! L \<Longrightarrow>  True \<notin> set ba\<close> for ba
      by (simp add: in_set_conv_nth)
    have post_rel: \<open>RETURN s
        \<le> \<Down> {((i, vm, h), vm').
             (vm, {}) = vm' \<and>
             (\<forall>i\<in>set h. i = False) \<and>
             i = length to_remove' \<and>
             ((drop i to_remove', h), set (drop i to_remove'))
             \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n}           (RES (vmtf \<A>\<^sub>i\<^sub>n M))\<close>
        if
         \<open>\<not> (case s of (i, vm, h) \<Rightarrow> i < length to_remove')\<close> and
         \<open>I s\<close> and
         \<open>I' s\<close>
       for s
    proof -
      obtain i vm h where s: \<open>s = (i, vm, h)\<close> by (cases s)
      have [simp]: \<open>i = length (to_remove')\<close> and [iff]: \<open>True \<notin> set h\<close> and
        [simp]: \<open>(([], h), {}) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<close>
          \<open>(vm, {}) \<in> vmtf \<A>\<^sub>i\<^sub>n M\<close>
        using that unfolding s I_def I'_def by (auto simp: distinct_atoms_rel_empty_hash_iff)
      show ?thesis
        unfolding s
        by (rule RETURN_RES_refine) auto
    qed

    show ?thesis
      unfolding I_def[symmetric]
      apply (refine_rcg
        WHILEIT_rule_stronger_inv_RES'[where R=\<open>measure (\<lambda>(i, vm::vmtf, h). Suc (length to_remove') -i)\<close> and
            I'=\<open>I'\<close>])
      subgoal by auto
      subgoal by (rule I_init)
      subgoal by (rule I'_init)
      subgoal for x1'' x2'' x1a'' x2a'' by (rule post_loop)
      subgoal by (rule post_rel)
      done
  qed


  show ?thesis
    unfolding vmtf_flush_int_def vmtf_flush_alt_def
    apply (refine_rcg)
    subgoal by (rule pre_sort)
    subgoal by (rule length_le)
    apply (assumption+)[2]
    subgoal by auto
    apply (assumption+)[5]
    subgoal by auto
    apply (rule loop_ref; assumption)
    subgoal by (auto simp: emptied_list_def)
    done
qed

lemma vmtf_change_to_remove_order':
  \<open>(uncurry (vmtf_flush_int \<A>\<^sub>i\<^sub>n), uncurry (vmtf_flush \<A>\<^sub>i\<^sub>n)) \<in>
   [\<lambda>(M, vm). vm \<in> vmtf \<A>\<^sub>i\<^sub>n M \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n \<and> isasat_input_nempty \<A>\<^sub>i\<^sub>n]\<^sub>f
     Id \<times>\<^sub>r (Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n) \<rightarrow> \<langle>(Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n)\<rangle> nres_rel\<close>
  unfolding PR_CONST_def
  by (intro frefI nres_relI)
    (use vmtf_change_to_remove_order in auto)


subsection \<open>Phase saving\<close>

type_synonym phase_saver = \<open>bool list\<close>

definition phase_saving :: \<open>nat multiset \<Rightarrow> phase_saver \<Rightarrow> bool\<close> where
\<open>phase_saving \<A> \<phi> \<longleftrightarrow> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length \<phi>)\<close>

text \<open>Save phase as given (e.g. for literals in the trail):\<close>
definition save_phase :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase L \<phi> = \<phi>[atm_of L := is_pos L]\<close>

lemma phase_saving_save_phase[simp]:
  \<open>phase_saving \<A> (save_phase L \<phi>) \<longleftrightarrow> phase_saving \<A> \<phi>\<close>
  by (auto simp: phase_saving_def save_phase_def)

text \<open>Save opposite of the phase (e.g. for literals in the conflict clause):\<close>
definition save_phase_inv :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase_inv L \<phi> = \<phi>[atm_of L := \<not>is_pos L]\<close>

end
