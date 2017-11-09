(*  Title:       Theorem Proving Processes
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Theorem Proving Processes\<close>

theory Proving_Process
  imports Unordered_Ground_Resolution Lazy_List_Liminf "HOL-Library.BNF_Corec"
begin

text \<open>
This material corresponds to Section 4.1 (``Theorem Proving Processes'') of Bachmair and Ganzinger's
chapter.
\<close>


(* FIXME: move chains into their own file, Lazy_List_Chain.thy perhaps *)
subsection \<open>Chains\<close>

coinductive chain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
	singleton: "chain R (LCons x LNil)"
| cons: "chain R xs \<Longrightarrow> R x (lhd xs) \<Longrightarrow> chain R (LCons x xs)"

lemma
  chain_LNil[simp]: "\<not> chain R LNil" and
  lnull_chain: "lnull xs \<Longrightarrow> \<not> chain R xs"
  by (auto elim: chain.cases)

lemma chain_lappend:
  assumes
    r_xs: "chain R xs" and
    r_ys: "chain R ys" and
    mid: "R (llast xs) (lhd ys)"
  shows "chain R (lappend xs ys)"
proof (cases "lfinite xs")
  case True
  then show ?thesis
    using r_xs mid
  proof (induct rule: lfinite.induct)
    case (lfinite_LConsI xs x)
    note fin = this(1) and ih = this(2) and r_xxs = this(3) and mid = this(4)
    show ?case
    proof (cases "xs = LNil")
      case True
      then show ?thesis
        using r_ys mid by simp (rule cons)
    next
      case xs_nnil: False
      have r_xs: "chain R xs"
        by (metis chain.simps ltl_simps(2) r_xxs xs_nnil)
      have mid': "R (llast xs) (lhd ys)"
        by (metis llast_LCons lnull_def mid xs_nnil)
      have start: "R x (lhd (lappend xs ys))"
        by (metis (no_types) chain.simps lhd_LCons lhd_lappend lnull_chain ltl_simps(2) r_xxs
            xs_nnil)
      show ?thesis
        unfolding lappend_code(2) using ih[OF r_xs mid'] start by (rule cons)
    qed
  qed simp
next
  case False
  then show ?thesis
    by (simp add: r_xs lappend_inf)
qed

lemma chain_length_pos: "chain R xs \<Longrightarrow> llength xs > 0"
  by (cases xs) simp+

lemma chain_ldropn:
  assumes "chain R xs" and "enat n < llength xs"
  shows "chain R (ldropn n xs)"
  using assms
  by (induct n arbitrary: xs, simp,
      metis chain.cases ldrop_eSuc_ltl ldropn_LNil ldropn_eq_LNil ltl_simps(2) not_less)

lemma chain_lnth_rel:
  assumes
    deriv: "chain R xs" and
    len: "enat (Suc j) < llength xs"
  shows "R (lnth xs j) (lnth xs (Suc j))"
proof -
  define ys where "ys = ldropn j xs"
  have "llength ys > 1"
    unfolding ys_def using len
    by (metis One_nat_def funpow_swap1 ldropn_0 ldropn_def ldropn_eq_LNil ldropn_ltl not_less
        one_enat_def)
  obtain y0 y1 ys' where
    ys: "ys = LCons y0 (LCons y1 ys')"
    unfolding ys_def by (metis Suc_ile_eq ldropn_Suc_conv_ldropn len less_imp_not_less not_less)
  have "chain R ys"
    unfolding ys_def using Suc_ile_eq deriv chain_ldropn len less_imp_le by blast
  then have "R y0 y1"
    unfolding ys by (auto elim: chain.cases)
  then show ?thesis
    using ys_def unfolding ys by (metis ldropn_Suc_conv_ldropn ldropn_eq_LConsD llist.inject)
qed

(* FIXME: split into a monotonicity lemma and a composition lemma? *)
lemma chain_lmap:
  assumes "\<forall>x y. R x y \<longrightarrow> R' (f x) (f y)" and "chain R xs"
  shows "chain R' (lmap f xs)"
  using assms
proof (coinduction arbitrary: xs)
  case chain
  then have "(\<exists>y. xs = LCons y LNil) \<or> (\<exists>ys x. xs = LCons x ys \<and> chain R ys \<and> R x (lhd ys))"
    using chain.simps[of R xs] by auto
  then show ?case
  proof
    assume "\<exists>ys x. xs = LCons x ys \<and> chain R ys \<and> R x (lhd ys)"
    then have "\<exists>ys x. lmap f xs = LCons x ys \<and>
      (\<exists>xs. ys = lmap f xs \<and> (\<forall>x y. R x y \<longrightarrow> R' (f x) (f y)) \<and> chain R xs) \<and> R' x (lhd ys)"
      using chain
      by (metis (no_types) lhd_LCons llist.distinct(1) llist.exhaust_sel llist.map_sel(1)
          lmap_eq_LNil lnull_chain ltl_lmap ltl_simps(2))
    then show ?thesis
      by auto
  qed auto
qed

lemma tranclp_imp_exists_finite_chain:
  "R\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists>xs. lfinite xs \<and> chain R xs \<and> lhd xs = x \<and> llast xs = y"
proof (induct rule: tranclp.induct)
  case (r_into_trancl x y)
  note r_xy = this

  define xs where
    "xs = LCons x (LCons y LNil)"

  have "lfinite xs" and "chain R xs" and "lhd xs = x" and "llast xs = y"
    unfolding xs_def using r_xy by (auto intro: chain.intros)
  then show ?case
    by blast
next
  case (trancl_into_trancl x y z)
  note rstar_xy = this(1) and ih = this(2) and r_yz = this(3)

  obtain xs where
    xs: "lfinite xs" "chain R xs" "lhd xs = x" "llast xs = y"
    using ih by blast
  define ys where
    "ys = lappend xs (LCons z LNil)"

  have "lfinite ys" and "chain R ys" and "lhd ys = x" and "llast ys = z"
    unfolding ys_def using xs r_yz by (auto simp: lnull_chain intro: singleton chain_lappend)
  then show ?case
    by blast
qed

lemma lfinite_chain_tranclp_imp_exists_lfinite_chain:
  "lfinite xs \<Longrightarrow> chain R\<^sup>+\<^sup>+ xs \<Longrightarrow>
   \<exists>ys. lfinite ys \<and> chain R ys \<and> lhd ys = lhd xs \<and> llast ys = llast xs"
proof (induction rule: lfinite_induct)
  case (LCons xs)
  show ?case
  proof (cases "lnull (ltl xs)")
    case True
    then show ?thesis
      by (metis LCons.hyps(1,2) lhd_LCons_ltl llist.collapse(1) singleton)
  next
    case nnul_tl_xs: False
    then have r_tl_xs: "chain R\<^sup>+\<^sup>+ (ltl xs)"
      by (metis LCons.prems chain.simps lnull_def ltl_simps(2))

    have "R\<^sup>+\<^sup>+ (lhd xs) (lhd (ltl xs))"
      by (metis (no_types) LCons.prems chain.simps lhd_LCons lnull_def ltl_simps(2) nnul_tl_xs)
    then obtain ys where
      ys: "lfinite ys" "chain R ys" "lhd ys = lhd xs" "llast ys = lhd (ltl xs)"
      using tranclp_imp_exists_finite_chain by metis

    obtain zs where
      zs: "lfinite zs" "chain R zs" "lhd zs = lhd (ltl xs)" "llast zs = llast (ltl xs)"
      using LCons.IH[OF r_tl_xs] by blast

    define yzs where
      "yzs = lappend ys (ltl zs)"

    have "lfinite yzs" "chain R yzs" "lhd yzs = lhd xs" "llast yzs = llast xs"
      unfolding yzs_def using ys zs LCons.hyps nnul_tl_xs
      by (auto dest: lnull_chain,
        metis (no_types) chain.simps chain_lappend lappend_lnull2 lhd_LCons llist.disc(1)
          ltl_simps(2),
        metis (no_types) llast_LCons llast_lappend llist.disc(1) llist.exhaust_sel lnull_chain)
    then show ?thesis
      by fast
  qed
qed (simp add: lnull_def)

lemma tranclp_imp_exists_finite_chain_list:
  "R\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists>xs. xs \<noteq> [] \<and> tl xs \<noteq> [] \<and> chain R (llist_of xs) \<and> hd xs = x \<and> last xs = y"
proof (induct rule: tranclp.induct)
  case (r_into_trancl x y)
  note r_xy = this

  define xs where
    "xs = [x, y]"

  have "xs \<noteq> []" and "tl xs \<noteq> []" and "chain R (llist_of xs)" and "hd xs = x" and "last xs = y"
    unfolding xs_def using r_xy by (auto intro: chain.intros)
  then show ?case
    by blast
next
  case (trancl_into_trancl x y z)
  note rstar_xy = this(1) and ih = this(2) and r_yz = this(3)

  obtain xs where
    xs: "xs \<noteq> []" "tl xs \<noteq> []" "chain R (llist_of xs)" "hd xs = x" "last xs = y"
    using ih by blast
  define ys where
    "ys = xs @ [z]"

  have "ys \<noteq> []" and "tl ys \<noteq> []" and "chain R (llist_of ys)" and "hd ys = x" and "last ys = z"
    unfolding ys_def using xs r_yz
    by (auto simp: lappend_llist_of_llist_of[symmetric] intro: singleton chain_lappend)
  then show ?case
    by blast
qed


inductive_cases chain_consE: "chain R (LCons x xs)"
inductive_cases chain_nontrivE: "chain R (LCons x (LCons y xs))"

primrec prepend where
  "prepend [] ys = ys"
| "prepend (x # xs) ys = LCons x (prepend xs ys)"

lemma prepend_butlast:
  "xs \<noteq> [] \<Longrightarrow> \<not> lnull ys \<Longrightarrow> last xs = lhd ys \<Longrightarrow> prepend (butlast xs) ys = prepend xs (ltl ys)"
  by (induct xs) auto

lemma lnull_prepend[simp]: "lnull (prepend xs ys) = (xs = [] \<and> lnull ys)"
  by (induct xs) auto

lemma lhd_prepend[simp]: "lhd (prepend xs ys) = (if xs \<noteq> [] then hd xs else lhd ys)"
  by (induct xs) auto

lemma prepend_LNil[simp]: "prepend xs LNil = llist_of xs"
  by (induct xs) auto

lemma chain_prepend: 
  "chain R (llist_of zs) \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> \<not> lnull xs \<Longrightarrow> last zs = lhd xs \<Longrightarrow> chain R xs \<Longrightarrow> chain R (prepend zs (ltl xs))"
  by (induct zs)
    (auto split: if_splits simp: lnull_def[symmetric] intro!: chain.cons elim!: chain_consE)

context
begin

private coinductive chain' for R where
  "chain' R (LCons x LNil)"
| "chain R (llist_of zs) \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> tl zs \<noteq> [] \<Longrightarrow> \<not> lnull xs \<Longrightarrow> last zs = lhd xs \<Longrightarrow> chain' R xs \<Longrightarrow> ys = ltl xs \<Longrightarrow> chain' R (prepend zs ys)"

private lemma chain_imp_chain': "chain R xs \<Longrightarrow> chain' R xs"
  apply (coinduction arbitrary: xs rule: chain'.coinduct)
  apply (erule chain.cases, simp)
  apply (rule disjI2)
  subgoal for xs zs z
    apply (rule exI[of _ "[z, lhd zs]"], rule exI[of _ zs])
    apply (auto intro: chain.intros elim: chain.cases)
    done
  done

private inductive_cases chain'_LConsE: "chain' R (LCons x xs)"

private lemma LNil_eq_iff_lnull: "LNil = xs \<longleftrightarrow> lnull xs"
  by (cases xs) auto

private lemma chain'_stepD1: "chain' R (LCons x (LCons y xs)) \<Longrightarrow> chain' R (LCons y xs)"
  apply (cases xs)
   apply (simp only: chain'.intros(1))
  apply (erule chain'.cases)
   apply (auto simp: neq_Nil_conv not_lnull_conv elim!: chain_nontrivE)
  subgoal for z zs ys xs
    apply (cases ys)
     apply simp
    unfolding prepend.simps[symmetric]
    apply (rule chain'.intros)
          apply auto
    done
  done

private lemma chain'_stepD2: "chain' R (LCons x (LCons y xs)) \<Longrightarrow> R x y"
  by (erule chain'.cases) (auto simp: neq_Nil_conv elim!: chain_nontrivE split: if_splits)
  
private lemma chain'_imp_chain: "chain' R xs \<Longrightarrow> chain R xs"
  apply (coinduction arbitrary: xs rule: chain.coinduct)
  apply (erule chain'.cases, simp)
  unfolding neq_Nil_conv not_lnull_conv
  apply (erule exE)+
  subgoal for ys zs xs as Z ZZ X _ Zs Xs
    apply (cases Xs; auto elim: chain'_stepD1 chain'_stepD2 chain_nontrivE split: if_splits)
    unfolding prepend.simps[symmetric]
    apply (intro chain'.intros)
          apply (auto simp: neq_Nil_conv elim: chain_nontrivE)
    done
  done

private lemma chain_chain': "chain = chain'"
  unfolding fun_eq_iff by (metis chain_imp_chain' chain'_imp_chain)

lemma chain_prepend_coinduct[case_names chain]:
  "X x \<Longrightarrow> (\<And>x. X x \<Longrightarrow>
    (\<exists>z. x = LCons z LNil) \<or>
    (\<exists>xs zs. x = prepend zs (ltl xs) \<and> zs \<noteq> [] \<and> tl zs \<noteq> [] \<and> \<not> lnull xs \<and> last zs = lhd xs \<and>
      (X xs \<or> chain R xs) \<and> chain R (llist_of zs))) \<Longrightarrow> chain R x"
  by (subst chain_chain', erule chain'.coinduct) (auto simp: chain_chain')

end

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

private definition pick where
  "pick x y = (SOME xs. xs \<noteq> [] \<and> tl xs \<noteq> [] \<and> chain R (llist_of xs) \<and> hd xs = x \<and> last xs = y)"

private lemma pick[simp]:
  assumes "R\<^sup>+\<^sup>+ x y"
  shows "pick x y \<noteq> []" "tl (pick x y) \<noteq> []" "chain R (llist_of (pick x y))"
    "hd (pick x y) = x" "last (pick x y) = y"
  unfolding pick_def using tranclp_imp_exists_finite_chain_list[THEN someI_ex, OF assms]
  by auto

private friend_of_corec prepend where
  "prepend xs ys = (case xs of [] \<Rightarrow> (case ys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs) | x # xs' \<Rightarrow> LCons x (prepend xs' ys))"
  by (simp split: list.splits llist.splits) transfer_prover

private corec wit where
  "wit xs = (case xs of LCons x (LCons y xs) \<Rightarrow>
     let zs = pick x y in LCons (hd zs) (prepend (butlast (tl zs)) (wit (LCons y xs))) | _ \<Rightarrow> xs)"

private lemma
  wit_LNil[simp]: "wit LNil = LNil" and
  wit_lsingleton[simp]: "wit (LCons x LNil) = LCons x LNil" and
  wit_LCons: "wit (LCons x (LCons y xs)) =
     (let zs = pick x y in LCons (hd zs) (prepend (butlast (tl zs)) (wit (LCons y xs))))"
  by (subst wit.code; auto)+

private lemma lnull_wit[simp]: "lnull (wit xs) \<longleftrightarrow> lnull xs"
  by (subst wit.code) (auto split: llist.splits simp: Let_def)

private lemma lhd_wit[simp]: "chain (R\<^sup>+\<^sup>+) xs \<Longrightarrow> \<not> lnull xs \<Longrightarrow> lhd (wit xs) = lhd xs"
  by (erule chain.cases; subst wit.code) (auto split: llist.splits simp: Let_def)

private lemma butlast_alt: "butlast xs = (if tl xs = [] then [] else hd xs # butlast (tl xs))"
  by (cases xs) auto

private lemma wit_alt:
  "chain (R\<^sup>+\<^sup>+) xs \<Longrightarrow> wit xs = (case xs of LCons x (LCons y xs) \<Rightarrow>
     prepend (pick x y) (ltl (wit (LCons y xs))) | _ \<Rightarrow> xs)"
  by (auto split: llist.splits simp: prepend_butlast[symmetric] wit_LCons Let_def
    prepend.simps(2)[symmetric] butlast_alt[of "pick _ _"]
    simp del: prepend.simps elim!: chain_nontrivE)

lemma chain_tranclp_imp_exists_chain: "chain (R\<^sup>+\<^sup>+) xs \<Longrightarrow> \<exists>ys. chain R ys"
proof (rule exI[of _ "wit xs"], coinduction arbitrary: xs rule: chain_prepend_coinduct)
  case chain
  then show ?case
    by (subst (1 2) wit_alt; assumption?) (erule chain.cases; force split: llist.splits)
qed

lemma chain_tranclp_imp_exists_chain_strong:
  "\<not> lfinite xs \<Longrightarrow> chain (R\<^sup>+\<^sup>+) xs \<Longrightarrow> \<exists>ys. chain R ys \<and> lhd ys = lhd xs \<and> lset xs \<subseteq> lset ys"
  sorry

end


subsection \<open>Processes\<close>

text \<open>
The locale assumptions below capture conditions R1 to R3 of Definition 4.1.
@{text Rf} denotes $\mathcal{R}_{\mathcal{F}}$; @{text Ri} denotes $\mathcal{R}_{\mathcal{I}}$.
\<close>

locale redundancy_criterion = inference_system +
  fixes
    Rf :: "'a clause set \<Rightarrow> 'a clause set" and
    Ri :: "'a clause set \<Rightarrow> 'a inference set"
  assumes
    Ri_subset_\<Gamma>: "Ri N \<subseteq> \<Gamma>" and
    Rf_mono: "N \<subseteq> N' \<Longrightarrow> Rf N \<subseteq> Rf N'" and
    Ri_mono: "N \<subseteq> N' \<Longrightarrow> Ri N \<subseteq> Ri N'" and
    Rf_indep: "N' \<subseteq> Rf N \<Longrightarrow> Rf N \<subseteq> Rf (N - N')" and
    Ri_indep: "N' \<subseteq> Rf N \<Longrightarrow> Ri N \<subseteq> Ri (N - N')" and
    Rf_sat: "satisfiable (N - Rf N) \<Longrightarrow> satisfiable N"
begin

definition saturated_upto :: "'a clause set \<Rightarrow> bool" where
  "saturated_upto N \<longleftrightarrow> inferences_from (N - Rf N) \<subseteq> Ri N"

inductive derive :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<triangleright>" 50) where
  deduction_deletion: "N - M \<subseteq> concls_of (inferences_from M) \<Longrightarrow> M - N \<subseteq> Rf N \<Longrightarrow> M \<triangleright> N"

lemma derive_subset: "M \<triangleright> N \<Longrightarrow> N \<subseteq> M \<union> concls_of (inferences_from M)"
  by (meson Diff_subset_conv derive.cases)

end

locale sat_preserving_redundancy_criterion =
  sat_preserving_inference_system "\<Gamma> :: ('a :: wellorder) inference set" + redundancy_criterion
begin

lemma deriv_sat_preserving:
  assumes
    deriv: "chain (op \<triangleright>) Ns" and
    sat_n0: "satisfiable (lhd Ns)"
  shows "satisfiable (Sup_llist Ns)"
proof -
  have ns0: "lnth Ns 0 = lhd Ns"
    using deriv by (metis lnull_chain lhd_conv_lnth)
  have len_ns: "llength Ns > 0"
    using deriv by (case_tac Ns) simp+
  {
    fix DD
    assume fin: "finite DD" and sset_lun: "DD \<subseteq> Sup_llist Ns"
    then obtain k where dd_sset: "DD \<subseteq> Sup_upto_llist Ns k"
      using finite_Sup_llist_imp_Sup_upto_llist by blast
    have "satisfiable (Sup_upto_llist Ns k)"
    proof (induct k)
      case 0
      then show ?case
        using len_ns ns0 sat_n0 unfolding Sup_upto_llist_def true_clss_def by auto
    next
      case (Suc k)
      show ?case
      proof (cases "enat (Suc k) \<ge> llength Ns")
        case True
        then have "Sup_upto_llist Ns k = Sup_upto_llist Ns (Suc k)"
          unfolding Sup_upto_llist_def using le_Suc_eq not_less by blast
        then show ?thesis
          using Suc by simp
      next
        case False
        then have "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using deriv by (auto simp: chain_lnth_rel)
        then have "lnth Ns (Suc k) \<subseteq> lnth Ns k \<union> concls_of (inferences_from (lnth Ns k))"
          by (rule derive_subset)
        moreover have "lnth Ns k \<subseteq> Sup_upto_llist Ns k"
          unfolding Sup_upto_llist_def using False Suc_ile_eq linear by blast
        ultimately have "lnth Ns (Suc k)
          \<subseteq> Sup_upto_llist Ns k \<union> concls_of (inferences_from (Sup_upto_llist Ns k))"
          by clarsimp (metis UnCI UnE image_Un inferences_from_mono le_iff_sup)
        moreover have "Sup_upto_llist Ns (Suc k) = Sup_upto_llist Ns k \<union> lnth Ns (Suc k)"
          unfolding Sup_upto_llist_def using False by (force elim: le_SucE)
        moreover have
          "satisfiable (Sup_upto_llist Ns k \<union> concls_of (inferences_from (Sup_upto_llist Ns k)))"
          using Suc \<Gamma>_sat_preserving unfolding sat_preserving_inference_system_def by simp
        ultimately show ?thesis
          by (metis le_iff_sup true_clss_union)
      qed
    qed
    then have "satisfiable DD"
      using dd_sset unfolding Sup_upto_llist_def by (blast intro: true_clss_mono)
  }
  then show ?thesis
    using ground_resolution_without_selection.clausal_logic_compact[THEN iffD1] by metis
qed

text \<open>
This corresponds to Lemma 4.2:
\<close>

lemma
  assumes deriv: "chain (op \<triangleright>) Ns"
  shows
    Rf_Sup_subset_Rf_Liminf: "Rf (Sup_llist Ns) \<subseteq> Rf (Liminf_llist Ns)" and
    Ri_Sup_subset_Ri_Liminf: "Ri (Sup_llist Ns) \<subseteq> Ri (Liminf_llist Ns)" and
    sat_deriv_Liminf_iff: "satisfiable (Liminf_llist Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
proof -
  {
    fix C i j
    assume
      c_in: "C \<in> lnth Ns i" and
      c_ni: "C \<notin> Rf (Sup_llist Ns)" and
      j: "j \<ge> i" and
      j': "enat j < llength Ns"
    from c_ni have c_ni': "\<And>i. enat i < llength Ns \<Longrightarrow> C \<notin> Rf (lnth Ns i)"
      using Rf_mono lnth_subset_Sup_llist Sup_llist_def by (blast dest: contra_subsetD)
    have "C \<in> lnth Ns j"
    using j j'
    proof (induct j)
      case 0
      then show ?case
        using c_in by blast
    next
      case (Suc k)
      then show ?case
      proof (cases "i < Suc k")
        case True
        have "i \<le> k"
          using True by linarith
        moreover have "enat k < llength Ns"
          using Suc.prems(2) Suc_ile_eq by (blast intro: dual_order.strict_implies_order)
        ultimately have c_in_k: "C \<in> lnth Ns k"
          using Suc.hyps by blast
        have rel: "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using Suc.prems deriv by (auto simp: chain_lnth_rel)
        then show ?thesis
          using c_in_k c_ni' Suc.prems(2) by cases auto
      next
        case False
        then show ?thesis
          using Suc c_in by auto
      qed
    qed
  }
  then have lu_ll: "Sup_llist Ns - Rf (Sup_llist Ns) \<subseteq> Liminf_llist Ns"
    unfolding Sup_llist_def Liminf_llist_def by blast
  have rf: "Rf (Sup_llist Ns - Rf (Sup_llist Ns)) \<subseteq> Rf (Liminf_llist Ns)"
    using lu_ll Rf_mono by simp
  have ri: "Ri (Sup_llist Ns - Rf (Sup_llist Ns)) \<subseteq> Ri (Liminf_llist Ns)"
    using lu_ll Ri_mono by simp
  show "Rf (Sup_llist Ns) \<subseteq> Rf (Liminf_llist Ns)"
    using rf Rf_indep by blast
  show "Ri (Sup_llist Ns) \<subseteq> Ri (Liminf_llist Ns)"
    using ri Ri_indep by blast

  show "satisfiable (Liminf_llist Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
  proof
    assume "satisfiable (lhd Ns)"
    then have "satisfiable (Sup_llist Ns)"
      using deriv deriv_sat_preserving by simp
    then show "satisfiable (Liminf_llist Ns)"
      using true_clss_mono[OF Liminf_llist_subset_Sup_llist] by blast
  next
    assume "satisfiable (Liminf_llist Ns)"
    then have "satisfiable (Sup_llist Ns - Rf (Sup_llist Ns))"
      using true_clss_mono[OF lu_ll] by blast
    then have "satisfiable (Sup_llist Ns)"
      using Rf_sat by blast
    then show "satisfiable (lhd Ns)"
      using deriv true_clss_mono lhd_subset_Sup_llist lnull_chain by metis
  qed
qed

lemma
  assumes "chain (op \<triangleright>) Ns"
  shows
    Rf_Liminf_eq_Rf_Sup: "Rf (Liminf_llist Ns) = Rf (Sup_llist Ns)" and
    Ri_Liminf_eq_Ri_Sup: "Ri (Liminf_llist Ns) = Ri (Sup_llist Ns)"
  using assms
  by (auto simp: Rf_Sup_subset_Rf_Liminf Rf_mono Ri_Sup_subset_Ri_Liminf Ri_mono
      Liminf_llist_subset_Sup_llist subset_antisym)

end

text \<open>
The assumption below corresponds to condition R4 of Definition 4.1.
\<close>

locale effective_redundancy_criterion = redundancy_criterion +
  assumes Ri_effective: "\<gamma> \<in> \<Gamma> \<Longrightarrow> concl_of \<gamma> \<in> N \<union> Rf N \<Longrightarrow> \<gamma> \<in> Ri N"
begin

definition fair_clss_seq :: "'a clause set llist \<Rightarrow> bool" where
  "fair_clss_seq Ns \<longleftrightarrow> (let N' = Liminf_llist Ns - Rf (Liminf_llist Ns) in
     concls_of (inferences_from N' - Ri N') \<subseteq> Sup_llist Ns \<union> Rf (Sup_llist Ns))"

end

locale sat_preserving_effective_redundancy_criterion =
  sat_preserving_inference_system "\<Gamma> :: ('a :: wellorder) inference set" +
  effective_redundancy_criterion
begin

sublocale sat_preserving_redundancy_criterion
  ..

text \<open>
The result below corresponds to Theorem 4.3.
\<close>

theorem fair_derive_saturated_upto:
  assumes
    deriv: "chain (op \<triangleright>) Ns" and
    fair: "fair_clss_seq Ns"
  shows "saturated_upto (Liminf_llist Ns)"
  unfolding saturated_upto_def
proof
  fix \<gamma>
  let ?N' = "Liminf_llist Ns - Rf (Liminf_llist Ns)"
  assume \<gamma>: "\<gamma> \<in> inferences_from ?N'"
  show "\<gamma> \<in> Ri (Liminf_llist Ns)"
  proof (cases "\<gamma> \<in> Ri ?N'")
    case True
    then show ?thesis
      using Ri_mono by blast
  next
    case False
    have "concls_of (inferences_from ?N' - Ri ?N') \<subseteq> Sup_llist Ns \<union> Rf (Sup_llist Ns)"
      using fair unfolding fair_clss_seq_def Let_def .
    then have "concl_of \<gamma> \<in> Sup_llist Ns \<union> Rf (Sup_llist Ns)"
      using False \<gamma> by auto
    moreover
    {
      assume "concl_of \<gamma> \<in> Sup_llist Ns"
      then have "\<gamma> \<in> Ri (Sup_llist Ns)"
        using \<gamma> Ri_effective inferences_from_def by blast
      then have "\<gamma> \<in> Ri (Liminf_llist Ns)"
        using deriv Ri_Sup_subset_Ri_Liminf by fast
    }
    moreover
    {
      assume "concl_of \<gamma> \<in> Rf (Sup_llist Ns)"
      then have "concl_of \<gamma> \<in> Rf (Liminf_llist Ns)"
        using deriv Rf_Sup_subset_Rf_Liminf by blast
      then have "\<gamma> \<in> Ri (Liminf_llist Ns)"
        using \<gamma> Ri_effective inferences_from_def by auto
    }
    ultimately show "\<gamma> \<in> Ri (Liminf_llist Ns)"
      by blast
  qed
qed

end

text \<open>
This corresponds to the trivial redundancy criterion defined on page 36 of
Section 4.1.
\<close>

locale trivial_redundancy_criterion = inference_system
begin

definition Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf _ = {}"

definition Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri N = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> concl_of \<gamma> \<in> N}"

sublocale effective_redundancy_criterion \<Gamma> Rf Ri
  by unfold_locales (auto simp: Rf_def Ri_def)

lemma saturated_upto_iff: "saturated_upto N \<longleftrightarrow> concls_of (inferences_from N) \<subseteq> N"
  unfolding saturated_upto_def inferences_from_def Rf_def Ri_def by auto

end

text \<open>
The following lemmas corresponds to the standard extension of a redundancy criterion defined on
page 38 of Section 4.1.
\<close>

lemma redundancy_criterion_standard_extension:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "redundancy_criterion \<Gamma> Rf Ri"
  shows "redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))"
  using assms unfolding redundancy_criterion_def
  by (intro conjI) ((auto simp: rev_subsetD)[5], satx)

lemma redundancy_criterion_standard_extension_saturated_upto_iff:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "redundancy_criterion \<Gamma> Rf Ri"
  shows "redundancy_criterion.saturated_upto \<Gamma> Rf Ri M \<longleftrightarrow>
    redundancy_criterion.saturated_upto \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) M"
  using assms redundancy_criterion.saturated_upto_def redundancy_criterion.saturated_upto_def
    redundancy_criterion_standard_extension
  unfolding inference_system.inferences_from_def by blast

lemma redundancy_criterion_standard_extension_effective:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "effective_redundancy_criterion \<Gamma> Rf Ri"
  shows "effective_redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))"
  using assms redundancy_criterion_standard_extension[of \<Gamma>]
  unfolding effective_redundancy_criterion_def effective_redundancy_criterion_axioms_def by auto

lemma redundancy_criterion_standard_extension_fair_iff:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "effective_redundancy_criterion \<Gamma> Rf Ri"
  shows "effective_redundancy_criterion.fair_clss_seq \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) Ns \<longleftrightarrow>
    effective_redundancy_criterion.fair_clss_seq \<Gamma> Rf Ri Ns"
  using assms redundancy_criterion_standard_extension_effective[of \<Gamma> \<Gamma>' Rf Ri]
    effective_redundancy_criterion.fair_clss_seq_def[of \<Gamma> Rf Ri Ns]
    effective_redundancy_criterion.fair_clss_seq_def[of \<Gamma>' Rf "(\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))" Ns]
  unfolding inference_system.inferences_from_def Let_def by auto

theorem redundancy_criterion_standard_extension_fair_derive_saturated_upto:
  assumes
    subs: "\<Gamma> \<subseteq> \<Gamma>'" and
    red: "redundancy_criterion \<Gamma> Rf Ri" and
    red': "sat_preserving_effective_redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))" and
    deriv: "chain (redundancy_criterion.derive \<Gamma>' Rf) Ns" and
    fair: "effective_redundancy_criterion.fair_clss_seq \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) Ns"
  shows "redundancy_criterion.saturated_upto \<Gamma> Rf Ri (Liminf_llist Ns)"
proof -
  have "redundancy_criterion.saturated_upto \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) (Liminf_llist Ns)"
    by (rule sat_preserving_effective_redundancy_criterion.fair_derive_saturated_upto
        [OF red' deriv fair])
  then show ?thesis
    by (rule redundancy_criterion_standard_extension_saturated_upto_iff[THEN iffD2, OF subs red])
qed

end
