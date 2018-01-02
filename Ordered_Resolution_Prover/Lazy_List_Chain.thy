(*  Title:       Relational Chains over Lazy Lists
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Relational Chains over Lazy Lists\<close>

theory Lazy_List_Chain
  imports "HOL-Library.BNF_Corec" Lazy_List_Liminf
begin


subsection \<open>Potentially Incomplete Chains\<close>

coinductive chain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
	chain_singleton: "chain R (LCons x LNil)"
| chain_cons: "chain R xs \<Longrightarrow> R x (lhd xs) \<Longrightarrow> chain R (LCons x xs)"

lemma
  chain_LNil[simp]: "\<not> chain R LNil" and
  chain_not_lnull: "chain R xs \<Longrightarrow> \<not> lnull xs"
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
        using r_ys mid by simp (rule chain_cons)
    next
      case xs_nnil: False
      have r_xs: "chain R xs"
        by (metis chain.simps ltl_simps(2) r_xxs xs_nnil)
      have mid': "R (llast xs) (lhd ys)"
        by (metis llast_LCons lnull_def mid xs_nnil)
      have start: "R x (lhd (lappend xs ys))"
        by (metis (no_types) chain.simps lhd_LCons lhd_lappend chain_not_lnull ltl_simps(2) r_xxs
            xs_nnil)
      show ?thesis
        unfolding lappend_code(2) using ih[OF r_xs mid'] start by (rule chain_cons)
    qed
  qed simp
qed (simp add: r_xs lappend_inf)

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
    chain: "chain R xs" and
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
    unfolding ys_def using Suc_ile_eq chain chain_ldropn len less_imp_le by blast
  then have "R y0 y1"
    unfolding ys by (auto elim: chain.cases)
  then show ?thesis
    using ys_def unfolding ys by (metis ldropn_Suc_conv_ldropn ldropn_eq_LConsD llist.inject)
qed

lemma lnth_rel_chain:
  assumes
    "\<not> lnull xs" and
    "\<forall>j. enat (j + 1) < llength xs \<longrightarrow> R (lnth xs j) (lnth xs (j + 1))"
  shows "chain R xs"
  using assms
proof (coinduction arbitrary: xs rule: chain.coinduct)
  case chain
  note nnul = this(1) and nth_chain = this(2)

  show ?case
  proof (cases "lnull (ltl xs)")
    case True
    have "xs = LCons (lhd xs) LNil"
      using nnul True by (simp add: llist.expand)
    then show ?thesis
      by blast
  next
    case nnul': False
    moreover have "xs = LCons (lhd xs) (ltl xs)"
      using nnul by simp
    moreover have
      "\<forall>j. enat (j + 1) < llength (ltl xs) \<longrightarrow> R (lnth (ltl xs) j) (lnth (ltl xs) (j + 1))"
      using nnul nth_chain
      by (metis Suc_eq_plus1 ldrop_eSuc_ltl ldropn_Suc_conv_ldropn ldropn_eq_LConsD lnth_ltl)
    moreover have "R (lhd xs) (lhd (ltl xs))"
      using nnul' nnul nth_chain[rule_format, of 0, simplified]
      by (metis ldropn_0 ldropn_Suc_conv_ldropn ldropn_eq_LConsD lhd_LCons_ltl lhd_conv_lnth
          lnth_Suc_LCons ltl_simps(2))
    ultimately show ?thesis
      by blast
  qed
qed

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
          lmap_eq_LNil chain_not_lnull ltl_lmap ltl_simps(2))
    then show ?thesis
      by auto
  qed auto
qed

lemma chain_mono:
  assumes "\<forall>x y. R x y \<longrightarrow> R' x y" and "chain R xs"
  shows "chain R' xs"
  using assms by (rule chain_lmap[of _ _ "\<lambda>x. x", unfolded llist.map_ident])

lemma lfinite_chain_imp_rtranclp_lhd_llast: "lfinite xs \<Longrightarrow> chain R xs \<Longrightarrow> R\<^sup>*\<^sup>* (lhd xs) (llast xs)"
proof (induct rule: lfinite.induct)
  case (lfinite_LConsI xs x)
  note fin_xs = this(1) and ih = this(2) and r_x_xs = this(3)
  show ?case
  proof (cases "xs = LNil")
    case xs_nnil: False
    then have r_xs: "chain R xs"
      using r_x_xs by (blast elim: chain.cases)
    then show ?thesis
      using ih[OF r_xs] xs_nnil r_x_xs
      by (metis chain.cases converse_rtranclp_into_rtranclp lhd_LCons llast_LCons chain_not_lnull
          ltl_simps(2))
  qed simp
qed simp

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
    by (auto simp: lappend_llist_of_llist_of[symmetric] intro: chain_singleton chain_lappend)
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

lemma lfinite_prepend[simp]: "lfinite (prepend xs ys) \<longleftrightarrow> lfinite ys"
  by (induct xs) auto

lemma llength_prepend[simp]: "llength (prepend xs ys) = length xs + llength ys"
  by (induct xs) (auto simp: enat_0 iadd_Suc eSuc_enat[symmetric])

lemma llast_prepend[simp]: "\<not> lnull ys \<Longrightarrow> llast (prepend xs ys) = llast ys"
  by (induct xs) (auto simp: llast_LCons)

lemma prepend_prepend: "prepend xs (prepend ys zs) = prepend (xs @ ys) zs"
  by (induct xs) auto

lemma chain_prepend:
  "chain R (llist_of zs) \<Longrightarrow> last zs = lhd xs \<Longrightarrow> chain R xs \<Longrightarrow> chain R (prepend zs (ltl xs))"
  by (induct zs; cases xs)
    (auto split: if_splits simp: lnull_def[symmetric] intro!: chain_cons elim!: chain_consE)

lemma lmap_prepend[simp]: "lmap f (prepend xs ys) = prepend (map f xs) (lmap f ys)"
  by (induct xs) auto

lemma lset_prepend[simp]: "lset (prepend xs ys) = set xs \<union> lset ys"
  by (induct xs) auto

lemma prepend_LCons: "prepend xs (LCons y ys) = prepend (xs @ [y]) ys"
  by (induct xs) auto

lemma lnth_prepend:
  "lnth (prepend xs ys) i = (if i < length xs then nth xs i else lnth ys (i - length xs))"
  by (induct xs arbitrary: i) (auto simp: lnth_LCons' nth_Cons')

theorem lfinite_less_induct[consumes 1, case_names less]:
  assumes fin: "lfinite xs"
    and step: "\<And>xs. lfinite xs \<Longrightarrow> (\<And>zs. llength zs < llength xs \<Longrightarrow> P zs) \<Longrightarrow> P xs"
  shows "P xs"
using fin proof (induct "the_enat (llength xs)" arbitrary: xs rule: less_induct)
  case (less xs)
  show ?case
    using less(2) by (intro step[OF less(2)] less(1))
      (auto dest!: lfinite_llength_enat simp: eSuc_enat elim!: less_enatE llength_eq_enat_lfiniteD)
qed

theorem lfinite_prepend_induct[consumes 1, case_names LNil prepend]:
  assumes "lfinite xs"
    and LNil: "P LNil"
    and prepend: "\<And>xs. lfinite xs \<Longrightarrow> (\<And>zs. (\<exists>ys. xs = prepend ys zs \<and> ys \<noteq> []) \<Longrightarrow> P zs) \<Longrightarrow> P xs"
  shows "P xs"
using assms(1) proof (induct xs rule: lfinite_less_induct)
  case (less xs)
  from less(1) show ?case
    by (cases xs)
      (force simp: LNil neq_Nil_conv dest: lfinite_llength_enat intro!: prepend[of "LCons _ _"] intro: less)+
qed

coinductive emb :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool" where
  "emb LNil xs"
| "emb xs ys \<Longrightarrow> emb (LCons x xs) (prepend zs (LCons x ys))"

inductive prepend_cong1 for X where
  prepend_cong1_base: "X xs \<Longrightarrow> prepend_cong1 X xs"
| prepend_cong1_prepend: "prepend_cong1 X ys \<Longrightarrow> prepend_cong1 X (prepend xs ys)"

lemma emb_prepend_coinduct[rotated, case_names emb]:
  assumes "(\<And>x1 x2. X x1 x2 \<Longrightarrow>
    (\<exists>xs. x1 = LNil \<and> x2 = xs)
     \<or> (\<exists>xs ys x zs. x1 = LCons x xs \<and> x2 = prepend zs (LCons x ys)
       \<and> (prepend_cong1 (X xs) ys \<or> emb xs ys)))" (is "\<And>x1 x2. X x1 x2 \<Longrightarrow> ?bisim x1 x2")
  shows "X x1 x2 \<Longrightarrow> emb x1 x2"
proof (erule emb.coinduct[OF prepend_cong1_base])
  fix xs zs
  assume "prepend_cong1 (X xs) zs"
  then show "?bisim xs zs"
    by (induct zs rule: prepend_cong1.induct) (erule assms, force simp: prepend_prepend)
qed

context
begin

private coinductive chain' for R where
  "chain' R (LCons x LNil)"
| "chain R (llist_of zs) \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> tl zs \<noteq> [] \<Longrightarrow> \<not> lnull xs \<Longrightarrow> last zs = lhd xs \<Longrightarrow>
     ys = ltl xs \<Longrightarrow> chain' R xs \<Longrightarrow> chain' R (prepend zs ys)"

private lemma chain_imp_chain': "chain R xs \<Longrightarrow> chain' R xs"
proof (coinduction arbitrary: xs rule: chain'.coinduct)
  case chain'
  then show ?case
  proof (cases rule: chain.cases)
    case (chain_cons zs z)
    then show ?thesis
      by (intro disjI2) (force intro: chain.intros exI[of _ "[z, lhd zs]"] exI[of _ zs]
          elim: chain.cases)
  qed simp
qed

private inductive_cases chain'_LConsE: "chain' R (LCons x xs)"

private lemma chain'_stepD1:
  assumes "chain' R (LCons x (LCons y xs))"
  shows "chain' R (LCons y xs)"
proof (cases xs)
  case [simp]: (LCons z zs)
  with assms show ?thesis
  proof (cases rule: chain'.cases)
    case (2 as ys xs)
    then show ?thesis
    proof (cases "tl (tl as)")
      case Nil
      with 2 show ?thesis by (auto simp: neq_Nil_conv)
    next
      case (Cons b bs)
      with 2 have "chain' R (prepend (y # b # bs) xs)"
        by (intro chain'.intros)
          (auto simp: chain_cons not_lnull_conv neq_Nil_conv elim: chain_nontrivE)
      with 2 Cons show ?thesis
        by (auto simp: neq_Nil_conv)
    qed
  qed
qed (simp only: chain'.intros(1))

private lemma chain'_stepD2: "chain' R (LCons x (LCons y xs)) \<Longrightarrow> R x y"
  by (erule chain'.cases) (auto simp: neq_Nil_conv elim!: chain_nontrivE split: if_splits)

private lemma chain'_imp_chain: "chain' R xs \<Longrightarrow> chain R xs"
proof (coinduction arbitrary: xs rule: chain.coinduct)
  case chain
  then show ?case
  proof (cases rule: chain'.cases)
    case (2 ys zs xs)
    then show ?thesis
    proof (cases "ltl zs")
      case LNil
      with chain 2 show ?thesis
        by (auto 0 4 simp: neq_Nil_conv not_lnull_conv elim: chain'_stepD1 chain'_stepD2)
    next
      case (LCons b bs)
      with chain 2 show ?thesis
        unfolding neq_Nil_conv not_lnull_conv
        by (elim exE) (auto elim: chain'_stepD1 chain_nontrivE)
    qed
  qed simp
qed

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
  unfolding pick_def using tranclp_imp_exists_finite_chain_list[THEN someI_ex, OF assms] by auto

private lemma butlast_pick[simp]: "R\<^sup>+\<^sup>+ x y \<Longrightarrow> butlast (pick x y) \<noteq> []"
  by (cases "pick x y"; cases "tl (pick x y)") (auto dest: pick(2))

private friend_of_corec prepend where
  "prepend xs ys = (case xs of [] \<Rightarrow> (case ys of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons x xs) | x # xs' \<Rightarrow> LCons x (prepend xs' ys))"
  by (simp split: list.splits llist.splits) transfer_prover

private corec wit where
  "wit xs = (case xs of LCons x (LCons y xs) \<Rightarrow>
     let zs = pick x y in LCons (hd zs) (prepend (butlast (tl zs)) (wit (LCons y xs))) | _ \<Rightarrow> xs)"

private lemma
  wit_LNil[simp]: "wit LNil = LNil" and
  wit_lsingleton[simp]: "wit (LCons x LNil) = LCons x LNil" and
  wit_LCons2: "wit (LCons x (LCons y xs)) =
     (let zs = pick x y in LCons (hd zs) (prepend (butlast (tl zs)) (wit (LCons y xs))))"
  by (subst wit.code; auto)+

private lemma wit_LCons: "wit (LCons x xs) = (case xs of LNil \<Rightarrow> LCons x LNil | LCons y xs \<Rightarrow>
     (let zs = pick x y in LCons (hd zs) (prepend (butlast (tl zs)) (wit (LCons y xs)))))"
  by (subst wit.code; auto split: llist.splits)+

private lemma lnull_wit[simp]: "lnull (wit xs) \<longleftrightarrow> lnull xs"
  by (subst wit.code) (auto split: llist.splits simp: Let_def)

private lemma lhd_wit[simp]: "chain R\<^sup>+\<^sup>+ xs \<Longrightarrow> lhd (wit xs) = lhd xs"
  by (erule chain.cases; subst wit.code) (auto split: llist.splits simp: Let_def)

private lemma butlast_alt: "butlast xs = (if tl xs = [] then [] else hd xs # butlast (tl xs))"
  by (cases xs) auto

private lemma wit_alt:
  "chain R\<^sup>+\<^sup>+ xs \<Longrightarrow> wit xs = (case xs of LCons x (LCons y xs) \<Rightarrow>
     prepend (pick x y) (ltl (wit (LCons y xs))) | _ \<Rightarrow> xs)"
  by (auto split: llist.splits simp: prepend_butlast[symmetric] wit_LCons2 Let_def
    prepend.simps(2)[symmetric] butlast_alt[of "pick _ _"]
    simp del: prepend.simps elim!: chain_nontrivE)

private lemma wit_alt2:
  "chain R\<^sup>+\<^sup>+ xs \<Longrightarrow> wit xs = (case xs of LCons x (LCons y xs) \<Rightarrow>
     prepend (butlast (pick x y)) (wit (LCons y xs)) | _ \<Rightarrow> xs)"
  by (auto split: llist.splits simp: wit_LCons2 Let_def
    prepend.simps(2)[symmetric] butlast_alt[of "pick _ _"]
    simp del: prepend.simps elim!: chain_nontrivE)

private lemma LNil_eq_iff_lnull: "LNil = xs \<longleftrightarrow> lnull xs"
  by (cases xs) auto

private lemma lfinite_wit[simp]:
  assumes "chain R\<^sup>+\<^sup>+ xs"
  shows "lfinite (wit xs) \<longleftrightarrow> lfinite xs"
proof
  assume "lfinite (wit xs)"
  from this assms show "lfinite xs"
  proof (induct "wit xs" arbitrary: xs rule: lfinite_prepend_induct)
    case (prepend zs)
    then show ?case
    proof (cases zs)
      case [simp]: (LCons x xs)
      then show ?thesis
      proof (cases xs)
        case [simp]: LCons
        with prepend show ?thesis
          by (subst (asm) (2) wit_alt2) (force split: llist.splits elim!: chain_nontrivE)+
      qed simp
    qed simp
  qed (simp add: LNil_eq_iff_lnull)
next
  assume "lfinite xs"
  then show "lfinite (wit xs)"
  proof (induct xs rule: lfinite.induct)
    case (lfinite_LConsI xs x)
    then show ?case
      by (cases xs) (auto simp: wit_LCons Let_def)
  qed simp
qed

private lemma llast_wit[simp]:
  assumes "chain R\<^sup>+\<^sup>+ xs"
  shows "llast (wit xs) = llast xs"
proof (cases "lfinite xs")
  case True
  from this assms show ?thesis
  proof (induct rule: lfinite.induct)
    case (lfinite_LConsI xs x)
    then show ?case
      by (cases xs) (auto simp: wit_LCons2 llast_LCons elim: chain_nontrivE)
  qed auto
qed (auto simp: llast_linfinite assms)

lemma emb_wit[simp]: "chain R\<^sup>+\<^sup>+ xs \<Longrightarrow> emb xs (wit xs)"
proof (coinduction arbitrary: xs rule: emb_prepend_coinduct)
  case (emb xs)
  then show ?case
  proof (cases rule: chain.cases)
    case (chain_cons zs z)
    then show ?thesis
      by (subst (2) wit.code)
        (auto split: llist.splits intro!: exI[of _ "[]"] exI[of _ "_ :: _ llist"]
          prepend_cong1_prepend[OF prepend_cong1_base])
  qed (auto intro!: exI[of _ LNil] exI[of _ "[]"] emb.intros)
qed

lemma chain_tranclp_imp_exists_chain:
  "chain R\<^sup>+\<^sup>+ xs \<Longrightarrow>
   \<exists>ys. chain R ys \<and> emb xs ys \<and> (lfinite ys \<longleftrightarrow> lfinite xs) \<and> lhd ys = lhd xs
     \<and> llast ys = llast xs"
proof (intro exI[of _ "wit xs"] conjI, coinduction arbitrary: xs rule: chain_prepend_coinduct)
  case chain
  then show ?case
    by (subst (1 2) wit_alt; assumption?) (erule chain.cases; force split: llist.splits)
qed auto

inductive_cases emb_LConsE: "emb (LCons z zs) ys"
inductive_cases emb_LNil2E: "emb xs LNil"

lemma emb_lset_mono[rotated]: "x \<in> lset xs \<Longrightarrow> emb xs ys \<Longrightarrow> x \<in> lset ys"
  by (induct x xs arbitrary: ys rule: llist.set_induct) (auto elim!: emb_LConsE)

lemma emb_Ball_lset_antimono:
  assumes "emb Xs Ys"
  shows "\<forall>Y \<in> lset Ys. x \<in> Y \<Longrightarrow> \<forall>X \<in> lset Xs. x \<in> X"
  using emb_lset_mono[OF assms] by blast

lemma emb_lfinite_antimono[rotated]: "lfinite ys \<Longrightarrow> emb xs ys \<Longrightarrow> lfinite xs"
  by (induct ys arbitrary: xs rule: lfinite_prepend_induct)
    (force elim!: emb_LNil2E simp: LNil_eq_iff_lnull prepend_LCons elim: emb.cases)+

lemma emb_Liminf_llist_mono_aux:
  assumes "emb Xs Ys" and "\<not> lfinite Xs" and "\<not> lfinite Ys" and "\<forall>j\<ge>i. x \<in> lnth Ys j"
  shows "\<forall>j\<ge>i. x \<in> lnth Xs j"
using assms proof (induct i arbitrary: Xs Ys rule: less_induct)
  case (less i)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using emb_Ball_lset_antimono[OF less(2), of x] less(5)
      unfolding Ball_def in_lset_conv_lnth simp_thms
        not_lfinite_llength[OF less(3)] not_lfinite_llength[OF less(4)] enat_ord_code subset_eq
      by blast
  next
    case [simp]: (Suc nat)
    from less(2,3) obtain xs as b bs where
      [simp]: "Xs = LCons b xs" "Ys = prepend as (LCons b bs)" and "emb xs bs"
      by (auto elim: emb.cases)
    have IH: "\<forall>k\<ge>j. x \<in> lnth xs k" if "\<forall>k\<ge>j. x \<in> lnth bs k" "j < i" for j
      using that less(1)[OF _ \<open>emb xs bs\<close>] less(3,4) by auto
    from less(5) have "\<forall>k\<ge>i - length as - 1. x \<in> lnth xs k"
      by (intro IH allI)
        (drule spec[of _ "_ + length as + 1"], auto simp: lnth_prepend lnth_LCons')
    then show ?thesis
      by (auto simp: lnth_LCons')
  qed
qed

lemma emb_Liminf_llist_infinite:
  assumes "emb Xs Ys" and "\<not> lfinite Xs"
  shows "Liminf_llist Ys \<subseteq> Liminf_llist Xs"
proof -
  from assms have "\<not> lfinite Ys"
    using emb_lfinite_antimono by blast
  with assms show ?thesis
    unfolding Liminf_llist_def by (auto simp: not_lfinite_llength dest: emb_Liminf_llist_mono_aux)
qed

lemma emb_lmap: "emb xs ys \<Longrightarrow> emb (lmap f xs) (lmap f ys)"
proof (coinduction arbitrary: xs ys rule: emb.coinduct)
  case emb
  show ?case
  proof (cases xs)
    case xs: (LCons x xs')

    obtain ysa0 and zs0 where
      ys: "ys = prepend zs0 (LCons x ysa0)" and
      emb': "emb xs' ysa0"
      using emb_LConsE[OF emb[unfolded xs]] by metis

    let ?xa = "f x"
    let ?xsa = "lmap f xs'"
    let ?zs = "map f zs0"
    let ?ysa = "lmap f ysa0"

    have "lmap f xs = LCons ?xa ?xsa"
      unfolding xs by simp
    moreover have "lmap f ys = prepend ?zs (LCons ?xa ?ysa)"
      unfolding ys by simp
    moreover have "\<exists>xsa ysa. ?xsa = lmap f xsa \<and> ?ysa = lmap f ysa \<and> emb xsa ysa"
      using emb' by blast
    ultimately show ?thesis
      by blast
  qed simp
qed

end


subsection \<open>Complete Chains\<close>

coinductive full_chain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
	full_chain_singleton: "(\<forall>y. \<not> R x y) \<Longrightarrow> full_chain R (LCons x LNil)"
| full_chain_cons: "full_chain R xs \<Longrightarrow> R x (lhd xs) \<Longrightarrow> full_chain R (LCons x xs)"

lemma
  full_chain_LNil[simp]: "\<not> full_chain R LNil" and
  full_chain_not_lnull: "full_chain R xs \<Longrightarrow> \<not> lnull xs"
  by (auto elim: full_chain.cases)

lemma full_chain_ldropn:
  assumes full: "full_chain R xs" and "enat n < llength xs"
  shows "full_chain R (ldropn n xs)"
  using assms
  by (induct n arbitrary: xs, simp,
      metis full_chain.cases ldrop_eSuc_ltl ldropn_LNil ldropn_eq_LNil ltl_simps(2) not_less)

lemma full_chain_iff_chain:
  "full_chain R xs \<longleftrightarrow> chain R xs \<and> (lfinite xs \<longrightarrow> (\<forall>y. \<not> R (llast xs) y))"
proof (intro iffI conjI impI allI; (elim conjE)?)
  assume full: "full_chain R xs"

  show chain: "chain R xs"
    using full by (coinduction arbitrary: xs) (auto elim: full_chain.cases)

  {
    fix y
    assume "lfinite xs"
    then obtain n where
      suc_n: "Suc n = llength xs"
      by (metis chain chain_length_pos lessE less_enatE lfinite_conv_llength_enat)

    have "full_chain R (ldropn n xs)"
      by (rule full_chain_ldropn[OF full]) (use suc_n Suc_ile_eq in force)
    moreover have "ldropn n xs = LCons (llast xs) LNil"
      using suc_n by (metis enat_le_plus_same(2) enat_ord_simps(2) gen_llength_def
          ldropn_Suc_conv_ldropn ldropn_all lessI llast_ldropn llast_singleton llength_code)
    ultimately show "\<not> R (llast xs) y"
      by (auto elim: full_chain.cases)
  }
next
  assume
    "chain R xs" and
    "lfinite xs \<longrightarrow> (\<forall>y. \<not> R (llast xs) y)"
  then show "full_chain R xs"
    by (coinduction arbitrary: xs) (erule chain.cases, simp, metis lfinite_LConsI llast_LCons)
qed

lemma full_chain_imp_chain: "full_chain R xs \<Longrightarrow> chain R xs"
  using full_chain_iff_chain by blast

lemma full_chain_length_pos: "full_chain R xs \<Longrightarrow> llength xs > 0"
  by (fact chain_length_pos[OF full_chain_imp_chain])

lemma full_chain_lnth_rel:
  "full_chain R xs \<Longrightarrow> enat (Suc j) < llength xs \<Longrightarrow> R (lnth xs j) (lnth xs (Suc j))"
  by (fact chain_lnth_rel[OF full_chain_imp_chain])

inductive_cases full_chain_consE: "full_chain R (LCons x xs)"
inductive_cases full_chain_nontrivE: "full_chain R (LCons x (LCons y xs))"

lemma full_chain_tranclp_imp_exists_full_chain:
  assumes full: "full_chain R\<^sup>+\<^sup>+ xs"
  shows "\<exists>ys. full_chain R ys \<and> emb xs ys \<and> lfinite ys = lfinite xs \<and> lhd ys = lhd xs
    \<and> llast ys = llast xs"
proof -
  obtain ys where ys:
    "chain R ys" "emb xs ys" "lfinite ys = lfinite xs" "lhd ys = lhd xs" "llast ys = llast xs"
    using full_chain_imp_chain[OF full] chain_tranclp_imp_exists_chain by blast
  have "full_chain R ys"
    using ys(1,3,5) full unfolding full_chain_iff_chain by auto
  then show ?thesis
    using ys(2-5) by auto
qed

end
