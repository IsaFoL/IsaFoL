(* Title:        Compactness in clausal logic terms
 * Author:       Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Compactness_For_Clausal_Logic
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    "hol_light_import/FOL_Syntax"
    (* Nested_Multisets_Ordinals.Multiset_More *)
    (*Weighted_Path_Order.WPO*)
begin

section \<open>Preliminaries\<close>

(* TODO: 
     - see if count_list lemmas can be merged to the List theory
     - see if list_from_multiset def and lemmas can be merged to the Multiset theory
 *)

(* -------------------------- *)
(* count_list specific lemmas *)
subsection \<open>count_list lemmas\<close>

lemma count_list_plus_one: \<open>a \<in> set l \<Longrightarrow> count_list (a # l) a = 1 + count_list l a\<close>
  by (induction l) auto

lemma length_count_one: \<open>length l = 1 \<Longrightarrow> count_list l a = 1 \<Longrightarrow> l = [a]\<close>
  by (metis One_nat_def count_notin length_0_conv length_Suc_conv length_greater_0_conv
      length_pos_if_in_set set_ConsD)

lemma count_sum_cons: \<open>sum (count_list (a # l)) (set (a # l)) = 1 + sum (count_list l) (set l)\<close>
  by (metis List.finite_set length_Cons order.refl plus_1_eq_Suc sum_count_set)

lemma count_list_mset: \<open>count_list l x = count (mset l) x\<close>
  by (induction l) auto

lemma count_list_of_count_mset_always_exists: \<open>\<exists>l. (\<forall>x. count_list l x = (count m x))\<close>
proof (induction m)
  case empty
  find_theorems count_list
  then show ?case
    by (simp add: count_list_0_iff)
next
  case (add a m)
  then obtain l where l_is: \<open>\<forall>x. count_list l x = count m x\<close>
    by blast
  then have \<open>\<forall>x. count_list (a#l) x = count (add_mset a m) x\<close>
    by simp
  then show ?case by blast
qed

lemma mset_count_list_eq: \<open>(\<exists>l. m = mset l) \<equiv> (\<exists>l. \<forall>x. count_list l x = count m x)\<close> (is "?A \<equiv> ?B")
proof -
  have \<open>\<exists>l. m = mset l \<Longrightarrow> \<exists>l. \<forall>x. count_list l x = count m x\<close>
  proof -
    assume ?A
    then obtain l where l_is: \<open>m = mset l\<close>
      by blast
    then have \<open>count_list l x = count m x\<close> for x
    proof -
      fix x
      assume "m = mset l"
      then show \<open>count_list l x = count m x\<close>
      proof (induction l arbitrary: m rule: length_induct)
        case (1 xs m)
        then show ?case
        proof (cases \<open>length xs = 0\<close>)
          case True
          assume m_eq: "m = mset xs"
          have \<open>xs = []\<close>
            using True by auto
          then show ?thesis
            using m_eq by auto
        next
          case False
          assume m_eq: "m = mset xs" and
            IH: \<open>\<forall>ys. length ys < length xs \<longrightarrow> (\<forall>y. y = mset ys \<longrightarrow> count_list ys x = count y x)\<close>
          obtain a ys where xs_is: \<open>xs = a # ys\<close>
            using False by (metis list.size(3) neq_Nil_conv)
          then have length_eq: \<open>length ys < length xs\<close>
            by simp
          obtain n where m_is: \<open>m = add_mset a n\<close>
            using m_eq xs_is by auto
          then have n_eq: \<open>n = mset ys\<close>
            using xs_is m_eq by simp
          then have \<open>count_list ys x = count n x\<close>
            using IH length_eq n_eq by blast
          then show ?thesis
            using m_is xs_is by simp
        qed
      qed
    qed
    then show ?B
      by blast
  qed
  then show \<open>?A \<equiv> ?B\<close>
    using equal_intr_rule[of ?A ?B] ex_mset by (smt (verit, ccfv_threshold))
qed

lemma mset_impl_count_list: \<open>m = mset l \<Longrightarrow> \<forall>x. count_list l x = count m x\<close>
proof
  fix x
  assume \<open>m = mset l\<close>
  then show \<open>count_list l x = count m x\<close>
  proof (induction l arbitrary: m rule: length_induct)
    case (1 xs m)
    then show ?case
    proof (cases \<open>length xs = 0\<close>)
      case True
      assume m_eq: "m = mset xs"
      have \<open>xs = []\<close>
        using True by auto
      then show ?thesis
        using m_eq by auto
    next
      case False
      assume m_eq: "m = mset xs" and
        IH: \<open>\<forall>ys. length ys < length xs \<longrightarrow> (\<forall>y. y = mset ys \<longrightarrow> count_list ys x = count y x)\<close>
      obtain a ys where xs_is: \<open>xs = a # ys\<close>
        using False by (metis list.size(3) neq_Nil_conv)
      then have length_eq: \<open>length ys < length xs\<close>
        by simp
      obtain n where m_is: \<open>m = add_mset a n\<close>
        using m_eq xs_is by auto
      then have n_eq: \<open>n = mset ys\<close>
        using xs_is m_eq by simp
      then have \<open>count_list ys x = count n x\<close>
        using IH length_eq n_eq by blast
      then show ?thesis
        using m_is xs_is by simp
    qed
  qed
qed

lemma count_list_impl_mset: \<open>(\<forall>x. count_list l x = count m x) \<Longrightarrow> m = mset l\<close>
proof -
  assume \<open>\<forall>x. count_list l x = count m x\<close>
  then have \<open>\<forall>x. count (mset l) x = count m x\<close>
    using count_list_mset by metis
  then show \<open>m = mset l\<close>
    using multi_count_eq by metis
qed

(* -------------------------- *)

(* ----------------------------------------------------------------------------- *)
(* list_from_multiset lemmas, to obtain a list in a random order from a multiset *)
subsection \<open>list_from_multiset lemmas\<close>

definition list_of_multiset :: "'a multiset \<Rightarrow> 'a list" where
  \<open>list_of_multiset m = (SOME l. mset l = m)\<close>

lemma list_of_multiset_exists: \<open>\<exists>l. m = mset l\<close>
  using ex_mset by metis

lemma empty_list_of_multiset: \<open>list_of_multiset {#} = []\<close>
  unfolding list_of_multiset_def by simp

lemma singleton_list_of_multiset: \<open>list_of_multiset {#x#} = [x]\<close>
  unfolding list_of_multiset_def by simp

lemma nempty_multiset_to_list: \<open>m \<noteq> {#} \<Longrightarrow> list_of_multiset m \<noteq> []\<close>
  using empty_list_of_multiset
  by (metis (mono_tags, lifting) list_of_multiset_def mset_list_of_mset someI_ex)

lemma mset_list_of_multiset[simp]: "mset (list_of_multiset m) = m"
  by (metis (mono_tags, lifting) ex_mset list_of_multiset_def someI_ex)

lemma length_list_of_multiset[simp]: "length (list_of_multiset m) = size m"
  unfolding list_of_multiset_def by (metis (mono_tags) ex_mset size_mset someI_ex)

lemma length_list_of_multiset_add_mset[simp]: 
  \<open>length (list_of_multiset (add_mset x m)) = length (list_of_multiset m) + 1\<close>
  by simp

lemma \<open>mset (list_of_multiset m) = mset l \<Longrightarrow> m = mset l\<close>
  by simp

lemma \<open>mset (list_of_multiset (add_mset x m)) = add_mset x (mset (list_of_multiset m))\<close>
  by simp

lemma set_list_of_multiset_eq: \<open>set (list_of_multiset m) = set_mset m\<close>
  unfolding list_of_multiset_def
  by (metis list_of_multiset_def mset_list_of_multiset set_mset_mset)
(* ----------------------------------------------------------------------------- *)


(* ------------------------------------------------ *)
(* lemmas relating list_of_multiset with count_list and count *)
subsection \<open>lemmas relating to both list_of_multiset and count_list\<close>

lemma count_list_of_multiset: \<open>\<forall>x. count_list (list_of_multiset m) x = (count m x)\<close>
  unfolding list_of_multiset_def
  by (metis count_list_mset list_of_multiset_def mset_list_of_multiset)

lemma count_x_list_of_multiset: \<open>count_list (list_of_multiset m) x = count m x\<close>
  using count_list_of_multiset by (simp add: count_list_mset)

lemma count_mset_list_of_multiset: \<open>count (mset (list_of_multiset m)) x = count m x\<close>
  using count_list_mset count_x_list_of_multiset by simp

lemma sum_count_add_multiset_list: 
  \<open>sum (count_list (list_of_multiset (add_mset a m))) (set (list_of_multiset (add_mset a m))) =
    1 + sum (count_list (list_of_multiset m)) (set (list_of_multiset m))\<close>
  by (simp add: sum_count_set)

(* ------------------------------------------------ *)

section \<open>Alignments\<close>

(* -------------------- *)
(* alignments for atoms *)
subsection \<open>Atoms alignments\<close>

datatype natom =
  Bot (\<open>\<^bold>\<bottom>\<close>)
  | Atom (pred:nat) (args:\<open>nterm list\<close>)

lemma count_natom: \<open>OFCLASS(natom,countable_class)\<close>
  by countable_datatype

instantiation natom :: countable
begin
instance using count_natom by simp
end

(* impossible to show that countable is wellorder, cf zulip question "proof that linorder is
 countable" *)
(*
term countable_class
term wellorder_class

term "t :: 'b :: wellorder"

definition countable_less_eq :: \<open>'a :: countable \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>countable_less_eq a b \<longleftrightarrow> less_eq (to_nat a) (to_nat b)\<close>

definition countable_less :: \<open>'a :: countable \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>countable_less a b \<longleftrightarrow> less (to_nat a) (to_nat b)\<close>

subclass (in countable) (wellorder countable_less_eq countable_less)

*)

fun natom_to_form :: "natom \<Rightarrow> form" where
  \<open>natom_to_form natom.Bot = form.Bot\<close>
| \<open>natom_to_form (natom.Atom p ts) = form.Atom p ts\<close>

fun form_to_atom :: "form \<Rightarrow> natom option" where
  \<open>form_to_atom form.Bot = Some natom.Bot\<close>
| \<open>form_to_atom (form.Atom p ts) = Some (natom.Atom p ts)\<close>
| \<open>form_to_atom _ = None\<close>

lemma form_to_atom_to_form [simp]: \<open>form_to_atom (natom_to_form a) = Some a\<close>
  by (metis natom_to_form.elims form_to_atom.simps(1) form_to_atom.simps(2))

lemma form_bot_to_natom_to_bot: \<open>natom_to_form (the (form_to_atom form.Bot)) = form.Bot\<close>
  by simp

lemma form_atom_to_natom_to_atom: 
  \<open>FOL_Syntax.is_Atom \<phi> \<Longrightarrow> natom_to_form (the (form_to_atom \<phi>)) = \<phi>\<close>
  using FOL_Syntax.is_Atom_def by fastforce
(* -------------------- *)

(* ----------------------- *)
(* alignments for literals *)
subsection \<open>Literals alignments\<close>

type_synonym nlit = "natom literal"

fun nlit_to_form :: "nlit \<Rightarrow> form" where
  \<open>nlit_to_form (Pos a) = natom_to_form a\<close>
| \<open>nlit_to_form (Neg a) = \<^bold>\<not> (natom_to_form a)\<close>

fun nlit_shape :: "form \<Rightarrow> bool" where
  \<open>nlit_shape form.Bot = True\<close>
| \<open>nlit_shape (form.Atom p ts) = True\<close>
| \<open>nlit_shape (\<phi> \<^bold>\<longrightarrow> \<psi>) = (((\<phi> = form.Bot) \<or> (FOL_Syntax.is_Atom \<phi>)) \<and> (\<psi> = form.Bot))\<close>
| \<open>nlit_shape _ = False\<close>

definition shallow_neg :: "form \<Rightarrow> form \<Rightarrow> bool" where
  \<open>shallow_neg \<phi> \<psi> = (((\<phi> = form.Bot) \<or> (FOL_Syntax.is_Atom \<phi>)) \<and> (\<psi> = form.Bot))\<close>

fun is_shallow_neg :: "form \<Rightarrow> bool" where
  \<open>is_shallow_neg (\<phi> \<^bold>\<longrightarrow> \<psi>) = shallow_neg \<phi> \<psi>\<close>
| \<open>is_shallow_neg _ = False\<close>

fun form_to_nlit :: "form \<Rightarrow> nlit option" where
  \<open>form_to_nlit form.Bot = Some (Pos (natom.Bot))\<close>
| \<open>form_to_nlit (form.Atom p ts) = Some (Pos (natom.Atom p ts))\<close>
| \<open>form_to_nlit (\<phi> \<^bold>\<longrightarrow> \<psi>) = 
    (if (shallow_neg \<phi> \<psi>) then Some (Neg (the (form_to_atom \<phi>))) else None)\<close>
| \<open>form_to_nlit _ = None\<close>

lemma nlit_to_form_nlit[simp]: \<open>form_to_nlit (nlit_to_form l) = Some l\<close>
  using shallow_neg_def
  by (smt (verit, best) form.disc(2) form_to_atom_to_form form_to_nlit.simps(1) 
      form_to_nlit.simps(2) form_to_nlit.simps(3) literal.exhaust natom_to_form.elims 
      nlit_to_form.simps(1) nlit_to_form.simps(2) option.sel)

lemma form_bot_to_nlit_to_bot: \<open>nlit_to_form (the (form_to_nlit form.Bot)) = form.Bot\<close> by simp

lemma form_atom_to_nlit_to_atom: \<open>FOL_Syntax.is_Atom \<phi> \<Longrightarrow> nlit_to_form (the (form_to_nlit \<phi>)) = \<phi>\<close>
  using FOL_Syntax.is_Atom_def by fastforce

lemma shallow_neg_to_nlit_to_neg: \<open>is_shallow_neg \<phi> \<Longrightarrow> nlit_to_form (the (form_to_nlit \<phi>)) = \<phi>\<close>
  using shallow_neg_def FOL_Syntax.is_Atom_def is_shallow_neg.elims(2) by fastforce
(* ----------------------- *)

(* ---------------------- *)
(* alignments for clauses *)
subsection \<open>Clauses alignments\<close>

(* The variables occurring in clauses become free variables in formulas.
 * This should work because free variables are implicitly universally quantified in FOL_Semantics *)
type_synonym nclause = "natom clause"

fun nlit_list_to_form :: "nlit list \<Rightarrow> form" where
  \<open>nlit_list_to_form [] = form.Bot\<close>
| \<open>nlit_list_to_form (a # as) = nlit_list_to_form as \<^bold>\<or> (nlit_to_form a)\<close>

definition nclause_to_form :: "nclause \<Rightarrow> form" where
  \<open>nclause_to_form C = nlit_list_to_form (list_of_multiset C)\<close>

fun is_clausal :: "form \<Rightarrow> bool" where
  \<open>is_clausal form.Bot = True\<close>
| \<open>is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = ((\<phi>2 = \<psi>) \<and> (nlit_shape \<psi>) \<and> (is_clausal \<phi>1))\<close>
| \<open>is_clausal _ = False\<close>

find_theorems name: is_clausal

lemma is_clausal_nlit_list: \<open>is_clausal (nlit_list_to_form ls)\<close>
proof (induction "nlit_list_to_form ls" arbitrary: ls rule: is_clausal.induct)
  case 1
  then show ?case
    by simp
next
  case (2 \<phi>1 \<phi>2 \<psi>)
  have \<open>\<exists>ms. \<phi>1 = nlit_list_to_form ms\<close>
    using 2(2) by (metis form.distinct(3) form.sel(3) nlit_list_to_form.elims)
  then have clausal_phi: \<open>is_clausal \<phi>1\<close>
    using 2(1) by blast
  moreover have phi_psi_eq: \<open>\<phi>2 = \<psi>\<close>
    using 2(2) by (metis form.inject(2) form.simps(7) nlit_list_to_form.elims)
  moreover have psi_shape: \<open>nlit_shape \<psi>\<close>
    by (metis 2(2) form.sel(4) form.simps(7) form_to_nlit.simps(3) form_to_nlit.simps(4)
        nlit_list_to_form.elims nlit_shape.elims(3) nlit_to_form_nlit option.discI shallow_neg_def)
  ultimately show ?case
    by (metis 2(2) is_clausal.simps(2))
next
  case ("3_1" v va)
  then have \<open>False\<close>
    by (metis form.distinct(1) form.simps(11) nlit_list_to_form.elims)
  then show ?case
    by blast
next
  case ("3_2" va)
  then have \<open>False\<close>
    by (metis form.sel(3) form.simps(7) nlit_list_to_form.elims)
  then show ?case
    by blast
next
  case ("3_3" vb vc va)
  then have \<open>False\<close>
    by (metis form.distinct(3) form.sel(3) form.simps(11) nlit_list_to_form.elims)
  then show ?case
    by blast
next
  case ("3_4" vb vc va)
  then have \<open>False\<close>
    by (metis form.sel(3) form.simps(15) form.simps(7) nlit_list_to_form.elims)
  then show ?case
    by blast
next
  case ("3_5" v va)
  then have \<open>False\<close>
    by (metis form.simps(15) form.simps(9) nlit_list_to_form.elims)
  then show ?case
    by blast
qed

lemma is_clausal_nclause: \<open>is_clausal (nclause_to_form C)\<close>
  unfolding nclause_to_form_def using is_clausal_nlit_list by auto

fun nlit_list_from_form :: "form \<Rightarrow> nlit list option" where
  \<open>nlit_list_from_form form.Bot = Some []\<close>
| \<open>nlit_list_from_form ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = 
    (if (is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>)) 
     then (Some ((the (form_to_nlit \<psi>)) # (the (nlit_list_from_form \<phi>1))))
     else None)\<close>
| \<open>nlit_list_from_form _ = None\<close>

lemma nlit_list_form_conv: \<open>the (nlit_list_from_form (nlit_list_to_form ls)) = ls\<close>
proof (induction ls)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons a ls)
  then show ?case
    by (metis is_clausal_nlit_list nlit_list_from_form.simps(2) nlit_list_to_form.simps(2)
        nlit_to_form_nlit option.sel)
qed

definition nclause_from_form :: "form \<Rightarrow> nclause option" where
  \<open>nclause_from_form \<phi> = map_option (\<lambda>ls. mset ls) (nlit_list_from_form \<phi>)\<close>

lemma clause_to_form_conv: \<open>the (nclause_from_form (nclause_to_form C)) = C\<close>
proof (cases \<open>C = {#}\<close>)
  case True
  then show ?thesis
  unfolding nclause_from_form_def nclause_to_form_def by (simp add: empty_list_of_multiset)
next
  case False
  then obtain l ls where l_ls_are: \<open>list_of_multiset C = l # ls\<close>
    by (metis mset_list_of_multiset mset.simps(1) neq_Nil_conv)
  then have C_as_form: \<open>nclause_to_form C  = (nlit_list_to_form ls) \<^bold>\<or> (nlit_to_form l)\<close>
    using nclause_to_form_def by simp
  have \<open>is_clausal (nclause_to_form C)\<close>
    using is_clausal_nclause[of C] .
  then have \<open>nlit_list_from_form (nclause_to_form C) =
    Some ((the (form_to_nlit (nlit_to_form l))) #
     (the (nlit_list_from_form (nlit_list_to_form ls))))\<close>
    using C_as_form by auto
  also have \<open>... = Some (l # ls)\<close>
    using nlit_list_form_conv by auto
  finally show ?thesis
    unfolding nclause_from_form_def nclause_to_form_def
    by (metis mset_list_of_multiset l_ls_are option.sel option.simps(9))
qed

lemma form_nlit_list_conv: \<open>is_clausal \<phi> \<Longrightarrow> nlit_list_to_form (the (nlit_list_from_form \<phi>)) = \<phi>\<close>
proof (induction \<phi> rule: is_clausal.induct)
  case 1
  then show ?case by auto
next
  case (2 \<phi>1 \<phi>2 \<psi>)
  then show ?case
    by (smt (verit, ccfv_threshold) form.disc(2) form_atom_to_nlit_to_atom form_bot_to_nlit_to_bot
        is_clausal.simps(2) is_shallow_neg.simps(1) nlit_list_from_form.simps(2)
        nlit_list_to_form.simps(2) nlit_shape.elims(1) option.sel shallow_neg_def
        shallow_neg_to_nlit_to_neg)
next
  case ("3_1" v va)
  then have False
    by simp
  then show ?case
    by blast
next
  case ("3_2" va)
  then have False
    by simp
  then show ?case
    by blast
next
  case ("3_3" vb vc va)
  then have False
    by simp
  then show ?case
    by blast
next
  case ("3_4" vb vc va)
  then have False
    by simp
  then show ?case
    by blast
next
  case ("3_5" v va)
  then have False
    by simp
  then show ?case
    by blast
qed

(* The following doesn't hold because the literals may change ordering during the transformation process *)
(* lemma \<open>is_clausal \<phi> \<Longrightarrow> nclause_to_form (the (nclause_from_form \<phi>)) = \<phi>\<close> *)

(* What we know is that the transformation returns a clause with the same literals as the original
 *  formula if it is indeed a clause *)
lemma \<open>is_clausal \<phi> \<Longrightarrow> is_clausal (nclause_to_form (the (nclause_from_form \<phi>)))\<close>
  using is_clausal_nclause[of "the (nclause_from_form \<phi>)"] .

lemma some_clausal_nlit_list: \<open>is_clausal \<phi> \<Longrightarrow> nlit_list_from_form \<phi> \<noteq> None\<close>
  by (induction \<phi> rule: nlit_list_from_form.induct) simp+

lemma \<open>is_clausal \<phi> \<Longrightarrow> nclause_from_form \<phi> \<noteq> None\<close>
  unfolding nclause_from_form_def using some_clausal_nlit_list by simp

abbreviation mset_from_clausal_form :: "form \<Rightarrow> nlit multiset" where
(*  \<open>mset_from_clausal_form \<phi> \<equiv> mset (the (nlit_list_from_form \<phi>))\<close> *)
  \<open>mset_from_clausal_form \<phi> \<equiv> the (map_option mset (nlit_list_from_form \<phi>))\<close>

lemma mset_to_form_conv: \<open>m = mset_from_clausal_form (nclause_to_form m)\<close>
  using clause_to_form_conv unfolding nclause_from_form_def by simp

lemma form_to_clause_mset: \<open>mset_from_clausal_form \<phi> =
  mset_from_clausal_form (nclause_to_form (the (nclause_from_form \<phi>)))\<close>
  (is "?m1 = ?m2")
proof - 
  obtain m where \<open>m = mset_from_clausal_form \<phi>\<close>
    by auto
  then show \<open>?m1 = ?m2\<close>
    using mset_to_form_conv[of m] unfolding nclause_from_form_def by fast
qed
(* ---------------------- *)

(* ----------------------------- *)
(* aligments for sets of clauses *)
subsection \<open>Alignments for sets of clauses\<close>

type_synonym nclauses = "nclause set"

definition nclauses_to_form_set :: "nclauses \<Rightarrow> form set" where
  \<open>nclauses_to_form_set Cs = nclause_to_form ` Cs\<close>

definition form_set_to_nclauses :: "form set \<Rightarrow> nclauses option" where
  \<open>form_set_to_nclauses F = (let Cs = nclause_from_form ` F in
    (if None \<in> Cs then None else Some (the ` Cs)))\<close>

lemma clauses_to_form_set_conv: \<open>the (form_set_to_nclauses (nclauses_to_form_set Cs)) = Cs\<close>
  unfolding form_set_to_nclauses_def nclauses_to_form_set_def 
  sorry


(* ----------------------------- *)
end