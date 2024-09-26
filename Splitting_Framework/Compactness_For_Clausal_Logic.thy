(* Title:        Compactness in clausal logic terms
 * Author:       Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Compactness_For_Clausal_Logic
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    "hol_light_import/HOL_Light_Bridge" 
    (* "hol_light_import/FOL_Syntax" *)
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

lemma length_list_of_multiset[simp]: "length (list_of_multiset m) = size_class.size m"
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
  \<open>nlit_shape form.Bot = HOL.True\<close>
| \<open>nlit_shape (form.Atom p ts) = HOL.True\<close>
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
  \<open>is_clausal form.Bot = HOL.True\<close>
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
lemma form_to_clause_clausal: \<open>is_clausal \<phi> \<Longrightarrow> is_clausal (nclause_to_form (the (nclause_from_form \<phi>)))\<close>
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

(* Can this be moved to somewhere else? *)
lemma equality_subsetsI: \<open>(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B\<close>
  by blast

lemma clauses_to_form_set_conv: \<open>the (form_set_to_nclauses (nclauses_to_form_set Cs)) = Cs\<close>
proof -
  have \<open>None \<notin> nclause_from_form ` nclause_to_form ` Cs\<close>
  proof (rule ccontr)
    assume \<open>\<not> None \<notin> nclause_from_form ` nclause_to_form ` Cs\<close>
    then have \<open>None \<in> nclause_from_form ` nclause_to_form ` Cs\<close>
      by blast
    then have \<open>None \<in> nlit_list_from_form ` nclause_to_form ` Cs\<close>
      unfolding nclause_from_form_def by force
    then show \<open>False\<close>
      by (metis imageE is_clausal_nclause some_clausal_nlit_list)
  qed
  then have \<open>form_set_to_nclauses (nclauses_to_form_set Cs) = 
    Some (the ` nclause_from_form ` (nclauses_to_form_set Cs))\<close>
    using form_set_to_nclauses_def nclauses_to_form_set_def by presburger 
  moreover have \<open>the ` nclause_from_form ` nclause_to_form ` Cs = Cs\<close>
  proof (rule equality_subsetsI)
    fix x
    assume \<open>x \<in> the ` nclause_from_form ` nclause_to_form ` Cs\<close>
    then obtain C where "C \<in> Cs" and \<open>x = the (nclause_from_form (nclause_to_form C))\<close>
      by blast
    then show \<open>x \<in> Cs\<close>
      using clause_to_form_conv by simp
  next
    fix x
    assume \<open>x \<in> Cs\<close>
    then show \<open>x \<in> the ` nclause_from_form ` nclause_to_form ` Cs\<close>
      using clause_to_form_conv by (simp add: image_iff)
  qed
  ultimately show ?thesis
    unfolding form_set_to_nclauses_def nclauses_to_form_set_def by auto
qed

(* Again, the conversion starting from formulas and back cannot ensure the ordering of literals *)
lemma form_set_to_clauses_clausal: \<open>Ball F is_clausal \<Longrightarrow>
   Ball (nclauses_to_form_set (the (form_set_to_nclauses F))) is_clausal\<close>
  using form_to_clause_clausal by (simp add: is_clausal_nclause nclauses_to_form_set_def)

lemma form_set_to_clauses_mset: \<open>Ball F (\<lambda>\<phi>. mset_from_clausal_form \<phi> =
  mset_from_clausal_form (nclause_to_form (the (nclause_from_form \<phi>))))\<close>
  using form_to_clause_mset by (simp add: is_clausal_nclause nclauses_to_form_set_def)
(* ----------------------------- *)


section \<open>Tarski and Herbrand Entailments\<close>



lemma ex_beta: \<open>\<forall>I. \<exists>\<beta>. is_valuation I \<beta>\<close> 
proof
  fix I
  show \<open>\<exists>\<beta>. is_valuation I \<beta>\<close> 
    unfolding is_valuation_def using intrp_is_struct struct.M_nonempty by fastforce
qed

lemma holds_closed_ex_equiv_all_val: \<open>FOL_Syntax.FV \<phi> = {} \<Longrightarrow> (\<exists>\<beta>. I,\<beta> \<Turnstile> \<phi>) \<Longrightarrow> (\<forall>\<beta>. I,\<beta> \<Turnstile> \<phi>)\<close>
  by (metis emptyE holds_indep_\<beta>_if)

lemma sat_union: \<open>satisfies I (\<Phi> \<union> \<Psi>) = (satisfies I \<Phi> \<and> satisfies I \<Psi>)\<close>
  unfolding satisfies_def by (smt (verit) Un_iff)

lemma sat_union_left: \<open>satisfies I (\<Phi> \<union> \<Psi>) \<Longrightarrow> satisfies I \<Phi>\<close>
  unfolding satisfies_def by blast

lemma bot_not_sat: \<open>\<not> satisfies I {form.Bot}\<close>
  unfolding satisfies_def
proof
  assume \<open>\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<^bold>\<bottom>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>\<close>
  then have sat_bot: \<open>\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> I,\<beta> \<Turnstile> form.Bot\<close>
    by blast
  obtain \<beta> where \<open>is_valuation I \<beta>\<close> 
    using ex_beta by blast
  moreover have \<open>\<not> I,\<beta> \<Turnstile> form.Bot\<close>
    by auto
  ultimately show \<open>False\<close> using sat_bot 
    by fast
qed

lemma holds_or: \<open>I,\<beta> \<Turnstile> \<phi> \<^bold>\<or> \<psi> \<equiv> (I,\<beta> \<Turnstile> \<phi>) \<or> (I,\<beta> \<Turnstile> \<psi>)\<close>
  by (smt (verit, best) holds.simps(3))

lemma holds_not: \<open>I,\<beta> \<Turnstile> \<^bold>\<not> \<phi> \<equiv> \<not> (I,\<beta> \<Turnstile> \<phi>)\<close>
  by auto

lemma holds_not_not[simp]: \<open>I,\<beta> \<Turnstile> \<^bold>\<not> (\<^bold>\<not> \<phi>) = I,\<beta> \<Turnstile> \<phi>\<close>
  by auto

lemma sat_neg_forward: \<open>satisfies I {\<psi>} \<Longrightarrow> (\<not> (satisfies I  {\<^bold>\<not>\<psi>}))\<close>
  unfolding satisfies_def using ex_beta by auto

lemma sat_neg_neg[simp]: \<open>satisfies I {\<^bold>\<not> (\<^bold>\<not> \<phi>)} = satisfies I {\<phi>}\<close>
  unfolding satisfies_def by auto

lemma sat_neg_back: \<open>satisfies I {\<^bold>\<not>\<psi>} \<Longrightarrow> (\<not> (satisfies I  {\<psi>}))\<close>
  using sat_neg_forward[of _ "\<^bold>\<not>\<psi>"] by simp

lemma ground_sat_neg_eq: \<open>FOL_Syntax.FV \<psi> = {} \<Longrightarrow> \<not> (satisfies I  {\<psi>}) \<Longrightarrow> satisfies I {\<^bold>\<not>\<psi>}\<close>
  unfolding satisfies_def using holds_closed_ex_equiv_all_val holds_not by blast

lemma language_with_Bot[simp]: \<open>FOL_Syntax.language (\<Phi> \<union> {form.Bot}) = FOL_Syntax.language \<Phi>\<close>
  unfolding FOL_Syntax.language_def functions_forms_def FOL_Syntax.predicates_def by auto

lemma language_union[simp]: \<open>FOL_Syntax.language (\<Phi> \<union> \<Psi>) = 
  (functions_forms \<Phi> \<union> functions_forms \<Psi>, FOL_Syntax.predicates \<Phi> \<union> FOL_Syntax.predicates \<Psi>)\<close>
  unfolding FOL_Syntax.language_def functions_forms_def FOL_Syntax.predicates_def by auto

lemma language_not[simp]: \<open>FOL_Syntax.language {\<^bold>\<not>\<phi>} = FOL_Syntax.language {\<phi>}\<close>
  unfolding FOL_Syntax.language_def functions_forms_def FOL_Syntax.predicates_def by auto


definition entails_tarski :: \<open>form set \<Rightarrow> form set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>T\<close> 50) where
  \<open>\<Phi> \<Turnstile>\<^sub>T \<Psi> \<equiv> (\<forall>(I :: nterm intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> \<Psi>)) I \<longrightarrow>
    (satisfies I \<Phi> \<longrightarrow> satisfies I \<Psi>))\<close>



definition is_grounding :: \<open>(nat, nat) subst \<Rightarrow> bool\<close> where
  \<open>is_grounding \<sigma> \<equiv> \<forall>t. ground (t \<cdot> \<sigma>)\<close>

definition groundings :: \<open>form set \<Rightarrow> form set\<close> where
  \<open>groundings \<Phi> = {\<psi>. (\<exists>\<phi>\<in>\<Phi>. \<exists>\<sigma>. is_grounding \<sigma> \<and> \<psi> = \<phi>  \<cdot>\<^sub>f\<^sub>m \<sigma>)}\<close>

lemma groundings_ground: \<open>\<Union> (FOL_Syntax.FV ` (groundings \<Phi>)) = {}\<close>
  unfolding groundings_def is_grounding_def using ground_vars_term_empty
  by (smt (verit, best) SUP_bot_conv(1) all_not_in_conv formsubst_fv mem_Collect_eq)

lemma ground_dist: \<open>groundings (\<Phi> \<union> \<Psi>) = groundings \<Phi> \<union> groundings \<Psi>\<close>
  unfolding groundings_def by blast

lemma exists_grounding: \<open>\<exists>\<sigma>. is_grounding \<sigma>\<close>
proof -
  have \<open>\<exists>t. ground t\<close>
    by (metis all_not_in_conv ground.simps(2) list.set(1))
  then obtain t where t_ground: \<open>ground (t :: nterm)\<close> 
    by blast
  define \<sigma> :: "(nat, nat) subst" where \<open>\<sigma> = (\<lambda>v. t)\<close>
  then have \<open>is_grounding \<sigma>\<close>
    using t_ground
    by (simp add: is_grounding_def)
  then show ?thesis
    by blast
qed

lemma ground_ex_nempty: \<open>\<Phi> \<noteq> {} \<Longrightarrow> \<exists>\<phi>. \<phi> \<in> groundings \<Phi>\<close>
  using exists_grounding unfolding groundings_def by auto

lemma ground_ex: \<open>\<exists>\<phi>. \<phi> \<in> groundings {\<psi>}\<close>
  using ground_ex_nempty by blast

lemma ground_neg: \<open>groundings {\<^bold>\<not>\<phi>} = (\<lambda>\<psi>. \<^bold>\<not>\<psi>) ` (groundings {\<phi>})\<close>
  unfolding groundings_def by auto

lemma ground_bot: \<open>groundings {form.Bot} = {form.Bot}\<close>
  unfolding groundings_def 
proof -
  have \<open>{\<psi>. \<exists>\<phi>\<in>{\<^bold>\<bottom>}. \<exists>\<sigma>. is_grounding \<sigma> \<and> \<psi> = \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>} = {\<psi>. \<exists>\<sigma>. is_grounding \<sigma> \<and> \<psi> = form.Bot}\<close>
    by auto
  also have \<open>... = {form.Bot}\<close>
    using exists_grounding by simp
  finally show \<open>{\<psi>. \<exists>\<phi>\<in>{\<^bold>\<bottom>}. \<exists>\<sigma>. is_grounding \<sigma> \<and> \<psi> = \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>} = {\<^bold>\<bottom>}\<close> .
qed


lemma sat_ground_neg: \<open>satisfies I (groundings {\<psi>}) \<Longrightarrow> \<not> (satisfies I (groundings {\<^bold>\<not>\<psi>}))\<close>
  using ground_neg
  by (metis bot_not_sat ground_ex holds.simps(3) image_eqI satisfies_def singletonD)

lemma sat_ground_neg2: \<open>satisfies I (groundings {\<^bold>\<not>\<psi>}) \<Longrightarrow> \<not> (satisfies I (groundings {\<psi>}))\<close>
  using ground_neg
  by (metis bot_not_sat ground_ex holds.simps(3) image_eqI satisfies_def singletonD)

definition entails_herbrand :: \<open>form set \<Rightarrow> form set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>H\<close> 50) where
  \<open>\<Phi> \<Turnstile>\<^sub>H \<Psi> \<equiv> (\<forall>(I :: nterm intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> \<Psi>)) I \<longrightarrow>
    (satisfies I (groundings \<Phi>) \<longrightarrow> satisfies I (groundings \<Psi>)))\<close>

lemma \<open>(\<Phi> \<Turnstile>\<^sub>H {\<psi>}) = (\<Phi> \<union> {\<^bold>\<not>\<psi>} \<Turnstile>\<^sub>H {form.Bot})\<close>
proof -
  have \<open>\<forall>(I :: nterm intrp). \<not> (satisfies I {form.Bot})\<close>
    unfolding satisfies_def using ex_beta holds.simps(1) by blast
  then have \<open>\<forall>(I :: nterm intrp). \<not> (satisfies I (groundings {form.Bot}))\<close>
    using ground_bot by simp
  show \<open>(\<Phi> \<Turnstile>\<^sub>H {\<psi>}) = (\<Phi> \<union> {\<^bold>\<not>\<psi>} \<Turnstile>\<^sub>H {form.Bot})\<close>
  proof
    assume entails_phi_psi: \<open>\<Phi> \<Turnstile>\<^sub>H {\<psi>}\<close>
    show \<open>\<Phi> \<union> {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>} \<Turnstile>\<^sub>H {\<^bold>\<bottom>}\<close>
    proof (cases \<open>\<exists>(I :: nterm intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I \<and>
       satisfies I (groundings \<Phi>)\<close>)
      case True
      show ?thesis 
        unfolding entails_herbrand_def
      proof clarsimp
        fix I :: "nterm intrp"
        assume i_lang: \<open>is_interpretation (FOL_Syntax.language (\<^bold>\<bottom> \<triangleright> \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom> \<triangleright> \<Phi>)) I\<close> and
          i_sat_neg: \<open>satisfies I (groundings (\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom> \<triangleright> \<Phi>))\<close>
        then have i_sat_phi: \<open>satisfies I (groundings \<Phi>)\<close> and 
          i_sat_npsi: \<open>satisfies I (groundings {\<^bold>\<not>\<psi>})\<close>
          using ground_dist sat_union insert_is_Un by metis+
        have i_lang_simp: \<open>is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I\<close>
          using i_lang language_with_Bot language_not language_union by (metis fst_conv insert_is_Un
              language_def prod.sel(2) sup_commute)
        have i_sat_psi: \<open>satisfies I (groundings {\<psi>})\<close>
          using i_sat_phi i_lang_simp entails_phi_psi unfolding entails_herbrand_def by blast
        then have \<open>\<not> (satisfies I (groundings {\<^bold>\<not>\<psi>}))\<close>
          using sat_ground_neg by blast
        then have \<open>False\<close>
          using i_sat_npsi by blast
        then show \<open>satisfies I (groundings {\<^bold>\<bottom>})\<close>
          by blast
      qed
    next
      case False
      then have all_i_neg: 
        \<open>\<forall>(I :: nterm intrp). \<not> (is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I) \<or>
        \<not> (satisfies I (groundings \<Phi>))\<close>
        by blast
      have is_intrp: \<open>is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>} \<union> {\<^bold>\<bottom>})) I = 
        is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I\<close> for I :: "nterm intrp"
        using language_with_Bot language_not language_union by (metis language_def prod.inject)
      have  \<open>\<not> (satisfies I (groundings \<Phi>)) \<Longrightarrow> \<not> satisfies I (groundings (\<Phi> \<union> {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>}))\<close>
        for I :: "nterm intrp"
        using sat_union[of I "groundings \<Phi>"] ground_dist by presburger
      then have \<open>\<nexists>(I :: nterm intrp). 
        is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>} \<union> {\<^bold>\<bottom>})) I \<and> 
        satisfies I (groundings (\<Phi> \<union> {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>}))\<close>
        using is_intrp all_i_neg by blast        
      then show ?thesis
        unfolding entails_herbrand_def by blast
    qed
  next
    assume \<open>\<Phi> \<union> {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>} \<Turnstile>\<^sub>H {\<^bold>\<bottom>}\<close>
    then have \<open>\<forall>(I :: nterm intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I \<longrightarrow> 
      \<not> (satisfies I (groundings (\<Phi> \<union> {\<^bold>\<not>\<psi>})))\<close>
      using bot_not_sat ground_bot language_with_Bot language_not language_union
      unfolding entails_herbrand_def by (metis language_def prod.inject)
    then have a: \<open>\<forall>(I :: nterm intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I \<longrightarrow> 
      \<not> (satisfies I (groundings \<Phi>) \<and> satisfies I (groundings {\<^bold>\<not>\<psi>}))\<close>
      using sat_union ground_dist by metis
    then have \<open>\<forall>(I :: nterm intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> {\<psi>})) I \<longrightarrow>
       FOL_Semantics.satisfies I (groundings \<Phi>) \<longrightarrow>
      \<not> FOL_Semantics.satisfies I (groundings {\<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>})\<close>
      by blast
    
    then show \<open>\<Phi> \<Turnstile>\<^sub>H {\<psi>}\<close>
      unfolding entails_herbrand_def  
      sorry
  qed
qed



fun nlits_as_form_set :: \<open>form \<Rightarrow> form set option\<close> where
  \<open>nlits_as_form_set form.Bot = Some {}\<close>
| \<open>nlits_as_form_set ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = 
    (if (is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>)) 
     then (Some ({\<psi>} \<union> (the (nlits_as_form_set \<phi>1))))
     else None)\<close>
| \<open>nlits_as_form_set _ = None\<close>

definition neg_clause :: \<open>form \<Rightarrow> form set\<close> where
  \<open>neg_clause \<phi> = {\<^bold>\<not> l |l. l \<in> (the (nlits_as_form_set \<phi>))}\<close>

lemma functions_in_form_set: 
  \<open>is_clausal C \<Longrightarrow> functions_forms (the (nlits_as_form_set C)) = functions_forms {C}\<close>
  unfolding functions_forms_def by (induction C rule: nlits_as_form_set.induct) auto

lemma predicates_in_form_set:
  \<open>is_clausal C \<Longrightarrow> FOL_Syntax.predicates (the (nlits_as_form_set C)) = FOL_Syntax.predicates {C}\<close>
  unfolding FOL_Syntax.predicates_def by (induction C rule: nlits_as_form_set.induct) auto

lemma language_neg_clause: \<open>is_clausal C \<Longrightarrow>
    FOL_Syntax.language (neg_clause C) = FOL_Syntax.language {C}\<close>
  unfolding FOL_Syntax.language_def
proof (clarsimp, rule conjI)
  assume clause_C: \<open>is_clausal C\<close>
  have \<open>functions_forms (neg_clause C) =
    functions_forms (the (nlits_as_form_set C))\<close>
    unfolding neg_clause_def functions_forms_def by fastforce
  then show \<open>functions_forms (neg_clause C) = functions_forms {C}\<close>
    using functions_in_form_set[OF clause_C] by argo
next
  assume clause_C: \<open>is_clausal C\<close>
  have \<open>FOL_Syntax.predicates (neg_clause C) = FOL_Syntax.predicates (the (nlits_as_form_set C))\<close>
    unfolding neg_clause_def FOL_Syntax.predicates_def by fastforce
  then show \<open>FOL_Syntax.predicates (neg_clause C) = FOL_Syntax.predicates {C}\<close>
    using predicates_in_form_set[OF clause_C] by argo
qed



(*
find_theorems  \<open>\<forall>_\<in>{_}. _\<close>
lemma super_obvious: \<open>(\<forall>x. x \<in> {a} \<longrightarrow> P x) \<equiv> P a\<close> by auto
lemma duper_obvious: \<open>a \<longrightarrow> (b \<longrightarrow> c) \<equiv> ((b \<and> a) \<longrightarrow> c)\<close> by argo
find_theorems name: type name: empty
lemma \<open>\<exists>x. P x \<and> Q x \<Longrightarrow> \<forall>x. P x \<and> Q x \<equiv> (\<forall>x. P x) \<and> (\<forall>x. Q x)\<close>
  by (smt (verit, del_insts))
lemma \<open>\<forall>x. P x \<and> Q x \<Longrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)\<close> by auto
lemma \<open> (\<forall>x. P x) \<and> (\<forall>x. Q x) \<Longrightarrow> \<forall>x. P x \<and> Q x\<close> by auto
*)

lemma union_singleton_under_all: \<open>(\<forall>\<beta> \<phi>. (P \<beta> \<and> \<phi> \<in> {\<psi>} \<union> B) \<longrightarrow> R \<beta> \<phi>) \<equiv> 
  (\<forall>\<beta> \<phi>. P \<beta> \<and> \<phi> \<in> {\<psi>} \<longrightarrow> R \<beta> \<phi>) \<and>  (\<forall>\<beta> \<phi>. P \<beta> \<and> \<phi> \<in> B \<longrightarrow> R \<beta> \<phi>)\<close>
  by (smt (verit) Un_iff singleton_iff)

(* this is false because of valuations! *)
(* lemma sat_or: \<open>satisfies I {\<phi> \<^bold>\<or> \<psi>} = (satisfies I {\<phi>} \<or> satisfies I {\<psi>})\<close>
  unfolding satisfies_def
  oops *)


fun add_forall :: "nat list \<Rightarrow> form \<Rightarrow> form" where
  \<open>add_forall [] \<phi> = \<phi>\<close>
| \<open>add_forall (v # V) \<phi> = add_forall V (\<^bold>\<forall>v\<^bold>. \<phi>)\<close>

definition close_univ :: \<open>form \<Rightarrow> form\<close> where
  \<open>close_univ \<phi> = add_forall (sorted_list_of_set(FOL_Syntax.FV \<phi>)) \<phi>\<close>


lemma holds_FV_equiv_forall: 
  \<open>(\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (\<forall>a\<in>FOL_Semantics.dom I. I,\<beta>(x := a) \<Turnstile> \<phi>)) =
    (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
proof
  show \<open>\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> I,\<beta> \<Turnstile> \<phi> \<Longrightarrow>
    \<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (\<forall>a\<in>FOL_Semantics.dom I. I,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by auto
next
  show \<open>\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (\<forall>a\<in>FOL_Semantics.dom I. I,\<beta>(x := a) \<Turnstile> \<phi>) \<Longrightarrow>
    \<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> I,\<beta> \<Turnstile> \<phi>\<close>
  proof clarsimp
    fix \<beta> :: "nat \<Rightarrow> 'a"
    assume sat: \<open>\<forall>\<beta>. (\<forall>v. \<beta> v \<in> FOL_Semantics.dom I) \<longrightarrow> (\<forall>a\<in>FOL_Semantics.dom I. I,\<beta>(x := a) \<Turnstile> \<phi>)\<close> and
      val: \<open>\<forall>v. \<beta> v \<in> FOL_Semantics.dom I\<close>
    then have \<open>I,\<beta>(x := \<beta> x) \<Turnstile> \<phi>\<close>
      by blast
    moreover have \<open>\<beta>(x := \<beta> x) = \<beta>\<close>
      by blast
    ultimately show \<open>I,\<beta> \<Turnstile> \<phi>\<close>
      by auto
  qed
qed

lemma sat_FV_equiv_forall: \<open>satisfies I {\<^bold>\<forall>x\<^bold>. \<phi>} = satisfies I {\<phi>}\<close>
  unfolding satisfies_def using holds_FV_equiv_forall by simp

lemma sat_closed_equiv: \<open>satisfies I {close_univ \<phi>} = satisfies I {\<phi>}\<close>
  unfolding close_univ_def
proof (induction "sorted_list_of_set (FOL_Syntax.FV \<phi>)" arbitrary: \<phi>)
  case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case
    using sat_FV_equiv_forall by (metis FV.simps(4) add_forall.elims finite_FV list.distinct(1)
      list.inject sorted_list_of_set.sorted_key_list_of_set_eq_Nil_iff sorted_list_of_set_nonempty)
qed

(*
lemma sat_in_form_set: \<open>is_clausal C \<Longrightarrow> C \<noteq> form.Bot \<Longrightarrow>
  (\<exists>\<phi> \<in> (the (nlits_as_form_set C)). satisfies I {\<phi>}) = satisfies I {C}\<close>
  unfolding satisfies_def
proof (induction C rule: nlits_as_form_set.induct)
  case 1
  then show ?case
    by blast
next
  case (2 \<phi>1 \<phi>2 \<psi>)
  have is_clausal_phi1: \<open>is_clausal \<phi>1\<close>
    using 2(2) by simp
  have psi_eq: \<open>\<phi>2 = \<psi>\<close>
    using 2(2) by simp
  have split_lits: \<open>the (nlits_as_form_set (\<phi>1 \<^bold>\<longrightarrow> \<phi>2 \<^bold>\<longrightarrow> \<psi>)) = 
    {\<psi>} \<union> (the (nlits_as_form_set \<phi>1))\<close>
    using 2(2) by simp
  then show ?case
  proof (cases \<open>\<phi>1 = form.Bot\<close>)
    case True
    then show ?thesis
      using 2(2) by auto
  next
    case False
    have \<open>(\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<phi>1 \<^bold>\<longrightarrow> \<phi>2 \<^bold>\<longrightarrow> \<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>) =
      (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<phi>1) \<or> (I,\<beta> \<Turnstile> \<psi>))\<close>
      using holds_or by (smt (verit) psi_eq singleton_iff)
    also have \<open>... = (\<forall>\<beta>. (is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<phi>1)) \<or> (is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<psi>)))\<close>
      by blast
    also have \<open>... = (\<forall>\<beta>. (\<forall>\<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<phi>1} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>) \<or>
      (\<forall>\<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>))\<close>
      by blast
    show ?thesis
      using 2(1)[OF 2(2) is_clausal_phi1 False] holds_or psi_eq split_lits
      sorry
  qed
    (*have \<open>(\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> the (nlits_as_form_set (\<phi>1 \<^bold>\<longrightarrow> \<phi>2 \<^bold>\<longrightarrow> \<psi>)) \<longrightarrow> I,\<beta> \<Turnstile> \<phi>) \<equiv>
      (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<psi>} \<union> the (nlits_as_form_set \<phi>1) \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
      using split_lits by auto
    also have \<open>... \<equiv> (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>) \<and> 
      (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> the (nlits_as_form_set \<phi>1) \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
      using union_singleton_under_all[of "\<lambda>\<beta>. is_valuation I \<beta>" \<psi> "the (nlits_as_form_set \<phi>1)"
          "\<lambda>\<beta> \<phi>. I,\<beta> \<Turnstile> \<phi>"] .
    also have \<open>... \<equiv> (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>) \<and> 
      (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<phi>1} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
      using 2(1)[OF 2(2) is_clausal_phi1 False] by auto
    also have \<open>... \<equiv> (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<psi>} \<union> {\<phi>1} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
      by (smt (verit) Un_iff)
    also have \<open>... \<equiv> (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {\<phi>1 \<^bold>\<or> \<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
      
      sorry*)
next
  case ("3_1" v va)
  then show ?case sorry
next
  case ("3_2" va)
  then show ?case sorry
next
  case ("3_3" vb vc va)
  then show ?case sorry
next
  case ("3_4" vb vc va)
  then show ?case sorry
next
  case ("3_5" v va)
  then show ?case sorry
qed
*)



lemma \<open>FOL_Syntax.FV (\<phi> \<^bold>\<or> \<psi>) = {} \<Longrightarrow> satisfies I {\<phi> \<^bold>\<or> \<psi>} = satisfies I {\<phi>} \<or> satisfies I {\<psi>}\<close>
proof -
  assume closed: \<open>FOL_Syntax.FV (\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<longrightarrow> \<psi>) = {}\<close>
  {
    assume sat_or: \<open>satisfies I {\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<longrightarrow> \<psi>}\<close> and not_sat_phi: \<open>\<not> satisfies I {\<phi>}\<close>
    then have \<open>satisfies I {\<psi>}\<close>
      using holds_or unfolding satisfies_def
      by (metis FV.simps(3) closed holds_closed_ex_equiv_all_val insertI1 singletonD sup_eq_bot_iff)
  }
  moreover{
    assume sat_phi: \<open>satisfies I {\<phi>}\<close> and sat_psi: \<open>satisfies I {\<psi>}\<close>
    then have \<open>satisfies I {\<phi> \<^bold>\<or> \<psi>}\<close>
      unfolding satisfies_def by auto
  }
  ultimately show \<open>satisfies I {\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<longrightarrow> \<psi>} = satisfies I {\<phi>} \<or> satisfies I {\<psi>}\<close>
    by (metis holds_or insertI1 satisfies_def singletonD)
qed



lemma sat_singleton_simp: \<open>satisfies I {\<phi>} = (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
  unfolding satisfies_def by blast

(*
lemma \<open>(\<not> (satisfies I {\<phi> \<^bold>\<or> \<psi>})) = (satisfies I {\<^bold>\<not>\<phi>, \<^bold>\<not>\<psi>})\<close>
  unfolding satisfies_def
proof -
  have \<open>(\<not>(satisfies I {\<phi> \<^bold>\<or> \<psi>})) =
    (\<not>(\<forall>\<beta> \<phi>'. is_valuation I \<beta> \<and> \<phi>' \<in> {\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<longrightarrow> \<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>'))\<close>
    unfolding satisfies_def by simp
  also have \<open>... = (\<not>(\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<phi> \<or> I,\<beta> \<Turnstile> \<psi>)))\<close>
    using holds_or by auto
  also have \<open>... = (\<exists>\<beta>. is_valuation I \<beta> \<and> ((\<not> I,\<beta> \<Turnstile> \<phi>) \<and> (\<not> I,\<beta> \<Turnstile> \<psi>)))\<close>
    by auto
  also have \<open>... = (\<exists>\<beta>. is_valuation I \<beta> \<and> (I,\<beta> \<Turnstile> \<^bold>\<not> \<phi>) \<and> (I,\<beta> \<Turnstile> \<^bold>\<not>\<psi>))\<close>
    using holds_not by auto
  also have \<open>... = (\<exists>\<beta>. is_valuation I \<beta> \<and> (I,\<beta> \<Turnstile> \<^bold>\<not> \<phi>)) \<and> (\<exists>\<beta>. is_valuation I \<beta> \<and> (I,\<beta> \<Turnstile> \<^bold>\<not>\<psi>))\<close>
    sorry
  have \<open>(\<forall>\<beta> \<phi>'. is_valuation I \<beta> \<and> \<phi>' \<in> {\<^bold>\<not>\<phi>, \<^bold>\<not>\<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>') =
    (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<^bold>\<not>\<phi>) \<and> (I,\<beta> \<Turnstile> \<^bold>\<not>\<psi>))\<close>
    using holds_not by blast
  also have \<open>... \<Longrightarrow>
    ((\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<^bold>\<not>\<phi>)) \<and> (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<^bold>\<not>\<psi>)))\<close>
    by blast
  have \<open>((\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<^bold>\<not>\<phi>)) \<and> (\<forall>\<beta>. is_valuation I \<beta> \<longrightarrow> (I,\<beta> \<Turnstile> \<^bold>\<not>\<psi>))) =
    satisfies I {\<^bold>\<not>\<phi>} \<and> satisfies I {\<^bold>\<not>\<psi>}\<close>
    using sat_singleton_simp[of I "\<^bold>\<not>\<phi>"] sat_singleton_simp[of I "\<^bold>\<not>\<psi>"] 
    sorry
  show \<open>(\<not> (\<forall>\<beta> \<phi>'. is_valuation I \<beta> \<and> \<phi>' \<in> {\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<longrightarrow> \<psi>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>')) = 
    (\<forall>\<beta> \<phi>'. is_valuation I \<beta> \<and> \<phi>' \<in> {\<phi> \<^bold>\<longrightarrow> \<^bold>\<bottom>, \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>')\<close>
    sorry
qed

lemma sat_neg_clause: \<open>is_clausal C \<Longrightarrow> (satisfies I (neg_clause C)) = (\<not> (satisfies I {C}))\<close>
  unfolding satisfies_def neg_clause_def 
proof -
  assume \<open>is_clausal C\<close>
  then have \<open>Finite_Set.finite (the (nlits_as_form_set C))\<close>
    sorry
  show \<open>is_clausal C \<Longrightarrow>
    \<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {l \<^bold>\<longrightarrow> \<^bold>\<bottom> |l. l \<in> the (nlits_as_form_set C)} \<longrightarrow> I,\<beta> \<Turnstile> \<phi> \<Longrightarrow>
    \<not> (\<forall>\<beta> \<phi>. is_valuation I \<beta> \<and> \<phi> \<in> {C} \<longrightarrow> I,\<beta> \<Turnstile> \<phi>)\<close>
  proof (induction "the (nlits_as_form_set C)" rule:finite.induct)
  sorry

lemma 
  assumes \<open>is_clausal C\<close> and
    \<open>\<Phi> \<Turnstile>\<^sub>H {C}\<close>
  shows \<open>\<Phi> \<union> neg_clause C \<Turnstile>\<^sub>H {form.Bot}\<close>
proof (cases \<open>\<exists>(I :: (nat, nat) term intrp). is_interpretation (FOL_Syntax.language (\<Phi> \<union> {C})) I \<and>
  satisfies I (groundings \<Phi>)\<close>)
  case True
  show ?thesis
    unfolding entails_herbrand_def
  proof clarsimp
    fix I :: "(nat, nat) term intrp"
    show \<open>FOL_Semantics.satisfies I (groundings {form.Bot})\<close>
      sorry
  qed
next
  case False
  show ?thesis
    unfolding entails_herbrand_def
  proof clarsimp
    fix I :: "(nat, nat) term intrp"
    assume is_interp: \<open>is_interpretation (FOL_Syntax.language (form.Bot \<triangleright> \<Phi> \<union> neg_clause C)) I\<close> and
      sat: \<open>FOL_Semantics.satisfies I (groundings (\<Phi> \<union> neg_clause C))\<close>
    have \<open>is_interpretation (FOL_Syntax.language (\<Phi> \<union> {C})) I\<close>
      using language_neg_clause[OF assms(1)] language_union
      by (metis (no_types, lifting) fst_conv insert_is_Un is_interp is_interpretation_def
          language_def language_with_Bot sup_commute)
    moreover have \<open>satisfies I (groundings \<Phi>)\<close>
      using sat ground_dist sat_union_left by metis
    ultimately show \<open>FOL_Semantics.satisfies I (groundings {form.Bot})\<close>
      using False by blast
qed
*)


subsection \<open>Aligning entailment\<close>




section \<open>Clausal compactness\<close>

thm COMPACT_LS

lemma finite_to_form_set: \<open>Finite_Set.finite Cs \<Longrightarrow> Finite_Set.finite (nclauses_to_form_set Cs)\<close>
  unfolding nclauses_to_form_set_def by blast

lemma finite_from_form_set: \<open>Finite_Set.finite (nclauses_to_form_set Cs) \<Longrightarrow> Finite_Set.finite Cs\<close>
  by (metis clauses_to_form_set_conv finite_subset_image nclauses_to_form_set_def subset_eq)

lemma subset_to_form_set: \<open>Ds \<subseteq> Cs \<Longrightarrow> (nclauses_to_form_set Ds) \<subseteq> (nclauses_to_form_set Cs)\<close>
  unfolding nclauses_to_form_set_def by blast

lemma subset_from_form_set: \<open>(nclauses_to_form_set Ds) \<subseteq> (nclauses_to_form_set Cs) \<Longrightarrow> Ds \<subseteq> Cs\<close>
  by (metis clauses_to_form_set_conv nclauses_to_form_set_def subset_imageE)

theorem clausal_compactness: \<open>(\<forall>Ds. Finite_Set.finite Ds \<and> Ds \<subseteq> Cs \<longrightarrow> 
  (\<exists>(I :: 'a intrp). is_interpretation (FOL_Syntax.language (nclauses_to_form_set Cs)) I \<and> 
    satisfies I (nclauses_to_form_set Ds))) \<longrightarrow> 
  (\<exists>(J :: (nat, nat) term intrp). is_interpretation (FOL_Syntax.language (nclauses_to_form_set Cs)) J \<and> 
    satisfies J (nclauses_to_form_set Cs))\<close>
proof clarsimp
  assume subsets_entail: \<open>\<forall>Ds. (Finite_Set.finite Ds \<and> Ds \<subseteq> Cs \<longrightarrow> 
  (\<exists>(I :: 'a intrp). is_interpretation (FOL_Syntax.language (nclauses_to_form_set Cs)) I \<and> 
    satisfies I (nclauses_to_form_set Ds)))\<close>
  have \<open>\<forall>\<phi>s. Finite_Set.finite \<phi>s \<and> \<phi>s \<subseteq> (nclauses_to_form_set Cs) \<longrightarrow> 
  (\<exists>(I :: 'a intrp). is_interpretation (FOL_Syntax.language (nclauses_to_form_set Cs)) I \<and> 
    satisfies I \<phi>s)\<close>
  proof clarsimp
    fix \<phi>s
    assume fin_phi: \<open>Finite_Set.finite \<phi>s\<close> and
      \<open>\<phi>s \<subseteq> nclauses_to_form_set Cs\<close>
    then obtain Ds where Ds_is: \<open>\<phi>s = nclauses_to_form_set Ds\<close> and Ds_in: \<open>Ds \<subseteq> Cs\<close>
      by (metis nclauses_to_form_set_def subset_image_iff)
    moreover have \<open>Finite_Set.finite Ds\<close>
      using Ds_is finite_from_form_set fin_phi by simp
    ultimately show \<open>\<exists>(I::'a intrp). is_interpretation (FOL_Syntax.language (nclauses_to_form_set Cs)) I \<and> 
      FOL_Semantics.satisfies I \<phi>s\<close>
      using spec[OF subsets_entail, of Ds] by blast
  qed
  then show \<open>\<exists>(J :: (nat, nat) term intrp). is_interpretation (FOL_Syntax.language (nclauses_to_form_set Cs)) J \<and> 
    FOL_Semantics.satisfies J (nclauses_to_form_set Cs)\<close>
    using COMPACT_LS by auto
qed



end