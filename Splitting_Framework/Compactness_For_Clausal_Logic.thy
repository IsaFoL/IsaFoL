(* Title:        Compactness in clausal logic terms
 * Author:       Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Compactness_For_Clausal_Logic
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    "hol_light_import/FOL_Syntax"
    Nested_Multisets_Ordinals.Multiset_More
    (*Weighted_Path_Order.WPO*)
begin

(* TODO: 
     - move count and related lemmas to separate file, see if it can be merged to the List theory
     - move list_from_mset to separate file, see if it can be merged to AFP Multiset_More theory
 *)

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  \<open>count [] x = 0\<close>
| \<open>count (x # xs) y = (if x = y then 1 + count xs y else count xs y)\<close>

lemma null_count: \<open>a \<notin> set l \<Longrightarrow> count l a = 0\<close>
  by (induction l) auto

lemma count_plus_one: \<open>a \<in> set l \<Longrightarrow> count (a # l) a = 1 + count l a\<close>
  by (induction l) auto

lemma length_count_one: \<open>length l = 1 \<Longrightarrow> count l a = 1 \<Longrightarrow> l = [a]\<close>
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons x l)
  have \<open>l = []\<close> using Cons(2) by simp
  moreover have \<open>x = a\<close>
    using Cons by (metis calculation count.elims count.simps(2) list.distinct(1) zero_neq_one)
  ultimately show ?case by simp
qed

lemma count_sum_cons: \<open>sum (count (a # l)) (set (a # l)) = 1 + sum (count l) (set l)\<close>
proof (cases "a \<in> set l")
  case True
  have \<open>sum (count (a # l)) (set (a # l)) = sum (count (a # l)) ((set l - {a})) + count (a # l) a\<close>
    by (simp add: sum.insert_remove)
  also have \<open>... = sum (count (a # l)) ((set l - {a})) + count l a + 1\<close>
    using count_plus_one[OF True] by auto
  also have \<open>... = sum (count l) ((set l - {a})) + count l a + 1\<close>
    by (metis DiffE count.simps(2) singletonI sum.cong)
  also have \<open>... = sum (count l) (set l) + 1\<close>
    using True by (simp add: sum.remove)
  finally show ?thesis by simp
next
  case False
  have \<open>sum (count (a # l)) (set (a # l)) = sum (count (a # l)) ((set l - {a})) + count (a # l) a\<close>
    by (simp add: sum.insert_remove)
  also have \<open>... = sum (count (a # l)) (set l) + count (a # l) a\<close>
    using False by auto
  also have \<open>... = sum (count l) (set l) + count (a # l) a\<close>
    using False by (metis count.simps(2) sum.cong)
  also have \<open>... = sum (count l) (set l) + 1\<close>
    using False by (simp add: null_count)
  finally show ?thesis
    by simp
qed

lemma length_is_sum_count: \<open>length l = sum (\<lambda>x. count l x) (set l)\<close>
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  have \<open>length (a # l) = 1 + length l\<close>
    by auto
  also have \<open>... = 1 + sum (count l) (set l)\<close>
    using Cons by simp
  also have \<open>... = sum (count (a#l)) (set (a # l))\<close>
    using count_sum_cons by metis
  finally show ?case .
qed

lemma set_as_counts: \<open>set l = {x. 0 < count l x}\<close>
  by (induction l) auto

(* shows equivalence of the definition below of list_of_mset with the one in Multiset_More *)
lemma \<open>(\<exists>l. m = mset l) \<equiv> (\<exists>l. \<forall>x. count l x = multiset.count m x)\<close> (is "?A \<equiv> ?B")
proof -
  have \<open>\<exists>l. m = mset l \<Longrightarrow> \<exists>l. \<forall>x. count l x = multiset.count m x\<close>
  proof -
    assume ?A
    then obtain l where l_is: \<open>m = mset l\<close>
      by blast
    then have \<open>count l x = multiset.count m x\<close> for x
    proof -
      fix x
      assume "m = mset l"
      then show \<open>count l x = multiset.count m x\<close>
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
            IH: \<open>\<forall>ys. length ys < length xs \<longrightarrow> (\<forall>y. y = mset ys \<longrightarrow> count ys x = multiset.count y x)\<close>
          obtain a ys where xs_is: \<open>xs = a # ys\<close>
            using False by (metis list.size(3) neq_Nil_conv)
          then have length_eq: \<open>length ys < length xs\<close>
            by simp
          obtain n where m_is: \<open>m = add_mset a n\<close>
            using m_eq xs_is by auto
          then have n_eq: \<open>n = mset ys\<close>
            using xs_is m_eq by simp
          then have \<open>count ys x = multiset.count n x\<close>
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

lemma \<open>m = mset l \<Longrightarrow> \<forall>x. count l x = multiset.count m x\<close>
proof
  fix x
  assume \<open>m = mset l\<close>
  then show \<open>count l x = multiset.count m x\<close>
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
        IH: \<open>\<forall>ys. length ys < length xs \<longrightarrow> (\<forall>y. y = mset ys \<longrightarrow> count ys x = multiset.count y x)\<close>
      obtain a ys where xs_is: \<open>xs = a # ys\<close>
        using False by (metis list.size(3) neq_Nil_conv)
      then have length_eq: \<open>length ys < length xs\<close>
        by simp
      obtain n where m_is: \<open>m = add_mset a n\<close>
        using m_eq xs_is by auto
      then have n_eq: \<open>n = mset ys\<close>
        using xs_is m_eq by simp
      then have \<open>count ys x = multiset.count n x\<close>
        using IH length_eq n_eq by blast
      then show ?thesis
        using m_is xs_is by simp
    qed
  qed
qed

definition list_of_mset :: "'a multiset \<Rightarrow> 'a list" where
  \<open>list_of_mset m = (SOME l. (\<forall>x. count l x = (multiset.count m x)))\<close>

lemma empty_list_of_mset: "list_of_mset {#} = []"
  unfolding list_of_mset_def
proof -
  have "\<forall>as. ([] \<noteq> as \<or> (\<forall>a asa. (a::'a) # asa \<noteq> as)) \<and> ((\<exists>a asa. a # asa = as) \<or> [] = as)"
    by (metis (no_types) neq_Nil_conv)
  then obtain aa :: "'c \<Rightarrow> 'a list \<Rightarrow> 'a" and aas :: "'c \<Rightarrow> 'a list \<Rightarrow> 'a list" and
    aaa :: "'c \<Rightarrow> 'a list \<Rightarrow> 'a" and aasa :: "'c \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    f1: "\<forall>c as. ([] \<noteq> as \<or> (\<forall>a asa. a # asa \<noteq> as)) \<and> (aa c as # aas c as = as \<or> [] = as)"
    by moura
  have "\<forall>a. count [] (a::'a) = multiset.count {#} a"
    by simp
  then have "\<forall>a. 0 = count (SOME as. \<forall>a. count as (a::'a) = multiset.count {#} a) a"
    by (smt (z3) tfl_some zero_multiset.rep_eq)
  then show "(SOME as. \<forall>a. count as (a::'a) = multiset.count {#} a) = []"
    using f1 by (metis (lifting) One_nat_def add_is_0 count.simps(2) nat.simps(3))
qed

lemma list_of_mset_always_exists: \<open>\<exists>l. (\<forall>x. count l x = (Multiset.count m x))\<close>
proof (induction m)
  case empty
  then show ?case
    by (metis count.simps(1) count_empty)
next
  case (add a m)
  then obtain l where l_is: \<open>\<forall>x. count l x = multiset.count m x\<close>
    by blast
  then have \<open>\<forall>x. count (a#l) x = multiset.count (add_mset a m) x\<close>
    by simp
  then show ?case by blast
qed

thm someI_ex

lemma count_list_of_mset: \<open>\<forall>x. count (list_of_mset m) x = (Multiset.count m x)\<close>
  using someI_ex[OF list_of_mset_always_exists] unfolding list_of_mset_def .

lemma nempty_mset_to_list: \<open>m \<noteq> {#} \<Longrightarrow> list_of_mset m \<noteq> []\<close>
  using count_list_of_mset
  by (metis count.simps(1) multiset_nonemptyE not_in_iff)

lemma count_x_list_of_mset: \<open>count (list_of_mset m) x = multiset.count m x\<close>
  using count_list_of_mset by fast

lemma set_list_of_mset_equiv_set_mset: \<open>set (list_of_mset m) = set_mset m\<close>
proof (induction m)
  case empty
  then show ?case
    using empty_list_of_mset by auto
next
  case (add a m)
  have \<open>set (list_of_mset (add_mset a m)) = {a} \<union> set (list_of_mset m)\<close>
  proof -
    have \<open>set (list_of_mset (add_mset a m)) = {x. 0 < count (list_of_mset (add_mset a m)) x}\<close>
      using set_as_counts by fast
    also have \<open>... = {x. 0 < multiset.count (add_mset a m) x}\<close>
      using count_x_list_of_mset by metis
    also have \<open>... = {a} \<union> {x. 0 < multiset.count m x}\<close>
      by auto
    also have \<open>... = {a} \<union> {x. 0 < count (list_of_mset m) x}\<close>
      using count_x_list_of_mset by metis
    also have \<open>... = {a} \<union> set (list_of_mset m)\<close>
      using set_as_counts by fast
    finally show \<open>set (list_of_mset (add_mset a m)) = {a} \<union> set (list_of_mset m)\<close> .
  qed
  then show ?case
    using add by simp
qed

lemma sum_count_add_mset_list: 
  \<open>sum (count (list_of_mset (add_mset a m))) (set (list_of_mset (add_mset a m))) =
    1 + sum (count (list_of_mset m)) (set (list_of_mset m))\<close>
proof -
  have \<open>sum (count (list_of_mset (add_mset a m))) (set (list_of_mset (add_mset a m))) =
    sum (\<lambda>x. multiset.count (add_mset a m) x) (set (list_of_mset (add_mset a m)))\<close>
    using count_x_list_of_mset by meson
  also have \<open>... = sum (\<lambda>x. multiset.count (add_mset a m) x) (set_mset (add_mset a m))\<close>
    using set_list_of_mset_equiv_set_mset by metis
  also have \<open>... = 1 + sum (\<lambda>x. multiset.count m x) (set_mset m)\<close>
    by (metis plus_1_eq_Suc size_add_mset size_multiset_overloaded_eq)
  also have \<open>... = 1 + sum (\<lambda>x. multiset.count m x) (set (list_of_mset m))\<close>
    using set_list_of_mset_equiv_set_mset by metis
  also have \<open>... = 1 + sum (count (list_of_mset m)) (set (list_of_mset m))\<close>
    using count_x_list_of_mset by metis
  finally show ?thesis . 
qed

lemma size_is_length_list_of_mset: \<open>size M = length (list_of_mset M)\<close>
proof (induction M)
  case empty
  then show ?case
    using empty_list_of_mset by simp
next
  case (add x M)
  have \<open>length (list_of_mset (add_mset x M)) = length (list_of_mset M) + 1\<close>
  proof -
    let ?l_add = \<open>list_of_mset (add_mset x M)\<close> and ?l = \<open>list_of_mset M\<close>
    have \<open>length ?l_add = sum (\<lambda>x. count ?l_add x) (set ?l_add)\<close>
      using length_is_sum_count[of ?l_add] .
    also have \<open>... = 1 + sum (\<lambda>x. count ?l x) (set ?l)\<close>
      using sum_count_add_mset_list by fast
    also have \<open>... = 1 + length (list_of_mset M)\<close>
      using length_is_sum_count[of ?l] by argo
    finally show \<open>length (list_of_mset (add_mset x M)) = length (list_of_mset M) + 1\<close>
      by auto
  qed
  then show ?case
    using add by auto
qed

lemma list_of_msingleton: \<open>list_of_mset {#x#} = [x]\<close>
proof -
  have \<open>length (list_of_mset {#x#}) = 1\<close>
    using size_is_length_list_of_mset by (metis size_single)
  moreover have \<open>count (list_of_mset {#x#}) x = 1\<close>
    by (simp add: count_x_list_of_mset)
  ultimately show ?thesis
    using length_count_one by fast
qed

lemma length_list_of_add_mset: \<open>length (list_of_mset (add_mset x M)) = length (list_of_mset M) + 1\<close>
proof (induction M)
  case empty
  then show ?case
    using list_of_msingleton
    by (simp add: length_is_sum_count sum_count_add_mset_list)
next
  case (add x M)
  then show ?case
    using size_is_length_list_of_mset by (metis Suc_eq_plus1 size_add_mset)
qed

lemma count_list_mset: \<open>count l x = multiset.count (mset l) x\<close>
  by (induction l) auto

lemma \<open>count (Multiset_More.list_of_mset m) x = multiset.count m x\<close>
  using count_list_mset by (metis mset_list_of_mset)

lemma count_mset_list_of_mset: \<open>multiset.count (mset (list_of_mset m)) x = multiset.count m x\<close>
  using count_list_mset by (metis count_x_list_of_mset)

lemma mset_list_of_mset[simp]: \<open>mset (list_of_mset m) = m\<close>
  using count_mset_list_of_mset by (metis multi_count_eq)

lemma list_of_mset_exi: "\<exists>l. m = mset l"
  using mset_list_of_mset by metis

lemma \<open>mset l = mset (list_of_mset m) \<Longrightarrow> mset l = m\<close>
  by simp

lemma \<open>mset (list_of_mset (add_mset a m)) = add_mset a (mset (list_of_mset m))\<close>
  by simp

(* alignments for atoms *)
datatype natom =
  Bot (\<open>\<^bold>\<bottom>\<close>)
  | Atom (pred:nat) (args:\<open>nterm list\<close>)

(*find_theorems name: wpo_s name: WPO *)

(*
instantiation natom :: preorder
begin

definition less_natom :: "natom \<Rightarrow> natom \<Rightarrow> bool" where
  \<open>less_natom a b \<longleftrightarrow> (a = natom.Bot \<and> b \<noteq> natom.Bot)\<close>

definition less_eq_natom :: "natom \<Rightarrow> natom \<Rightarrow> bool" where
  \<open>less_eq_natom a b \<longleftrightarrow> True\<close>

instance apply intro_classes sorry

end
*)

lemma count_natom: \<open>OFCLASS(natom,countable_class)\<close>
  by countable_datatype

instantiation natom :: countable
begin
instance using count_natom by simp
end

(*
instantiation natom :: wellorder
begin

definition natom_less_eq (infix \<open>\<le>\<close> 50) where
\<open>natom_less_eq (a::natom) b \<longleftrightarrow> (to_nat a) \<le> (to_nat b)\<close>

definition natom_less (infix \<open><\<close> 50) where
\<open>natom_less (a::natom) b \<longleftrightarrow> (to_nat a) < (to_nat b)\<close>

instance
proof
  fix x y :: natom 
  show \<open>(natom_less x y) = ((natom_less_eq x y) \<and> \<not> (natom_less_eq y x))\<close>
  sorry
qed 
end
*)

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

(* alignments for literals *)
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

(* alignments for clauses *)
type_synonym nclause = "natom clause"

fun nlit_list_to_form :: "nlit list \<Rightarrow> form" where
  \<open>nlit_list_to_form [] = form.Bot\<close>
| \<open>nlit_list_to_form (a # as) = nlit_list_to_form as \<^bold>\<or> (nlit_to_form a)\<close>

definition nclause_to_form :: "nclause \<Rightarrow> form" where
  \<open>nclause_to_form C = nlit_list_to_form (list_of_mset C)\<close>

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
  unfolding nclause_from_form_def nclause_to_form_def by (simp add: empty_list_of_mset)
next
  case False
  then obtain l ls where l_ls_are: \<open>list_of_mset C = l # ls\<close>
    by (metis mset_list_of_mset mset.simps(1) neq_Nil_conv)
  then have C_as_form: \<open>nclause_to_form C  = (nlit_list_to_form ls) \<^bold>\<or> (nlit_to_form l)\<close>
    using nclause_to_form_def by fastforce
  have \<open>is_clausal (nclause_to_form C)\<close>
    using is_clausal_nclause[of C] .
  then have \<open>nlit_list_from_form (nclause_to_form C) =
    Some ((the (form_to_nlit (nlit_to_form l))) # (the (nlit_list_from_form (nlit_list_to_form ls))))\<close>
    using C_as_form by auto
  also have \<open>... = Some (l # ls)\<close>
    using nlit_list_form_conv by auto
  finally show ?thesis
    unfolding nclause_from_form_def nclause_to_form_def
    by (metis mset_list_of_mset l_ls_are option.sel option.simps(9))
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

(* this doesn't hold because the literals may change ordering during the transformation process *)
(* lemma \<open>is_clausal \<phi> \<Longrightarrow> nclause_to_form (the (nclause_from_form \<phi>)) = \<phi>\<close> *)
(* What we know is that the transformation returns a clause with the same literals as the original
 *  formula if it is indeed a clause *)
lemma \<open>is_clausal \<phi> \<Longrightarrow> is_clausal (nclause_to_form (the (nclause_from_form \<phi>)))\<close>
  using is_clausal_nclause[of "the (nclause_from_form \<phi>)"] .

fun nlit_mset_from_form :: "form \<Rightarrow> nclause option" where
  \<open>nlit_mset_from_form form.Bot = Some {#}\<close>
| \<open>nlit_mset_from_form ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = 
    (if (is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>)) 
     then Some (add_mset (the (form_to_nlit \<psi>)) (the (nlit_mset_from_form \<phi>1)))
     else None)\<close>
| \<open>nlit_mset_from_form _ = None\<close>

lemma \<open>is_clausal \<phi> \<Longrightarrow> (nlit_mset_from_form \<phi>) =
  (nlit_mset_from_form (nclause_to_form (the (nclause_from_form \<phi>))))\<close>
proof (induction \<phi> rule: nlit_list_from_form.induct)

  case 1
  then show ?case
    by (metis clause_to_form_conv empty_list_of_mset nclause_to_form_def nlit_list_to_form.simps(1))
next
  case (2 \<phi>1 \<phi>2 \<psi>)
(* this proof attempt looks like a dead end. try via count property of multisets *)
  have \<open>nlit_mset_from_form (\<phi>1 \<^bold>\<longrightarrow> \<phi>2 \<^bold>\<longrightarrow> \<psi>) = 
    Some (add_mset (the (form_to_nlit \<psi>)) (the (nlit_mset_from_form \<phi>1)))\<close>
    using 2(2) by simp
  have \<open>nlit_list_from_form (\<phi>1 \<^bold>\<longrightarrow> \<phi>2 \<^bold>\<longrightarrow> \<psi>) =
    Some ((the (form_to_nlit \<psi>)) # (the (nlit_list_from_form \<phi>1)))\<close>
    using 2(2) by simp
  then show ?case
    unfolding nclause_from_form_def nclause_to_form_def
    
    sorry
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

lemma \<open>is_clausal \<phi> \<Longrightarrow> (nlit_mset_from_form \<phi>) =
  (nlit_mset_from_form (nclause_to_form (the (nclause_from_form \<phi>))))\<close>
proof -
  assume is_clausal_phi: \<open>is_clausal \<phi>\<close>
  define ls where \<open>ls = list_of_mset (the (nclause_from_form \<phi>))\<close>
  have \<open>is_clausal (nlit_list_to_form ls)\<close>
    using is_clausal_nlit_list by blast
  have \<open>is_clausal \<phi> \<Longrightarrow> nlit_mset_from_form \<phi> =
    nlit_mset_from_form (nlit_list_to_form (list_of_mset (the (nclause_from_form \<phi>))))\<close>
  proof (induction \<open>(the (nclause_from_form \<phi>))\<close> arbitrary: \<phi>)
    case empty
    have not_None: \<open>nlit_list_from_form \<phi> \<noteq> None\<close>
      by (metis empty.prems form_nlit_list_conv nlit_list_from_form.simps(1)
          nlit_list_from_form.simps(2) nlit_list_to_form.cases nlit_list_to_form.simps(1)
          nlit_list_to_form.simps(2) option.distinct(1))
    then have \<open>\<phi> = form.Bot\<close>
      using empty nclause_from_form_def form_nlit_list_conv by force
    then show ?case
      by (metis empty(1) empty_list_of_mset nlit_list_to_form.simps(1))
  next
    case (add l m)
    obtain \<psi> where m_is: \<open>m = the (nclause_from_form \<psi>)\<close> and \<open>is_clausal \<psi>\<close>
      using add(2) clause_to_form_conv
      by (metis is_clausal_nclause)
    then have \<open>nlit_mset_from_form \<psi> =
       nlit_mset_from_form (nlit_list_to_form (list_of_mset (the (nclause_from_form \<psi>))))\<close>
      using add(1) by blast
    have \<open>nlit_mset_from_form \<phi> = Some (add_mset l (the (nlit_mset_from_form \<psi>)))\<close>
      using m_is add(2)
      sorry
    then show ?case sorry
  qed
 (*   case Nil
    have not_None: \<open>nlit_list_from_form \<phi> \<noteq> None\<close>
      using Nil(2) by (metis form_nlit_list_conv nlit_list_from_form.simps(1) 
          nlit_list_from_form.simps(2) nlit_list_to_form.cases nlit_list_to_form.simps(1)
          nlit_list_to_form.simps(2) option.distinct(1))
    have \<open>the (nclause_from_form \<phi>) = {#}\<close>
      using Nil(1) nempty_mset_to_list by force
    then have \<open>\<phi> = form.Bot\<close>
      using not_None nclause_from_form_def Nil.prems form_nlit_list_conv by force
    then show ?case
      using Nil.hyps by force
  next
    case (Cons a ls2)
    then show ?case sorry
  qed*)
  then show \<open>nlit_mset_from_form \<phi> =
   nlit_mset_from_form (nclause_to_form (the (nclause_from_form \<phi>)))\<close>
    unfolding nclause_to_form_def using is_clausal_phi by blast
qed

(* aligments for sets of clauses *)

end