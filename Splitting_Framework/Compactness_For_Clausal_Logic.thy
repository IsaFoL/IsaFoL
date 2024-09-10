(* Title:        Compactness in clausal logic terms
 * Author:       Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Compactness_For_Clausal_Logic
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    FOL_Syntax
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
(*proof
  fix x
  show \<open>count (list_of_mset m) x = (Multiset.count m x)\<close>
  proof (induction "list_of_mset m" arbitrary: m)
    case Nil
    then show ?case
      using empty_list_of_mset_empty count_empty
      sledgehammer
      by (metis count.simps(1) count_empty)
  next
    case (Cons a as)
    obtain m_as as_mixed where \<open>as_mixed = list_of_mset m_as\<close> \<open>mset as = mset as_mixed\<close>
      by simp
    then have \<open>count (list_of_mset m_as) x = (Multiset.count m_as x)\<close>
      using Cons(1) unfolding list_of_mset_def
      sorry
    then show ?case  sorry
  qed
(*    case empty
    then show ?case 
      using list_of_mset_empty by (metis count.simps(1) count_empty)
  next
    case (add a m)
    then show ?case sorry
  qed
    sorry
qed *)*)

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

find_theorems count
thm count_list_mset

lemma \<open>count (Multiset_More.list_of_mset m) x = multiset.count m x\<close>
  using count_list_mset by (metis mset_list_of_mset)

lemma count_mset_list_of_mset: \<open>multiset.count (mset (list_of_mset m)) x = multiset.count m x\<close>
  using count_list_mset by (metis count_x_list_of_mset)

lemma mset_list_of_mset[simp]: \<open>mset (list_of_mset m) = m\<close>
  using count_mset_list_of_mset by (metis multi_count_eq)

lemma list_of_mset_exi: "\<exists>l. m = mset l"
  using mset_list_of_mset by metis

lemma \<open>mset l = mset (list_of_mset m) \<Longrightarrow> mset l = m\<close>
proof (induction l arbitrary: m)
  case Nil
  then have \<open>m = {#}\<close>
    using empty_list_of_mset by (metis mset_zero_iff size_eq_0_iff_empty size_is_length_list_of_mset)
  then show ?case by auto
next
  case (Cons a l)
  then have \<open>mset l = mset (list_of_mset m) - {#a#}\<close>
    by (metis add_mset_remove_trivial mset.simps(2))
  obtain l2 where \<open>l2 = list_of_mset (mset (list_of_mset m) - {#a#})\<close>
    by blast
  then show ?case sorry
qed


lemma \<open>mset (list_of_mset (add_mset a m)) = add_mset a (mset (list_of_mset m))\<close>
proof (induction m arbitrary: a)
  case empty
  then show ?case
    using list_of_msingleton
    by (metis empty_list_of_mset mset.simps(2))
next
  case (add x M)
  then show ?case
     sorry (* by (metis Suc_eq_plus1 size_add_mset) *)
qed




























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

definition nclause_to_form :: "nclause \<Rightarrow> form" where
  \<open>nclause_to_form C = foldr (\<lambda>l \<phi>. \<phi> \<^bold>\<or> (nlit_to_form l)) (list_of_mset C) form.Bot\<close>

fun is_clausal :: "form \<Rightarrow> bool" where
  \<open>is_clausal form.Bot = True\<close>
| \<open>is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = ((\<phi>2 = \<psi>) \<and> (nlit_shape \<psi>) \<and> (is_clausal \<phi>1))\<close>
| \<open>is_clausal _ = False\<close>

fun nlit_list_from_form :: "form \<Rightarrow> nlit list option" where
  \<open>nlit_list_from_form form.Bot = Some []\<close>
| \<open>nlit_list_from_form ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = 
    (if (is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>)) 
     then (let ls = (the (nlit_list_from_form \<phi>1)) in Some ((the (form_to_nlit \<psi>)) # ls))
     else None)\<close>
| \<open>nlit_list_from_form _ = None\<close>

fun form_to_nclause :: \<open>form \<Rightarrow> nclause option\<close> where
  \<open>form_to_nclause form.Bot = Some {#}\<close>
| \<open>form_to_nclause ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>) = 
    (if (is_clausal ((\<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<^bold>\<longrightarrow> \<psi>)) 
     then (let ls = (the (form_to_nclause \<phi>1)) in Some (add_mset (the (form_to_nlit \<psi>))  ls))
     else None)\<close>
| \<open>form_to_nclause _ = None\<close>

definition no_bot :: "nclause \<Rightarrow> bool" where
  \<open>no_bot C = (Multiset.count C (Pos natom.Bot) = 0)\<close>

lemma no_bot_add: \<open>no_bot (add_mset l C) \<Longrightarrow> no_bot C\<close>
  unfolding no_bot_def
  by (metis Zero_neq_Suc add_mset.rep_eq)

lemma \<open>no_bot C \<Longrightarrow> the (form_to_nclause (nclause_to_form C)) = C\<close>
proof (induction "size C" arbitrary: C)
  case 0
  then show ?case
    unfolding no_bot_def nclause_to_form_def 
    using empty_list_of_mset form_to_nclause.simps(1) option.sel
    by (smt (verit) foldr.simps(1) id_apply size_eq_0_iff_empty)
next
  case (Suc x)
  then have \<open>\<exists>l ls. list_of_mset C = l # ls\<close>
    using size_is_length_list_of_mset by (metis Suc.hyps(2) length_Suc_conv)
  then obtain l ls where l_ls_are: \<open>list_of_mset C = l # ls\<close>
    by blast
  define D where \<open>D = mset ls\<close>
  then have \<open>size D = x\<close>
    using l_ls_are Suc(2)
    by (metis diff_Suc_1 length_Cons size_is_length_list_of_mset size_mset)
  moreover have \<open>no_bot D\<close>
    using Suc(3) D_def l_ls_are
    by (metis Compactness_For_Clausal_Logic.mset_list_of_mset mset.simps(2) no_bot_add)
  ultimately have \<open>the (form_to_nclause (nclause_to_form D)) = D\<close>
    using Suc(1) by blast
  find_theorems foldr
  find_theorems foldl
    (* TODO: find the right fold and detail steps in following "have" *)
  have \<open>nclause_to_form C = (nclause_to_form D \<^bold>\<or> nlit_to_form l)\<close>
    using l_ls_are D_def foldr_Cons[of "(\<lambda>l \<phi>. \<phi> \<^bold>\<longrightarrow> nlit_to_form l \<^bold>\<longrightarrow> nlit_to_form l)" l ls]
    unfolding nclause_to_form_def
    sorry
  (*then have \<open>\<exists>l D. C = add_mset l D\<close>
    by (metis size_eq_Suc_imp_eq_union)
  then obtain l D where C_is: \<open>C = add_mset l D\<close>
    by blast
  then have \<open>no_bot D\<close>
    using Suc(3) no_bot_add by blast
  moreover have \<open>size D = x\<close>
    using C_is Suc(2) by auto
  ultimately have \<open>the (form_to_nclause (nclause_to_form D)) = D\<close>
    using Suc(1) by blast*)
  then show ?case
    unfolding nclause_to_form_def
    sorry
qed
(*  case empty
  then show ?case
    unfolding no_bot_def nclause_to_form_def using empty_list_of_mset
      (* Interesting abduction problem: can cvc find empty_list_of_mset if not given? *)
      by (metis fold_simps(1) form_to_nclause.simps(1) option.sel)
next
  case (add x C)
  then show ?case
    unfolding no_bot_def nclause_to_form_def
    sorry 
qed *)




(* aligments for sets of clauses *)

end