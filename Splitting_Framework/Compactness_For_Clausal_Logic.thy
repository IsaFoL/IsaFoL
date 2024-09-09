(* Title:        Compactness in clausal logic terms
 * Author:       Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Compactness_For_Clausal_Logic
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    FOL_Syntax
    (*Weighted_Path_Order.WPO*)
begin

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  \<open>count [] x = 0\<close>
| \<open>count (x # xs) y = (if x = y then 1 + count xs y else count xs y)\<close>

lemma null_count: \<open>a \<notin> set l \<Longrightarrow> count l a = 0\<close>
  by (induction l) auto

lemma count_plus_one: \<open>a \<in> set l \<Longrightarrow> count (a # l) a = 1 + count l a\<close>
  by (induction l) auto


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

lemma \<open>length l = sum (\<lambda>x. count l x) (set l)\<close>
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

definition list_of_mset :: "'a multiset \<Rightarrow> 'a list" where
  \<open>list_of_mset m = (SOME l. (\<forall>x. count l x = (Multiset.count m x)))\<close>

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

lemma \<open>size M = length (list_of_mset M)\<close>
  using size_multiset_overloaded_eq
  sorry

lemma \<open>size M = length (list_of_mset M)\<close>
proof (induction M)
  case empty
  then show ?case
    using empty_list_of_mset by simp
next
  case (add x M)
  then show ?case sorry
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
  \<open>nclause_to_form C = fold (\<lambda>l \<phi>. \<phi> \<^bold>\<or> (nlit_to_form l)) (list_of_mset C) form.Bot\<close>

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

lemma length_list_of_add_mset: \<open>l = list_of_mset (add_mset x M) \<Longrightarrow> length l = length (list_of_mset M) + 1\<close>
proof (induction M)
  case empty
  then show ?case
    using empty_list_of_mset
     sorry
next
  case (add x M)
  then show ?case sorry
qed

lemma no_bot_add: \<open>no_bot (add_mset l C) \<Longrightarrow> no_bot C\<close>
  unfolding no_bot_def
  by (metis Zero_neq_Suc add_mset.rep_eq)

find_theorems name: mset name: induct

lemma \<open>no_bot C \<Longrightarrow> the (form_to_nclause (nclause_to_form C)) = C\<close>
proof (induction "size C" arbitrary: C)
  case 0
  then show ?case
    unfolding no_bot_def nclause_to_form_def 
    using empty_list_of_mset fold_simps(1) form_to_nclause.simps(1) option.sel
    by (smt (verit, best) size_eq_0_iff_empty)
next
  case (Suc x)
  then have \<open>\<exists>l D. C = add_mset l D\<close>
    by (metis size_eq_Suc_imp_eq_union)
  then obtain l D where \<open>C = add_mset l D\<close>
    by blast
  then have \<open>no_bot D\<close>
    using Suc(3) no_bot_add by blast
  moreover have \<open>size D = x\<close>
    sorry
  ultimately have \<open>the (form_to_nclause (nclause_to_form D)) = D\<close>
    using Suc(1) by blast
  then show ?case
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