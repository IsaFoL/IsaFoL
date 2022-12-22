(* Original Author: Tobias Nipkow
   Modified in order to parametrize over the order
*)

section \<open>Pairing Heap According to Oksaki (Modified)\<close>

theory Ordered_Pairing_Heap_List2
imports
  "HOL-Library.Multiset"
  "HOL-Data_Structures.Priority_Queue_Specs"
begin

chapter \<open>Pairing heaps\<close>


text \<open>
  To make it useful we simply parametrized the formalization by the order. We ruse the formalization
  of Tobias Nipkow, but make it \<^emph>\<open>useful\<close> for refinement by separating node and score. We also need
  to add way to increase the score.\<close>

subsection \<open>Definitions\<close>

text \<open>This version of pairing heaps is a modified version
of the one by Okasaki \cite{Okasaki} that avoids structural invariants.\<close>

datatype ('b, 'a) hp = Hp (node: 'b) (score: 'a) (hps: "('b, 'a) hp list")

type_synonym ('a, 'b) heap = "('a, 'b) hp option"

hide_const (open) insert

fun get_min  :: "('b, 'a) heap \<Rightarrow> 'a" where
"get_min (Some(Hp _ x _)) = x"

text \<open>This is basically the useful version:\<close>
fun get_min2  :: "('b, 'a) heap \<Rightarrow> 'b" where
"get_min2 (Some(Hp n x _)) = n"


locale pairing_heap_assms =
  fixes lt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and
    le :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
begin

fun link :: "('b, 'a) hp \<Rightarrow> ('b, 'a) hp \<Rightarrow> ('b, 'a) hp" where
"link (Hp m x lx) (Hp n y ly) = 
    (if lt x y then Hp m x (Hp n y ly # lx) else Hp n y (Hp m x lx # ly))"

fun merge :: "('b, 'a) heap \<Rightarrow> ('b, 'a) heap \<Rightarrow> ('b, 'a) heap" where
"merge h None = h" |
"merge None h = h" |
"merge (Some h1) (Some h2) = Some(link h1 h2)"

lemma merge_None[simp]: "merge None h = h"
by(cases h)auto

fun insert :: "'b \<Rightarrow> ('a) \<Rightarrow> ('b, 'a) heap \<Rightarrow> ('b, 'a) heap" where
"insert n x None = Some(Hp n x [])" |
"insert n x (Some h) = Some(link (Hp n x []) h)"

fun pass\<^sub>1 :: "('b, 'a) hp list \<Rightarrow> ('b, 'a) hp list" where
  "pass\<^sub>1 [] = []"
| "pass\<^sub>1 [h] = [h]" 
| "pass\<^sub>1 (h1#h2#hs) = link h1 h2 # pass\<^sub>1 hs"

fun pass\<^sub>2 :: "('b, 'a) hp list \<Rightarrow> ('b, 'a) heap" where
  "pass\<^sub>2 [] = None"
| "pass\<^sub>2 (h#hs) = Some(case pass\<^sub>2 hs of None \<Rightarrow> h | Some h' \<Rightarrow> link h h')"

fun merge_pairs :: "('b, 'a) hp list \<Rightarrow> ('b, 'a) heap" where
  "merge_pairs [] = None"
| "merge_pairs [h] = Some h" 
| "merge_pairs (h1 # h2 # hs) =
  Some(let h12 = link h1 h2 in case merge_pairs hs of None \<Rightarrow> h12 | Some h \<Rightarrow> link h12 h)"

fun del_min :: "('b, 'a) heap \<Rightarrow> ('b, 'a) heap" where
  "del_min None = None"
| "del_min (Some(Hp _ x hs)) = pass\<^sub>2 (pass\<^sub>1 hs)"

fun (in -)remove_key_children :: \<open>'b \<Rightarrow> ('b, 'a) hp list \<Rightarrow> ('b, 'a) hp list\<close> where
  \<open>remove_key_children k [] = []\<close> |
  \<open>remove_key_children k ((Hp x n c) # xs) =
  (if k = x then remove_key_children k xs else ((Hp x n (remove_key_children k c)) # remove_key_children k xs))\<close>

fun (in -)remove_key :: \<open>'b \<Rightarrow> ('b, 'a) hp \<Rightarrow> ('b, 'a) heap\<close> where
  \<open>remove_key k (Hp x n c) = (if x = k then None else Some (Hp x n (remove_key_children k c)))\<close>

fun (in -)find_key_children :: \<open>'b \<Rightarrow> ('b, 'a) hp list \<Rightarrow> ('b, 'a) heap\<close> where
  \<open>find_key_children k [] = None\<close> |
  \<open>find_key_children k ((Hp x n c) # xs) =
  (if k = x then Some (Hp x n c) else
  (case find_key_children k c of Some a \<Rightarrow> Some a | _ \<Rightarrow> find_key_children k xs))\<close>


fun (in -)find_key :: \<open>'b \<Rightarrow> ('b, 'a) hp \<Rightarrow> ('b, 'a) heap\<close> where
  \<open>find_key k (Hp x n c) =
  (if k = x then Some (Hp x n c) else find_key_children k c)\<close>

definition decrease_key :: \<open>'b \<Rightarrow> 'a \<Rightarrow> ('b, 'a) hp \<Rightarrow> ('b, 'a) heap\<close> where
  \<open>decrease_key k s hp = (case find_key k hp of None \<Rightarrow> Some hp 
    | (Some (Hp _ _ c)) \<Rightarrow>
      (case remove_key k hp of
          None \<Rightarrow> Some (Hp k s c)
        | Some x \<Rightarrow>  merge_pairs [Hp k s c, x]))\<close>


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma pass12_merge_pairs: "pass\<^sub>2 (pass\<^sub>1 hs) = merge_pairs hs"
by (induction hs rule: merge_pairs.induct) (auto split: option.split)

declare pass12_merge_pairs[code_unfold]


subsubsection \<open>Invariants\<close>

fun (in -) set_hp :: \<open>('b, 'a) hp \<Rightarrow> 'a set\<close> where
  \<open>set_hp (Hp _ x hs) = ({x} \<union> \<Union>(set_hp ` set hs))\<close>


fun php :: "('b, 'a) hp \<Rightarrow> bool" where
"php (Hp _ x hs) = (\<forall>h \<in> set hs. (\<forall>y \<in> set_hp h. le x y) \<and> php h)"

definition invar :: "('b, 'a) heap \<Rightarrow> bool" where
"invar ho = (case ho of None \<Rightarrow> True | Some h \<Rightarrow> php h)"
end

locale pairing_heap = pairing_heap_assms lt le
  for lt :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and
    le :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> +
  assumes le: \<open>\<And>a b. le a b \<longleftrightarrow> a = b \<or> lt a b\<close> and
    trans: \<open>transp le\<close> and
    transt: \<open>transp lt\<close> and
    totalt: \<open>totalp lt\<close>
begin

lemma php_link: "php h1 \<Longrightarrow> php h2 \<Longrightarrow> php (link h1 h2)"
  apply (induction h1 h2 rule: link.induct)
  apply (auto 4 3 simp: le transt dest: transpD[OF transt] totalpD[OF totalt])
  by (metis totalpD totalt transpD transt)

lemma invar_None[simp]: \<open>invar None\<close>
  by (auto simp: invar_def)

lemma invar_merge:
  "\<lbrakk> invar h1; invar h2 \<rbrakk> \<Longrightarrow> invar (merge h1 h2)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_insert: "invar h \<Longrightarrow> invar (insert n x h)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_pass1: "\<forall>h \<in> set hs. php h \<Longrightarrow> \<forall>h \<in> set (pass\<^sub>1 hs). php h"
by(induction hs rule: pass\<^sub>1.induct) (auto simp: php_link)

lemma invar_pass2: "\<forall>h \<in> set hs. php h \<Longrightarrow> invar (pass\<^sub>2 hs)"
by (induction hs)(auto simp: php_link invar_def split: option.splits)

lemma invar_Some: "invar(Some h) = php h"
by(simp add: invar_def)

lemma invar_del_min: "invar h \<Longrightarrow> invar (del_min h)"
by(induction h rule: del_min.induct)
  (auto simp: invar_Some intro!: invar_pass1 invar_pass2)

lemma (in -)in_remove_key_children_in_childrenD: \<open>h \<in> set (remove_key_children k c) \<Longrightarrow> xa \<in> set_hp h \<Longrightarrow> xa \<in> \<Union>(set_hp ` set c)\<close>
  by (induction k c arbitrary: h rule: remove_key_children.induct)
   (auto split: if_splits)

lemma php_remove_key_children: \<open>\<forall>h\<in>set h1. php h  \<Longrightarrow> h \<in> set (remove_key_children k h1) \<Longrightarrow> php h\<close>
  by (induction k h1 arbitrary: h rule: remove_key_children.induct; simp)
   (force simp: decrease_key_def invar_def split: option.splits hp.splits if_splits
    dest: in_remove_key_children_in_childrenD)

lemma php_remove_key: \<open>php h1  \<Longrightarrow> invar (remove_key k h1)\<close>
  by (induction k h1 rule: remove_key.induct)
   (auto simp: decrease_key_def invar_def split: option.splits hp.splits
    dest: in_remove_key_children_in_childrenD
    intro: php_remove_key_children)

lemma invar_find_key_children: \<open>\<forall>h\<in>set c. php h \<Longrightarrow>  invar (find_key_children k c)\<close>
  by (induction k c rule: find_key_children.induct)
   (auto simp: invar_def split: option.splits)

lemma invar_find_key: \<open>php h1 \<Longrightarrow> invar (find_key k h1)\<close>
  by (induction k h1 rule: find_key.induct)
   (use invar_find_key_children[of _ ] in \<open>force simp: invar_def\<close>)

lemma (in -)remove_key_None_iff: \<open>remove_key k h1 = None \<longleftrightarrow> node h1 = k\<close>
  by (cases \<open>(k,h1)\<close> rule: remove_key.cases) auto

lemma php_decrease_key:
  \<open>php h1  \<Longrightarrow> (case (find_key k h1) of None \<Rightarrow> True | Some a \<Rightarrow> le s (score a)) \<Longrightarrow> invar (decrease_key k s h1)\<close>
  using invar_find_key[of h1 k, simplified] remove_key_None_iff[of k h1] php_remove_key[of h1 k]
  apply (auto simp: decrease_key_def invar_def php_remove_key php_link
    dest: transpD[OF transt, of _ \<open>score (the (find_key k h1))\<close>] totalpD[OF totalt]
    split: option.splits hp.splits)
  apply (meson le local.trans transpE)
  apply (rule php_link)
  apply (auto simp: decrease_key_def invar_def php_remove_key php_link
    split: option.splits hp.splits
    dest: transpD[OF transt, of _ \<open>score (the (find_key k h1))\<close>] totalpD[OF totalt])
  apply (meson le local.trans transpE)
  done


subsubsection \<open>Functional Correctness\<close>

fun (in -) mset_hp :: "('b, 'a) hp \<Rightarrow>'a multiset" where
"mset_hp (Hp _ x hs) = {#x#} + sum_mset(mset(map mset_hp hs))"

definition (in -) mset_heap :: "('b, 'a) heap \<Rightarrow>'a multiset" where
"mset_heap ho = (case ho of None \<Rightarrow> {#} | Some h \<Rightarrow> mset_hp h)"

lemma (in -) set_mset_mset_hp: "set_mset (mset_hp h) = set_hp h"
by(induction h) auto

lemma (in -) mset_hp_empty[simp]: "mset_hp hp \<noteq> {#}"
by (cases hp) auto

lemma (in -) mset_heap_Some: "mset_heap(Some hp) = mset_hp hp"
by(simp add: mset_heap_def)

lemma (in -) mset_heap_empty: "mset_heap h = {#} \<longleftrightarrow> h = None"
by (cases h) (auto simp add: mset_heap_def)

lemma (in -)get_min_in:
  "h \<noteq> None \<Longrightarrow> get_min h \<in> set_hp(the h)"
by(induction rule: get_min.induct)(auto)

lemma get_min_min: "\<lbrakk> h \<noteq> None; invar h; x \<in> set_hp(the h) \<rbrakk> \<Longrightarrow> le (get_min h) x"
  by (induction h rule: get_min.induct) (auto simp: invar_def le)


lemma (in pairing_heap_assms) mset_link: "mset_hp (link h1 h2) = mset_hp h1 + mset_hp h2"
by(induction h1 h2 rule: link.induct)(auto simp: add_ac)

lemma (in pairing_heap_assms) mset_merge: "mset_heap (merge h1 h2) = mset_heap h1 + mset_heap h2"
by (induction h1 h2 rule: merge.induct)
   (auto simp add: mset_heap_def mset_link ac_simps)

lemma (in pairing_heap_assms) mset_insert: "mset_heap (insert n a h) = {#a#} + mset_heap h"
by(cases h) (auto simp add: mset_link mset_heap_def insert_def)

lemma (in pairing_heap_assms) mset_merge_pairs: "mset_heap (merge_pairs hs) = sum_mset(image_mset mset_hp (mset hs))"
by(induction hs rule: merge_pairs.induct)
  (auto simp: mset_merge mset_link mset_heap_def Let_def split: option.split)

lemma (in pairing_heap_assms) mset_del_min: "h \<noteq> None \<Longrightarrow>
  mset_heap (del_min h) = mset_heap h - {#get_min h#}"
by(induction h rule: del_min.induct)
  (auto simp: mset_heap_Some pass12_merge_pairs mset_merge_pairs)

text \<open>Some more lemmas to make the heaps easier to use:\<close>
lemma invar_merge_pairs:
  "\<lbrakk>\<forall>h\<in>set h1. invar (Some h)\<rbrakk> \<Longrightarrow> invar (merge_pairs h1)"
  by (metis invar_Some invar_pass1 invar_pass2 pass12_merge_pairs)

end

context pairing_heap_assms
begin

lemma merge_pairs_None_iff [iff]: "merge_pairs hs = None \<longleftrightarrow> hs = []"
  by (cases hs rule: merge_pairs.cases) auto


end



text \<open>Last step: prove all axioms of the priority queue specification with the right sort:\<close>


locale pairing_heap2 =
  fixes ltype :: \<open>'a::linorder itself\<close>
begin

sublocale pairing_heap where
    lt =\<open>(<) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and le = \<open>(\<le>)\<close>
  by unfold_locales
     (auto simp: antisymp_def totalp_on_def)

interpretation pairing: Priority_Queue_Merge
where empty = None and is_empty = "\<lambda>h. h = None"
and merge = merge and insert = \<open>insert default\<close>
and del_min = del_min and get_min = get_min
and invar = invar and mset = mset_heap
proof(standard, goal_cases)
  case 1 show ?case by(simp add: mset_heap_def)
next
  case (2 q) thus ?case by(auto simp add: mset_heap_def split: option.split)
next
  case 3 show ?case by(simp add: mset_insert mset_merge)
next
  case 4 thus ?case by(simp add: mset_del_min mset_heap_empty)
next
  case (5 q) thus ?case using get_min_in[of q]
    by(auto simp add: eq_Min_iff get_min_min mset_heap_empty mset_heap_Some set_mset_mset_hp)
next
  case 6 thus ?case by (simp add: invar_def)
next
  case 7 thus ?case by(rule invar_insert)
next
  case 8 thus ?case by (simp add: invar_del_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: invar_merge)
qed

end

end
