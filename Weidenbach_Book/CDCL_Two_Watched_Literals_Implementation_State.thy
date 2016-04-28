theory CDCL_Two_Watched_Literals_Implementation_State
imports Partial_Annotated_Clausal_Logic "~~/src/HOL/Library/RBT"
begin

section \<open>RBT\<close>

subsection \<open>More RBT\<close>
lemma "RBT.keys t = [] \<Longrightarrow> t = RBT.empty"
  using non_empty_keys by auto

lemma entries_empty[simp]: "RBT.entries RBT.empty = []"
  unfolding RBT.empty_def RBT.entries_def by (metis RBT.empty_def RBT.entries_def entries.rep_eq 
  entries.simps(1) impl_of_empty)

lemma keys_empty[simp]: "RBT.keys RBT.empty = []" (is "?rbt = []")
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain k where "k \<in> set ?rbt" 
     by (cases ?rbt) auto
  then have "(k, the (RBT.lookup RBT.empty k)) \<in> set (RBT.entries RBT.empty)"
    by (simp add: RBT.keys_entries)
  then show False
    unfolding entries_empty by simp
qed

lemma keys_insert: "set (RBT.keys (RBT.insert a L t)) = insert a (set (RBT.keys t))"
  by (auto simp: keys_entries lookup_in_tree[symmetric] split: if_splits)

lemma keys_delete: "set (RBT.keys (RBT.delete d t)) = Set.remove d (set (RBT.keys t))"
  by (auto simp: keys_entries lookup_in_tree[symmetric] split: if_splits)

lemma delete_empty[simp]: "RBT.delete d RBT.empty = RBT.empty"
  using lookup_empty_empty by fastforce

lemma keys_nil[simp]: "RBT.keys t = [] \<longleftrightarrow> t = RBT.empty"
  apply (rule iffI)
    defer apply auto[]
  using non_empty_keys by blast


subsection \<open>Array-like type based on RBT\<close>

definition wf_rbt_array :: "(nat, 'a) RBT.rbt \<Rightarrow> bool" where
"wf_rbt_array t \<longleftrightarrow> set (RBT.keys t) = {1..length (RBT.keys t)}"

fun rbt_array_append :: "'a \<Rightarrow> (nat, 'a) RBT.rbt \<Rightarrow> (nat, 'a) RBT.rbt"  where
"rbt_array_append L t = RBT.insert (length (RBT.keys t)+1) L t"

fun rbt_array_rem_last :: "(nat, 'a) RBT.rbt \<Rightarrow> (nat, 'a) RBT.rbt"  where
"rbt_array_rem_last t = RBT.delete (length (RBT.keys t)) t"

lemma wf_rbt_array_rbt_array_append:
  assumes wf: "wf_rbt_array t"
  shows "wf_rbt_array (rbt_array_append L t)"
proof -
  have H: "set (RBT.keys t) = {1..length (RBT.keys t)}"
    using wf by (auto simp: wf_rbt_array_def)
  have "card (set (RBT.keys t))+1 \<notin> set (RBT.keys t)"
    by (subst H, subst (1) H) auto
  then have "length (RBT.keys (RBT.insert (length (RBT.keys t) + 1) L t)) = Suc (length (RBT.keys t))"
    by (auto simp: wf_rbt_array_def distinct_card[symmetric] keys_insert)
  moreover 
    have "insert (Suc (length (RBT.keys t))) (set (RBT.keys t)) = {Suc 0..Suc (length (RBT.keys t))}"
      by (subst H)  auto
  ultimately show ?thesis
    unfolding wf_rbt_array_def
    by (simp add: keys_insert wf_rbt_array_def)
qed

lemma wf_trail_rbt_array_rem_last:
  assumes wf: "wf_rbt_array t"
  shows "wf_rbt_array (rbt_array_rem_last t)"
proof -
  have H: "set (RBT.keys t) = {1..length (RBT.keys t)}"
    using wf by (auto simp: wf_rbt_array_def)
  show ?thesis
    proof (cases "card (set (RBT.keys t)) \<ge> 1")
      case True
      then have "card (set (RBT.keys t)) \<in> set (RBT.keys t)"
        by (subst H, subst (1) H) (auto simp: distinct_card[symmetric])
      then have "length (RBT.keys (RBT.delete (length (RBT.keys t)) t)) = length (RBT.keys t) - 1"
        by (auto simp: wf_rbt_array_def distinct_card[symmetric] keys_delete Set.remove_def)
      moreover 
        have "Set.remove (length (RBT.keys t)) (set (RBT.keys t)) =
          {Suc 0..length (RBT.keys t) - Suc 0}"
          by (subst H) auto
      ultimately show ?thesis
       unfolding wf_rbt_array_def by (simp add: keys_delete)
    next
      case False
      then have "t = RBT.empty"
        by (metis One_nat_def RBT.distinct_keys Suc_leI distinct_card length_greater_0_conv 
          non_empty_keys)
      then show ?thesis
        unfolding wf_rbt_array_def by (auto simp: keys_delete) 
    qed
qed

definition rel_rbt :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_rbt R = (\<lambda>A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y))"

typedef 't rbt_array = "{t::(nat, 't) RBT.rbt. wf_rbt_array t}"
proof 
  show "RBT.empty \<in> ?rbt_array" by (auto simp: wf_rbt_array_def)
qed

setup_lifting type_definition_rbt_array

lift_definition array_rem_last :: "'t rbt_array \<Rightarrow> 't rbt_array" is "rbt_array_rem_last"
by (rule wf_trail_rbt_array_rem_last)

lift_definition array_append :: "'t \<Rightarrow> 't rbt_array \<Rightarrow> 't rbt_array" is "rbt_array_append" 
by (rule wf_rbt_array_rbt_array_append)

lift_definition array_lookup :: "'t rbt_array \<Rightarrow> nat \<Rightarrow> 't option" is "RBT.lookup" .


section \<open>Definition of the State\<close>

subsection \<open>Trail\<close>


fun get_part_trail :: "(nat, 'a) RBT.rbt \<Rightarrow> nat \<Rightarrow> 'a list"  where
"get_part_trail C 0 = []" |
"get_part_trail C (Suc n) = the (RBT.lookup C (Suc n)) # get_part_trail C n"

abbreviation get_trail :: "(nat, 'a) RBT.rbt \<Rightarrow> 'a list" where
"get_trail C \<equiv> get_part_trail C (length (RBT.keys C))"

lemma get_part_trail_cong:
  assumes "m = m'" and "\<And>n. n \<le> m \<Longrightarrow> RBT.lookup C n = RBT.lookup D n"
  shows "get_part_trail C m = get_part_trail D m'"
  using assms(2) unfolding assms(1)
  apply (induction m')
    apply simp
  apply (simp add: assms)
  done

lemma "tl (get_part_trail t (length (RBT.keys t))) =  get_part_trail t (length (RBT.keys t)-1)"
  by (cases "(t, length (RBT.keys t))" rule: get_part_trail.cases) auto

lemma tl_get_part_trail:
  assumes wf: "wf_rbt_array t"
  shows 
    "tl (get_part_trail t (length (RBT.keys t))) = 
      get_part_trail (RBT.delete (length (RBT.keys t)) t) (length (RBT.keys t) - Suc 0)"
proof -
  have "wf_rbt_array (rbt_array_rem_last t)"
    using local.wf wf_trail_rbt_array_rem_last by blast
  then have H: "set (RBT.keys t) = {1..length (RBT.keys t)}"
    using wf by (auto simp: wf_rbt_array_def)
  show ?thesis
    proof (cases "card (set (RBT.keys t)) \<ge> 1")
      case True
      then have "card (set (RBT.keys t)) \<in> set (RBT.keys t)"
        by (subst H, subst (1) H) (auto simp: distinct_card[symmetric])
      then have l: "length (RBT.keys t) = Suc (length (RBT.keys (RBT.delete (length (RBT.keys t)) t)))"
        using True by (auto simp: wf_rbt_array_def distinct_card[symmetric] keys_delete Set.remove_def)

      have r: "Set.remove (length (RBT.keys t)) (set (RBT.keys t)) =
        {Suc 0..length (RBT.keys t) - Suc 0}"
        by (subst H) auto
      have T: "get_part_trail t (card (Set.remove (card (set (RBT.keys t))) (set (RBT.keys t)))) =
        get_part_trail (RBT.delete (card (set (RBT.keys t))) t) (card (set (RBT.keys t)) - Suc 0)"
        apply (rule get_part_trail_cong)
          apply (simp add: r distinct_card)
        by (metis RBT.distinct_keys distinct_card eq_iff fun_upd_apply keys_delete l le_imp_less_Suc
          lookup_delete not_less)    
      show ?thesis
        unfolding wf_rbt_array_def apply (subst (1) l) 
        by (auto simp add:distinct_card[symmetric] T keys_delete)
    next
      case False
      then have "t = RBT.empty"
        by (metis One_nat_def RBT.distinct_keys Suc_leI distinct_card length_greater_0_conv 
          non_empty_keys)
      then show ?thesis
        unfolding wf_rbt_array_def by (auto simp: keys_delete) 
    qed    
qed

lemma get_trail_rbt_array_rem_last_tl:
  assumes wf: "wf_rbt_array t"
  shows "get_trail (rbt_array_rem_last t) = tl (get_trail t)"
proof -
  have "wf_rbt_array (rbt_array_rem_last t)"
    using local.wf wf_trail_rbt_array_rem_last by blast
  then have H: "set (RBT.keys t) = {1..length (RBT.keys t)}"
    using wf by (auto simp: wf_rbt_array_def)
  show ?thesis
    proof (cases "card (set (RBT.keys t)) \<ge> 1")
      case True
      then have "card (set (RBT.keys t)) \<in> set (RBT.keys t)"
        by (subst H, subst (1) H) (auto simp: distinct_card[symmetric])
      then have [simp]: "length (RBT.keys (RBT.delete (length (RBT.keys t)) t)) =
        length (RBT.keys t) - 1"
        by (auto simp: wf_rbt_array_def distinct_card[symmetric] keys_delete Set.remove_def)
      moreover 
        have "Set.remove (length (RBT.keys t)) (set (RBT.keys t)) = 
          {Suc 0..length (RBT.keys t) - Suc 0}"
          by (subst H) auto
      ultimately show ?thesis
       unfolding wf_rbt_array_def by (simp add: keys_delete tl_get_part_trail assms)
    next
      case False
      then have "t = RBT.empty"
        by (metis One_nat_def RBT.distinct_keys Suc_leI distinct_card length_greater_0_conv 
          non_empty_keys)
      then show ?thesis
        unfolding wf_rbt_array_def by (auto simp: keys_delete) 
    qed    
qed

lemma get_trail_rbt_array_appendail_tr_cons:
  assumes wf: "wf_rbt_array t"
  shows "get_trail (rbt_array_append L t) = L # get_trail t"
proof -
  have H: "set (RBT.keys t) = {1..length (RBT.keys t)}"
    using wf by (auto simp: wf_rbt_array_def)
  have "card (set (RBT.keys t))+1 \<notin> set (RBT.keys t)"
    by (subst H, subst (1) H) auto
  then have "length (RBT.keys (RBT.insert (length (RBT.keys t) + 1) L t)) = Suc (length (RBT.keys t))"
    by (auto simp: wf_rbt_array_def distinct_card[symmetric] keys_insert)
  moreover 
    have i: "insert (Suc (length (RBT.keys t))) (set (RBT.keys t)) = {Suc 0..Suc (length (RBT.keys t))}"
      by (subst H)  auto
  moreover
    have "get_part_trail (RBT.insert (Suc (length (RBT.keys t))) L t) (length (RBT.keys t)) =
      get_part_trail t (length (RBT.keys t))"
        apply (rule get_part_trail_cong)
          apply (simp add: i distinct_card)
        by simp
  ultimately show ?thesis
    unfolding wf_rbt_array_def
    by (simp add: keys_insert wf_rbt_array_def)
qed


end