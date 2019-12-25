theory List_Allocator
imports
     Refine_Imperative_HOL.IICF
     Weidenbach_Book_Base.WB_List_More
begin



locale list_allocator
begin
  datatype 'a cell =
     Cell (content: \<open>'a\<close>) (cell_next: nat) (cell_ref: nat)

  type_synonym 'a memory = \<open>'a cell list\<close>

text \<open>TODO:
  \<^item> cell ref could be >0 except when used?
  \<^item> \<^term>\<open>list_memory\<close> should be closed under tail. This makes deallocation easier
    since, we then only remove one list from the representation.
\<close>
inductive valid_list_representation :: \<open>'a memory \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool\<close> where
empty_list: \<open>valid_list_representation mem [] 0 free_mem\<close> |
cons_list:
  \<open>valid_list_representation mem' (x # xs) y (free_mem - {y})\<close>
  if \<open>valid_list_representation mem xs x' free_mem\<close> and
    \<open>y \<in> free_mem\<close>
    \<open>mem' = mem[y := Cell x x' 0]\<close>
    \<open>y \<noteq> 0\<close>
    \<open>y < length mem\<close>

inductive_cases valid_list_representationE:
  \<open>valid_list_representation mem xs n free_mem\<close>

lemma valid_list_representation_cong:
  \<open>(\<forall>x. x \<notin> free_mem \<longrightarrow> x < length mem \<longrightarrow> mem ! x = mem' ! x) \<Longrightarrow>
   valid_list_representation mem xs n free_mem \<Longrightarrow>
  length mem' \<ge> length mem \<Longrightarrow>
   valid_list_representation mem' xs n free_mem\<close>
  apply (rotate_tac)
  apply (induction rule: valid_list_representation.induct)
  subgoal
    by (clarsimp simp add: valid_list_representation.intros)
  subgoal premises p for mem xs x' free_mem y mem'a x
    apply (rule valid_list_representation.intros(2)[of mem' xs x' free_mem])
    apply (rule p)
    using p(3-)
    apply clarsimp_all
    apply metis
    apply force
    done
  done

lemma valid_list_representation_tl:
  \<open>valid_list_representation mem (xs) (n) free_mem \<Longrightarrow> xs \<noteq> [] \<Longrightarrow>
    valid_list_representation mem (tl xs) (cell_next (mem ! n)) (insert n free_mem)\<close>
  apply (rule valid_list_representationE, assumption)
  apply (clarsimp_all simp add: insert_absorb)
  apply (rule valid_list_representation_cong)
  defer
  apply assumption
  apply clarsimp_all
  done

lemma valid_list_representation_reduce_free_mem:
  \<open>valid_list_representation mem (xs) (n) free_mem \<Longrightarrow> free_mem' \<subseteq> free_mem \<Longrightarrow>
    valid_list_representation mem xs n free_mem'\<close>
  apply (induction arbitrary: free_mem' rule: valid_list_representation.induct)
  subgoal by (simp add: valid_list_representation.intros)
  subgoal premises p for mem xs x' free_mem y mem' x free_mem'
    using p(1) p(2)[of \<open>insert y free_mem'\<close>] p(3-)
    using valid_list_representation.cons_list[of mem xs x' \<open>insert y free_mem'\<close> y mem' x]
    by force
  done


  definition list_memory :: \<open>'a memory \<Rightarrow> nat set \<Rightarrow> ('a list \<times> nat) multiset \<Rightarrow> bool\<close> where
  \<open>list_memory mem free_mem xxs \<longleftrightarrow>
    (\<forall>(xs,addr) \<in># xxs. valid_list_representation mem xs addr free_mem) \<and>
    (\<forall>(xs,addr) \<in># xxs. count xxs (xs, addr) = cell_ref (mem ! addr))\<close>


lemma valid_list_representation_append_newly_allocated:
  \<open>valid_list_representation mem xs addr free_mem \<Longrightarrow> valid_list_representation (mem @ mem') xs addr free_mem\<close>
  by (induction rule: valid_list_representation.induct)
   (auto simp: valid_list_representation.intros list_update_append1)

definition deallocate_hd  :: \<open>'a memory \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> (nat \<times> nat set)\<close> where
  \<open>deallocate_hd mem n free_mem = (cell_next (mem ! n), insert n free_mem)\<close>

definition deallocate_list :: \<open>'a memory \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> ('a memory \<times> nat set) nres\<close> where
  \<open>deallocate_list mem n free_mem = do {
      n \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(n, free_mem). n < length mem\<^esup>
        (\<lambda>(n, free_mem). cell_next (mem ! n) \<noteq> 0 \<and> cell_ref (mem ! n) = 0)
        (\<lambda>(n, free_mem). RETURN (cell_next (mem ! n), insert n free_mem))
        (n, free_mem);
     RETURN (mem, free_mem)
  }\<close>

lemma
  assumes
    \<open>list_memory mem free_mem (add_mset (xs, n) xxs)\<close> and
    \<open>cell_next (mem ! n) \<noteq> 0\<close> \<open>cell_ref (mem ! n) = Suc 0\<close>
  shows
    \<open>list_memory mem free_mem (add_mset (tl xs, cell_next (mem ! n)) xxs)\<close>
  using assms
  apply (auto simp: list_memory_def)
  oops

end


end