theory Array_Array_List
imports IICF
begin

fun heap_list_all :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all R [] [] = emp\<close>
| \<open>heap_list_all R (x # xs) (y # ys) = R x y * heap_list_all R xs ys\<close>
| \<open>heap_list_all R _ _ = false\<close>

definition arrayO:: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b array \<Rightarrow> assn\<close> where
  \<open>arrayO R' xs axs \<equiv> \<exists>\<^sub>A p. array_assn id_assn p axs * heap_list_all R' xs p\<close>

lemma heap_list_add_same_length:
  \<open>h \<Turnstile> heap_list_all R' xs p \<Longrightarrow> length p = length xs\<close>
  by (induction R' xs p arbitrary: h rule: heap_list_all.induct) (auto elim!: mod_starE)

definition nth_aa :: "'a::heap array_list array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  [code del]: "nth_aa a i j = Heap_Monad.guard (\<lambda>h. i < Array.length h a \<and> j < snd (Array.get h a ! i))
    (\<lambda>h. (Array.get h (fst (Array.get h a ! i)) ! j, h))"

lemma run_nth_aa[run_elims]:
  assumes "run (nth_aa a i j) \<sigma> \<sigma>' r"
          "\<not>is_exn \<sigma>"
  obtains "\<not>is_exn \<sigma>"
    "i < Array.length (the_state \<sigma>) a"
    "r = (Array.get (the_state \<sigma>) (fst ((Array.get (the_state \<sigma>) a)! i))) ! j"
    "j < snd ((Array.get (the_state \<sigma>) a)! i)"
    "\<sigma>' = \<sigma>"
  |
    "\<not> i < Array.length (the_state \<sigma>) a"
    "\<sigma>' = None"
  |
    "\<not>j < snd ((Array.get (the_state \<sigma>) a)! i)"
    "\<sigma>' = None"
  using assms
  apply (cases \<sigma>)
   apply (solves \<open>simp\<close>)
  apply (cases "\<not>i < Array.length (the_state \<sigma>) a")
   apply (solves \<open>simp add: run.simps nth_aa_def execute_guard(1)\<close>)
  apply (cases "\<not>j < snd ((Array.get (the_state \<sigma>) a)! i)")
   apply (solves \<open>simp add: run.simps nth_aa_def execute_guard(1)\<close>)
  by (auto simp add: run.simps nth_aa_def execute_guard)

lemma models_heap_list_all_models_nth:
  \<open>(h, as) \<Turnstile> heap_list_all R a b \<Longrightarrow> i < length a \<Longrightarrow> \<exists>as'. (h, as') \<Turnstile> R (a!i) (b!i)\<close>
  by (induction R a b arbitrary: as i rule: heap_list_all.induct)
    (auto simp: mod_star_conv nth_Cons elim!: less_SucE split: nat.splits)

lemma nth_aa:
  assumes
    i: \<open>i < length xs\<close> and j: \<open>j < length (xs ! i)\<close> and p: \<open>is_pure R'\<close>
  shows
    \<open><arrayO (arl_assn R') xs a> nth_aa a i j <\<lambda>r. arrayO (arl_assn R') xs a * R' (xs ! i ! j) r>\<^sub>t\<close>
proof -
  obtain R where R: \<open>the_pure R' = R\<close> and R': \<open>R' = pure R\<close>
    using p by fastforce
  show ?thesis
    unfolding nth_aa_def
    unfolding hoare_triple_def snga_assn_def array_assn_def is_array_def nth_aa_def
  proof (clarsimp simp only: Let_def Abs_assn_inverse, intro allI impI conjI)
    fix h :: Heap.heap and as :: \<open>nat set\<close> and \<sigma> :: \<open>Heap.heap option\<close> and
      r :: 'b
    assume
      h: \<open>(h, as) \<Turnstile> arrayO (arl_assn R') xs a\<close> and
      run: \<open>run (Heap_Monad.guard (\<lambda>h. i < Array.length h a \<and> j < snd (Array.get h a ! i)) 
          (\<lambda>h. (Array.get h (fst (Array.get h a ! i)) ! j, h))) (Some h) \<sigma> r\<close>
    have [simp]: \<open>i < Array.length h a\<close>
      using h i unfolding arrayO_def array_assn_def is_array_def
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    have xs_i: \<open>\<exists>as'. (h, as') \<Turnstile> (arl_assn R') (xs ! i) ((Array.get h a ! i))\<close>
      using h i unfolding arrayO_def array_assn_def is_array_def
      using models_heap_list_all_models_nth[of _ _ _ _ _ i]
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    then have j_le_get[simp]: \<open>j < snd (Array.get h a ! i)\<close>
      using j unfolding arrayO_def arl_assn_def is_array_list_def
      by (cases \<open>Array.get h a ! i\<close>) (auto simp: run.simps tap_def arrayO_def hr_comp_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          dest: list_rel_pres_length)

    show \<open>\<not> is_exn \<sigma>\<close>
      using run h assms
      by (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    have ex: \<open>execute
        (Heap_Monad.guard
          (\<lambda>h. i < length (Array.get h a) \<and>
               j < snd (Array.get h a ! i))
          (\<lambda>h. (Array.get h (fst (Array.get h a ! i)) ! j, h)))
        h = Some (Array.get h (fst (Array.get h a ! i)) ! j, h)\<close>
      using run h assms
      by (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    show \<open>(the_state \<sigma>, new_addrs h as (the_state \<sigma>)) \<Turnstile>
       arrayO (arl_assn R') xs a  * R' (xs ! i ! j) r * true\<close>
      using run h assms xs_i j_le_get
      apply (cases \<open>Array.get h a ! i\<close>) 
      apply (auto simp: run.simps tap_def arrayO_def R R'
          mod_star_conv arl_assn_def is_array_list_def hr_comp_def ex list_rel_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          dest!: list_all2_nthD[of _ _ _ j] simp del: j_le_get)
      by blast -- \<open>TODO well tune proof\<close>
    show \<open>relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>)\<close>
      using run h assms xs_i
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv arl_assn_def is_array_list_def hr_comp_def ex list_rel_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def relH_def
          in_range.simps)
    show \<open>lim h \<le> lim (the_state \<sigma>)\<close>
      using run h assms xs_i
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv arl_assn_def is_array_list_def hr_comp_def ex list_rel_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def relH_def
          in_range.simps)
  qed
qed

definition nth_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  \<open>nth_ll l i j = l ! i ! j\<close>
  
lemma [sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_ll)) \<in>
     [\<lambda>((l,i),j). i < length l \<and> j < length (l ! i)]\<^sub>a (arrayO (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO (arl_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO (arl_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  show ?thesis
    using assms
    apply sepref_to_hoare
    by (auto simp: nth_ll_def nth_aa IS_PURE_def)
qed
  
definition update_aa where
  \<open>update_aa a i x = Array.upd a i x\<close>

term \<open> Array.upd h a\<close>
term Array.update
term \<open>Array.set a (list_update (Array.get h a) i x) h\<close>
term arl_assn
term arl_append
definition arl_append_heap where
"arl_append_heap \<equiv> \<lambda>a i x.
  let j = Array.nth a i in
  let a' = arl_append j x in
  a'"

definition append_aa :: "'a::heap array_list array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  [code del]: "append_aa a i x = Heap_Monad.guard (\<lambda>h::Heap.heap. i < Array.length h a \<and> j < snd (Array.get h a ! i))
    (\<lambda>h. (arl_append (Array.get h a ! i) x))"

end