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

definition nth_aa where
  \<open>nth_aa xs i j = do {
      x \<leftarrow> Array.nth xs i;
      y \<leftarrow> arl_get x j;
      return y}\<close>

lemma models_heap_list_all_models_nth:
  \<open>(h, as) \<Turnstile> heap_list_all R a b \<Longrightarrow> i < length a \<Longrightarrow> \<exists>as'. (h, as') \<Turnstile> R (a!i) (b!i)\<close>
  by (induction R a b arbitrary: as i rule: heap_list_all.induct)
    (auto simp: mod_star_conv nth_Cons elim!: less_SucE split: nat.splits)

definition nth_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  \<open>nth_ll l i j = l ! i ! j\<close>

lemma nth_aa_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_ll)) \<in>
     [\<lambda>((l,i),j). i < length l \<and> j < length (l ! i)]\<^sub>a (arrayO (arl_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO (arl_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO (arl_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  show ?thesis
  proof (sepref_to_hoare, clarsimp simp only: hoare_triple_def Let_def, intro allI impI conjI)
    fix a :: \<open>'a list list\<close> and ai :: \<open>('b array_list) array\<close> and
      h :: Heap.heap and as:: \<open>nat set\<close> and \<sigma> :: \<open>Heap.heap option\<close> and r :: 'b and
      i i' j j' :: nat
    assume
      i: \<open>i < length a\<close> and
      j: \<open>j < length (a ! i)\<close> and
      h: \<open> (h, as) \<Turnstile>
       \<up> ((j', j) \<in> nat_rel) * \<up> ((i', i) \<in> nat_rel) *
       arrayO (arl_assn R) a ai\<close> and
      run: \<open>run (nth_aa ai i' j') (Some h) \<sigma> r\<close>

    have i_le: \<open>i < Array.length h ai\<close>
      using h i unfolding arrayO_def array_assn_def is_array_def
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    have xs_i: \<open>\<exists>as'. (h, as') \<Turnstile> (arl_assn R) (a ! i) (Array.get h ai ! i)\<close>
      using h i unfolding arrayO_def array_assn_def is_array_def
      using models_heap_list_all_models_nth[of _ _ _ _ _ i]
      by (auto simp: run.simps tap_def arrayO_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    then have j_le_get: \<open>j < Array.length h (fst (Array.get h ai ! i))\<close>
      using j unfolding arrayO_def arl_assn_def is_array_list_def
      by (cases \<open>Array.get h ai ! i\<close>) (auto simp: run.simps tap_def arrayO_def hr_comp_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          dest: list_rel_pres_length)
    have j_le_get_snd: \<open>j < snd (Array.get h ai ! i)\<close>
      using j xs_i unfolding arrayO_def arl_assn_def is_array_list_def
      by (cases \<open>Array.get h ai ! i\<close>) (auto simp: run.simps tap_def arrayO_def hr_comp_def
          mod_star_conv array_assn_def is_array_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          dest: list_rel_pres_length)
    have ex_arl: \<open>execute (arl_get (Array.get h ai ! i) j) h =
        Some (Array.get h (fst (Array.get h ai ! i)) ! j, h)\<close>
      using run h assms i_le i j j_le_get
      by (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def nth_aa_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length snga_assn_def
          execute_bind_case arl_get_def split_beta
          split: option.splits)
    have ex: \<open>execute (nth_aa ai i j) h = Some (Array.get h (fst (Array.get h ai ! i)) ! j, h)\<close>
      using run h assms i_le
      by (auto simp: run.simps tap_def arrayO_def execute_simps ex_arl
          mod_star_conv array_assn_def is_array_def nth_aa_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          execute_bind_case split: option.splits)
    show \<open>\<not> is_exn \<sigma>\<close>
      using run h assms
      by (auto simp: run.simps tap_def arrayO_def execute_simps ex
          mod_star_conv array_assn_def is_array_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)
    show \<open>(the_state \<sigma>, new_addrs h as (the_state \<sigma>)) \<Turnstile>
       \<up> ((j', j) \<in> nat_rel) * \<up> ((i', i) \<in> nat_rel) * arrayO (arl_assn R) a ai *
            (\<exists>\<^sub>Ax. R x r * \<up> (RETURN x \<le> RETURN (nth_ll a i j))) * true\<close>
      using run h assms xs_i j_le_get i_le j_le_get_snd
      apply (cases \<open>Array.get h ai ! i\<close>)
      apply (auto simp: run.simps tap_def arrayO_def R R' nth_ll_def
          mod_star_conv arl_assn_def is_array_list_def hr_comp_def ex list_rel_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          dest!: list_all2_nthD[of _ _ _ j])
        by blast
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

definition update_aa where
  \<open>update_aa a i x = Array.upd a i x\<close>

term \<open> Array.upd h a\<close>
term Array.update
term \<open>Array.set a (list_update (Array.get h a) i x) h\<close>
term arl_assn
term arl_append

definition append_el_aa where
"append_el_aa \<equiv> \<lambda>a i x. do {
  j \<leftarrow> Array.nth a i;
  a' \<leftarrow> arl_append j x;
  Array.upd i a' a
  }"



definition append_aa :: "'a::heap array_list array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  [code del]: "append_aa a i x = Heap_Monad.guard (\<lambda>h::Heap.heap. i < Array.length h a \<and> j < snd (Array.get h a ! i))
    (\<lambda>h. (arl_append (Array.get h a ! i) x))"

end