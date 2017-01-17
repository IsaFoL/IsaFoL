theory Array_Array_List
imports IICF
begin

fun heap_list_all :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all R [] [] = emp\<close>
| \<open>heap_list_all R (x # xs) (y # ys) = R x y * heap_list_all R xs ys\<close>
| \<open>heap_list_all R _ _ = false\<close>

definition heap_list_all_nth:: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow>  'a list \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>heap_list_all_nth R is xs ys = foldr (op *) (map (\<lambda>i. R (xs ! i) (ys ! i)) is) emp\<close>

lemma heap_list_all_nth_emty[simp]: \<open>heap_list_all_nth R [] [] [] = emp\<close>
  unfolding heap_list_all_nth_def by auto

lemma heap_list_all_heap_list_all_nth:
  \<open>length xs = length ys \<Longrightarrow> heap_list_all R xs ys = heap_list_all_nth R [0..< length xs] xs ys\<close>
proof (induction R xs ys rule: heap_list_all.induct)
  case (2 R x xs y ys) note IH = this
  then have IH: \<open>heap_list_all R xs ys = heap_list_all_nth R [0..<length xs] xs ys\<close>
    by auto
  have upt: \<open>[0..<length (x # xs)] = 0 # [1..<Suc (length xs)]\<close>
    by (simp add: upt_rec)
  have upt_map_Suc: \<open>[1..<Suc (length xs)] = map Suc [0..<length xs]\<close>
    by (induction xs) auto
  have map: \<open>(map (\<lambda>i. R ((x # xs) ! i) ((y # ys) ! i)) [1..<Suc (length xs)]) =
    (map (\<lambda>i. R (xs ! i) (ys ! i)) [0..< (length xs)])\<close>
    unfolding upt_map_Suc map_map by auto
  have 1: \<open>heap_list_all_nth R [0..<length (x # xs)] (x # xs) (y # ys) =
    R x y * heap_list_all_nth R [0..<length xs] xs ys\<close>
    unfolding heap_list_all_nth_def upt
    by (simp only: list.map foldr.simps map) auto
  show ?case
    using IH unfolding 1 by auto
qed auto

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
           arl_get_def split_beta
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

definition append_el_aa :: "('a::{default,heap} array_list) array \<Rightarrow>
  nat \<Rightarrow> 'a \<Rightarrow> ('a array_list) array Heap"where
"append_el_aa \<equiv> \<lambda>a i x. do {
  j \<leftarrow> Array.nth a i;
  a' \<leftarrow> arl_append j x;
  Array.upd i a' a
  }"
definition append_ll :: "'a list list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  \<open>append_ll xs i x = list_update xs i (xs ! i @ [x])\<close>
(* src si dst di (Suc l) *)
lemma
  \<open>i < Array.length h aa \<Longrightarrow> execute (blit aa i dst i l) h \<noteq> None\<close>
  apply (induction l)
   apply (auto simp: execute_simps execute_bind_case Array.nth_def
      Array.upd_def
      split: option.splits)
    oops
lemma nth_aa_hnr[sepref_fr_rules]:
  fixes R ::  \<open>'a \<Rightarrow> 'b :: {heap, default}\<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 append_el_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> append_ll)) \<in>
     [\<lambda>((l,i),x). i < length l]\<^sub>a (arrayO (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO (arl_assn R))\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(\<exists>\<^sub>Ax. arrayO (arl_assn R) a ai * R x r * true * \<up> (x = a ! ba ! b)) =
     (arrayO (arl_assn R) a ai * R (a ! ba ! b) r * true)\<close> for a ai ba b r
    by (auto simp: ex_assn_def)
  have ?thesis
    apply sepref_to_hoare
    apply (auto simp: append_el_aa_def (* arrayO_def *) array_assn_def is_array_def)
    apply (rule bind_rule)
      -- \<open>some work on ArrayO missing\<close>
      sorry
    show ?thesis
  proof (sepref_to_hoare, clarsimp simp only: hoare_triple_def Let_def, intro allI impI conjI)
    fix a :: \<open>'a list list\<close> and ai :: \<open>('b array_list) array\<close> and
      h :: Heap.heap and as:: \<open>nat set\<close> and \<sigma> :: \<open>Heap.heap option\<close> and r :: \<open>('b array_list) array\<close> and
      i i' :: nat and x' :: 'a and x :: 'b
    assume
      i: \<open>i < length a\<close> and
      h: \<open>(h, as) \<Turnstile> R x' x * \<up> ((i', i) \<in> nat_rel) * arrayO (arl_assn R) a ai\<close> and
      run: \<open>run (append_el_aa ai i' x) (Some h) \<sigma> r\<close>
    have i'_i[simp]: \<open>i' = i\<close>
      using h by auto
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
    have ex_arl: \<open>execute (arl_append (Array.get h ai ! i) x) h \<noteq> None\<close>
      using run h assms i_le i xs_i
      using arl_append_rule[of _ \<open>Array.get h ai ! i\<close> x, unfolded hoare_triple_def]
      unfolding arl_assn_def hr_comp_def
(*       apply (cases \<open>Array.get h ai ! i\<close>)
      apply (auto simp: run.simps tap_def arrayO_def execute_simps arl_append_def
          mod_star_conv array_assn_def is_array_def append_el_aa_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          array_grow_def Let_def split_beta
          execute_bind_case split: option.splits if_splits) *)





    have ex: \<open>execute (append_el_aa ai i x) h = Some x'''\<close>
      using run h assms i_le
      apply (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def append_el_aa_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
          execute_bind_case split: option.splits)
        oops
    show \<open>\<not> is_exn \<sigma>\<close>
      using run h assms
      by (auto simp: run.simps tap_def arrayO_def execute_simps
          mod_star_conv array_assn_def is_array_def Array.nth_def
          Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def)



definition append_aa :: "'a::heap array_list array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  [code del]: "append_aa a i x = Heap_Monad.guard (\<lambda>h::Heap.heap. i < Array.length h a \<and> j < snd (Array.get h a ! i))
    (\<lambda>h. (arl_append (Array.get h a ! i) x))"

end