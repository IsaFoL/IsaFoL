theory Array_List_Array
imports Array_Array_List "~~/src/HOL/Library/Code_Target_Numeral"
begin

subsection \<open>Array of Array Lists\<close>

type_synonym 'a array0_raa = \<open>'a array array_list\<close>
type_synonym 'a list_rll = \<open>'a list list\<close>

definition arrayO_raa:: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b array_list \<Rightarrow> assn\<close> where
  \<open>arrayO_raa R' xs axs \<equiv> \<exists>\<^sub>A p. arl_assn id_assn p axs * heap_list_all R' xs p\<close>

definition arrayO_raa_except:: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'b array_list \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>arrayO_raa_except R' is xs axs f \<equiv>
     \<exists>\<^sub>A p. arl_assn id_assn p axs * heap_list_all_nth R' (fold remove1 is [0..<length xs]) xs p *
    \<up> (length xs = length p) * f p\<close>

lemma arrayO_raa_except_array0: \<open>arrayO_raa_except R [] xs asx (\<lambda>_. emp) = arrayO_raa R xs asx\<close>
proof -
  have \<open>(h \<Turnstile> arl_assn id_assn p asx * heap_list_all_nth R [0..<length xs] xs p \<and> length xs = length p) =
    (h \<Turnstile> arl_assn id_assn p asx * heap_list_all R xs p)\<close> (is \<open>?a = ?b\<close>) for h p
  proof (rule iffI)
    assume ?a
    then show ?b
      by (auto simp: heap_list_all_heap_list_all_nth)
  next
    assume ?b
    then have \<open>length xs = length p\<close>
      by (auto simp: heap_list_add_same_length mod_star_conv)
    then show ?a
      using \<open>?b\<close>
        by (auto simp: heap_list_all_heap_list_all_nth)
    qed
  then show ?thesis
    unfolding arrayO_raa_except_def arrayO_raa_def by (auto simp: ex_assn_def)
qed

lemma arrayO_raa_except_array0_index:
  \<open>i < length xs \<Longrightarrow> arrayO_raa_except R [i] xs asx (\<lambda>p. R (xs ! i) (p ! i)) = arrayO_raa R xs asx\<close>
  unfolding arrayO_raa_except_array0[symmetric] arrayO_raa_except_def
  using heap_list_all_nth_remove1[of i \<open>[0..<length xs]\<close> R xs] by (auto simp: star_aci(2,3))

lemma arrayO_raa_nth_rule[sep_heap_rules]:
  assumes i: \<open>i < length a\<close>
  shows \<open> <arrayO_raa (array_assn R) a ai> arl_get ai i <\<lambda>r. arrayO_raa_except (array_assn R) [i] a ai
   (\<lambda>r'. array_assn R (a ! i) r * \<up>(r = r' ! i))>\<close>
proof -
  obtain t n where ai: \<open>ai = (t, n)\<close> by (cases ai)
  have i_le: \<open>i < Array.length h t\<close> if \<open>(h, as) \<Turnstile> arrayO_raa (array_assn R) a ai\<close> for h as
    using ai that i unfolding arrayO_raa_def array_assn_def is_array_def arl_assn_def is_array_list_def
    by (auto simp: run.simps tap_def arrayO_raa_def
        mod_star_conv array_assn_def is_array_def
        Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
        dest: heap_list_add_same_length)
  show ?thesis
    unfolding hoare_triple_def Let_def
  proof (clarify, intro allI impI conjI)
    fix h as \<sigma> r
    assume
      a: \<open>(h, as) \<Turnstile> arrayO_raa (array_assn R) a ai\<close> and
      r: \<open>run (arl_get ai i) (Some h) \<sigma> r\<close>
    have [simp]: \<open>length a = n\<close>
      using a ai
      by (auto simp: arrayO_raa_def mod_star_conv arl_assn_def is_array_list_def
          dest: heap_list_add_same_length)
    obtain p where
      p: \<open>(h, as) \<Turnstile> arl_assn id_assn p (t, n) *
            heap_list_all_nth (array_assn R) (remove1 i [0..<length p]) a p *
            array_assn R (a ! i) (p ! i)\<close>
      using assms a ai
      by (auto simp: hoare_triple_def Let_def  execute_simps relH_def in_range.simps
          arrayO_raa_except_array0_index[of i, symmetric] arl_get_def
          arrayO_raa_except_array0_index arrayO_raa_except_def
          elim!: run_elims
          intro!: norm_pre_ex_rule)
    then have \<open>(Array.get h t ! i) = p ! i\<close>
      using ai i i_le unfolding arrayO_raa_except_array0_index
      apply (auto simp: mod_star_conv array_assn_def is_array_def (* Array.get_def *) snga_assn_def
          Abs_assn_inverse arl_assn_def (* is_array_list_def *))
      unfolding is_array_list_def is_array_def hr_comp_def list_rel_def
      apply (auto simp: mod_star_conv array_assn_def is_array_def (* Array.get_def *) snga_assn_def
          Abs_assn_inverse arl_assn_def (* is_array_list_def *) from_nat_def
          intro!: nth_take[symmetric])
      done
    moreover have \<open>length p = n\<close>
      using p ai
      by (auto simp: arl_assn_def is_array_list_def)

    ultimately show \<open>(the_state \<sigma>, new_addrs h as (the_state \<sigma>)) \<Turnstile>
        arrayO_raa_except (array_assn R) [i] a ai (\<lambda>r'. array_assn R (a ! i) r * \<up> (r = r' ! i))\<close>
      using assms (* A *) ai i_le r p
      by (fastforce simp: hoare_triple_def Let_def  execute_simps relH_def in_range.simps
          arrayO_raa_except_array0_index[of i, symmetric] arl_get_def
          arrayO_raa_except_array0_index arrayO_raa_except_def
          elim!: run_elims
          intro!: norm_pre_ex_rule)
  qed ((solves \<open>use assms ai i_le in \<open>auto simp: hoare_triple_def Let_def execute_simps relH_def
    in_range.simps arrayO_raa_except_array0_index[of i, symmetric] arl_get_def
        elim!: run_elims
        intro!: norm_pre_ex_rule\<close>\<close>)+)[3]
qed

definition length_ra :: \<open>'a::heap array0_raa \<Rightarrow> nat Heap\<close> where
  \<open>length_ra xs = arl_length xs\<close>

lemma length_ra_rule[sep_heap_rules]:
   \<open><arrayO_raa R x xi> length_ra xi <\<lambda>r. arrayO_raa R x xi * \<up>(r = length x)>\<^sub>t\<close>
  by (sep_auto simp: arrayO_raa_def length_ra_def mod_star_conv arl_assn_def
      dest: heap_list_add_same_length)

lemma length_ra_hnr[sepref_fr_rules]: \<open>(length_ra, RETURN o length) \<in> (arrayO_raa R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

definition length_rll :: \<open>'a list_rll \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>length_rll l i = length (l!i)\<close>

lemma le_length_rll_nemptyD: \<open>b < length_rll a ba \<Longrightarrow> a ! ba \<noteq> []\<close>
  by (auto simp: length_rll_def)

definition length_raa :: \<open>'a::heap array0_raa \<Rightarrow> nat \<Rightarrow> nat Heap\<close> where
  \<open>length_raa xs i = do {
     x \<leftarrow> arl_get xs i;
    Array.len x}\<close>

lemma length_raa_rule[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow> <arrayO_raa (array_assn R) xs a> length_raa a b
   <\<lambda>r. arrayO_raa (array_assn R) xs a * \<up> (r = length_rll xs b)>\<^sub>t\<close>
  unfolding length_raa_def
  apply (cases a)
  apply sep_auto
  apply (sep_auto simp: arrayO_raa_except_def arl_length_def array_assn_def (*  *)
      eq_commute[of \<open>(_, _)\<close>] is_array_def hr_comp_def length_rll_def
      dest: list_all2_lengthD)
   apply (sep_auto simp: arrayO_raa_except_def arl_length_def arl_assn_def(*  *)
      eq_commute[of \<open>(_, _)\<close>] is_array_list_def hr_comp_def length_rll_def list_rel_def
      dest: list_all2_lengthD)[]
  unfolding arrayO_raa_def[symmetric] arl_assn_def[symmetric]
  apply (subst arrayO_raa_except_array0_index[symmetric, of b])
   apply simp
  unfolding arrayO_raa_except_def arl_assn_def hr_comp_def is_array_def
  apply sep_auto
  done

lemma length_raa_hnr[sepref_fr_rules]: \<open>(uncurry length_raa, uncurry (RETURN \<circ>\<circ> length_rll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_raa (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare sep_auto

definition nth_raa :: \<open>'a::heap array0_raa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Heap\<close> where
  \<open>nth_raa xs i j = do {
      x \<leftarrow> arl_get xs i;
      y \<leftarrow> Array.nth x j;
      return y}\<close>

definition nth_rll :: "'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  \<open>nth_rll l i j = l ! i ! j\<close>

lemma nth_raa_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arrayO_raa (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
  apply sepref_to_hoare
  apply (subst (2) arrayO_raa_except_array0_index[symmetric])
    apply (solves \<open>auto\<close>)[]
  apply (sep_auto simp: nth_raa_def nth_rll_def length_rll_def)
    apply (sep_auto simp: arrayO_raa_except_def arrayO_raa_def arl_assn_def hr_comp_def list_rel_def
        list_all2_lengthD
      star_aci(3) R R' pure_def H)
    sorry
qed

definition update_raa :: "('a::{heap,default}) array0_raa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array0_raa Heap" where
  \<open>update_raa a i j y = do {
      x \<leftarrow> arl_get a i;
      a' \<leftarrow> Array.upd j y x;
      arl_set a i a'
    }\<close> -- \<open>is the Array.upd really needed?\<close>

definition update_rll :: "'a list_rll \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list"  where
  \<open>update_rll xs i j y = xs[i:= (xs ! i)[j := y]]\<close>

declare nth_rule[sep_heap_rules del]
declare arrayO_raa_nth_rule[sep_heap_rules]

text \<open>TODO: is it possible to be more precise and not drop the \<^term>\<open>\<up> ((aa, bc) = r' ! bb)\<close>\<close>
lemma arrayO_raa_except_arl_set[sep_heap_rules]:
  fixes R :: \<open>'a \<Rightarrow> 'b :: {heap} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and
    \<open>ba < length_rll a bb\<close>
  shows \<open>
       <arrayO_raa_except (array_assn R) [bb] a ai (\<lambda>r'. array_assn R (a ! bb) aa *
         \<up> (aa = r' ! bb)) * R b bi>
       Array.upd ba bi aa
      <\<lambda>aa. arrayO_raa_except (array_assn R) [bb] a ai
        (\<lambda>r'. array_assn R ((a ! bb)[ba := b]) aa) * R b bi * true>\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    using assms
    apply (cases ai)
    apply (sep_auto simp: arrayO_raa_except_def arl_assn_def hr_comp_def list_rel_imp_same_length
        list_rel_update length_rll_def (* is_array_list_def *))
    sorry
qed

lemma update_raa_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_rll a bb\<close>
  shows \<open><R b bi * arrayO_raa (array_assn R) a ai> update_raa ai bb ba bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arrayO_raa (array_assn R) x r * \<up> (x = update_rll a bb ba b))>\<^sub>t\<close>
    using assms
  apply (sep_auto simp add: update_raa_def update_rll_def p)
  apply (sep_auto simp add: update_raa_def arrayO_raa_except_def array_assn_def is_array_def hr_comp_def)
  apply (subst_tac i=bb in arrayO_raa_except_array0_index[symmetric])
   apply (solves \<open>simp\<close>)
  apply (subst arrayO_raa_except_def)
  apply (auto simp add: update_raa_def arrayO_raa_except_def array_assn_def is_array_def hr_comp_def)

  apply (rule_tac x=\<open>p[bb := (aa, bc)]\<close> in ent_ex_postI)
  apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
    apply (solves \<open>auto\<close>)
   apply (solves \<open>auto\<close>)
(*   apply (auto simp: star_aci) *)
  sorry

lemma update_raa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_raa, uncurry3 (RETURN oooo update_rll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_rll l i]\<^sub>a (arrayO_raa (array_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arrayO_raa (array_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)

 definition swap_aa :: "('a::{heap,default}) array0_raa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array0_raa Heap" where
  \<open>swap_aa xs k i j = do {
    xi \<leftarrow> nth_raa xs k i;
    xj \<leftarrow> nth_raa xs k j;
    xs \<leftarrow> update_raa xs k i xj;
    xs \<leftarrow> update_raa xs k j xi;
    return xs
  }\<close>

definition swap_ll where
  \<open>swap_ll xs k i j = list_update xs k (swap (xs!k) i j)\<close>

lemma nth_raa_heap[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_rll aa b\<close>
  shows \<open>
   <arrayO_raa (array_assn R) aa a>
   nth_raa a b ba
   <\<lambda>r. \<exists>\<^sub>Ax. arrayO_raa (array_assn R) aa a *
               (R x r *
                \<up> (x = nth_rll aa b ba)) *
               true>\<close>
proof -
  have \<open><arrayO_raa (array_assn R) aa a *
        nat_assn b b *
        nat_assn ba ba>
       nth_raa a b ba
       <\<lambda>r. \<exists>\<^sub>Ax. arrayO_raa (array_assn R) aa a *
                   nat_assn b b *
                   nat_assn ba ba *
                   R x r *
                   true *
                   \<up> (x = nth_rll aa b ba)>\<close>
    using p assms nth_raa_hnr[of R] unfolding hfref_def hn_refine_def
    by auto
  then show ?thesis
    unfolding hoare_triple_def
    by (auto simp: Let_def pure_def)
qed

lemma update_raa_rule_pure:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_rll aa b\<close> and
    b: \<open>(bb, be) \<in> the_pure R\<close>
  shows \<open>
   <arrayO_raa (array_assn R) aa a>
           update_raa a b ba bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arrayO_raa (array_assn R)) aa a * arrayO_raa (array_assn R) x r *
                       true *
                       \<up> (x = update_rll aa b ba be)>\<close>
proof -
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using p by fastforce
  have bb: \<open>pure R' be bb = \<up>((bb, be) \<in> R')\<close>
    by (auto simp: pure_def)
  have \<open> <arrayO_raa (array_assn R) aa a * nat_assn b b * nat_assn ba ba * R be bb>
           update_raa a b ba bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arrayO_raa (array_assn R)) aa a * nat_assn b b * nat_assn ba ba *
                       R be bb *
                       arrayO_raa (array_assn R) x r *
                       true *
                       \<up> (x = update_rll aa b ba be)>\<close>
    using p assms update_raa_hnr[of R] unfolding hfref_def hn_refine_def
    by auto
  then show ?thesis
    using b unfolding R'[symmetric] unfolding hoare_triple_def RR' bb
    by (auto simp: Let_def pure_def)
qed

lemma length_update_rll[simp]: \<open>length (update_rll a bb b c) = length a\<close>
  unfolding update_rll_def by auto

lemma length_rll_update_rll:
  \<open>bb < length a \<Longrightarrow> length_rll (update_rll a bb b c) bb = length_rll a bb\<close>
  unfolding length_rll_def update_rll_def by auto

lemma swap_aa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 swap_aa, uncurry3 (RETURN oooo swap_ll)) \<in>
   [\<lambda>(((xs, k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
  (arrayO_raa (array_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> (arrayO_raa (array_assn R))\<close>
proof -
  note update_raa_rule_pure[sep_heap_rules]
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>the_pure (\<lambda>a b. \<up> ((b, a) \<in> R')) = R'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    using assms unfolding R'[symmetric] unfolding RR'
    apply sepref_to_hoare
    apply (sep_auto simp: swap_aa_def swap_ll_def (* arl_get_def *) arrayO_raa_except_def
        length_rll_update_rll)
    by (sep_auto simp: update_rll_def swap_def nth_rll_def list_update_swap)
qed

instantiation array :: (heap) default
begin
definition default_array :: \<open>'a array\<close> where
  \<open>default_array = Array (0::nat)\<close> -- \<open>This should be used nowhere in the generated code\<close>
instance
  by standard
end

definition append_raa :: \<open>'a::{heap} array0_raa \<Rightarrow> 'a array \<Rightarrow> 'a array0_raa Heap\<close> where
  \<open>append_raa xs x = arl_append xs x\<close>
export_code append_raa in SML file "tmp_test"

definition arl_append where
"arl_append \<equiv> \<lambda>(a,n) x. do {
    len \<leftarrow> Array.len a;

    if n<len then do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    } else do {
      let newcap = 2 * len;
      default \<leftarrow> Array.make 0 (\<lambda>_. default);
      a \<leftarrow> array_grow a newcap default;
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    }
  }"
definition arl_empty_sz where
"arl_empty_sz init_cap \<equiv> do {
    default \<leftarrow> Array.make 0 (\<lambda>_. default);
    a \<leftarrow> Array.new (max init_cap minimum_capacity) default;
    return (a,0)
  }"
definition \<open>test = do {
   xs \<leftarrow> (arl_empty_sz (1::nat) :: nat array0_raa Heap);
   a \<leftarrow> (Array.new 5 0 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   a \<leftarrow> (Array.new 5 1 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   a \<leftarrow> (Array.new 5 2 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   a \<leftarrow> (Array.new 5 3 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   a \<leftarrow> (Array.new 5 4 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   a \<leftarrow> (Array.new 5 5 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   a \<leftarrow> (Array.new 5 6 :: nat array Heap);
   xs \<leftarrow> arl_append xs a;
   nth_raa xs 6 1
}\<close>

export_code test in SML module_name Test

end