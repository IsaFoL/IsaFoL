theory Array_List_Array
imports Array_Array_List
begin

subsection \<open>Array of Array Lists\<close>

text \<open>There is a major difference compared to @{typ \<open>'a array_list array\<close>}: @{typ \<open>'a array_list\<close>}
  is not of sort default. This means that function like @{term arl_append} cannot be used here.\<close>

type_synonym 'a arrayO_raa = \<open>'a array array_list\<close>
type_synonym 'a list_rll = \<open>'a list list\<close>

definition arlO_assn :: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b array_list \<Rightarrow> assn\<close> where
  \<open>arlO_assn R' xs axs \<equiv> \<exists>\<^sub>Ap. arl_assn id_assn p axs * heap_list_all R' xs p\<close>

definition arlO_assn_except :: \<open>('a \<Rightarrow> 'b::heap \<Rightarrow> assn) \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'b array_list \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>arlO_assn_except R' is xs axs f \<equiv>
     \<exists>\<^sub>A p. arl_assn id_assn p axs * heap_list_all_nth R' (fold remove1 is [0..<length xs]) xs p *
    \<up> (length xs = length p) * f p\<close>

lemma arlO_assn_except_array0: \<open>arlO_assn_except R [] xs asx (\<lambda>_. emp) = arlO_assn R xs asx\<close>
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
    unfolding arlO_assn_except_def arlO_assn_def by (auto simp: ex_assn_def)
qed

lemma arlO_assn_except_array0_index:
  \<open>i < length xs \<Longrightarrow> arlO_assn_except R [i] xs asx (\<lambda>p. R (xs ! i) (p ! i)) = arlO_assn R xs asx\<close>
  unfolding arlO_assn_except_array0[symmetric] arlO_assn_except_def
  using heap_list_all_nth_remove1[of i \<open>[0..<length xs]\<close> R xs] by (auto simp: star_aci(2,3))

lemma arrayO_raa_nth_rule[sep_heap_rules]:
  assumes i: \<open>i < length a\<close>
  shows \<open> <arlO_assn (array_assn R) a ai> arl_get ai i <\<lambda>r. arlO_assn_except (array_assn R) [i] a ai
   (\<lambda>r'. array_assn R (a ! i) r * \<up>(r = r' ! i))>\<close>
proof -
  obtain t n where ai: \<open>ai = (t, n)\<close> by (cases ai)
  have i_le: \<open>i < Array.length h t\<close> if \<open>(h, as) \<Turnstile> arlO_assn (array_assn R) a ai\<close> for h as
    using ai that i unfolding arlO_assn_def array_assn_def is_array_def arl_assn_def is_array_list_def
    by (auto simp: run.simps tap_def arlO_assn_def
        mod_star_conv array_assn_def is_array_def
        Abs_assn_inverse heap_list_add_same_length length_def snga_assn_def
        dest: heap_list_add_same_length)
  show ?thesis
    unfolding hoare_triple_def Let_def
  proof (clarify, intro allI impI conjI)
    fix h as \<sigma> r
    assume
      a: \<open>(h, as) \<Turnstile> arlO_assn (array_assn R) a ai\<close> and
      r: \<open>run (arl_get ai i) (Some h) \<sigma> r\<close>
    have [simp]: \<open>length a = n\<close>
      using a ai
      by (auto simp: arlO_assn_def mod_star_conv arl_assn_def is_array_list_def
          dest: heap_list_add_same_length)
    obtain p where
      p: \<open>(h, as) \<Turnstile> arl_assn id_assn p (t, n) *
            heap_list_all_nth (array_assn R) (remove1 i [0..<length p]) a p *
            array_assn R (a ! i) (p ! i)\<close>
      using assms a ai
      by (auto simp: hoare_triple_def Let_def execute_simps relH_def in_range.simps
          arlO_assn_except_array0_index[of i, symmetric] arl_get_def
          arlO_assn_except_array0_index arlO_assn_except_def
          elim!: run_elims
          intro!: norm_pre_ex_rule)
    then have \<open>(Array.get h t ! i) = p ! i\<close>
      using ai i i_le unfolding arlO_assn_except_array0_index
      apply (auto simp: mod_star_conv array_assn_def is_array_def snga_assn_def
          Abs_assn_inverse arl_assn_def)
      unfolding is_array_list_def is_array_def hr_comp_def list_rel_def
      apply (auto simp: mod_star_conv array_assn_def is_array_def snga_assn_def
          Abs_assn_inverse arl_assn_def from_nat_def
          intro!: nth_take[symmetric])
      done
    moreover have \<open>length p = n\<close>
      using p ai by (auto simp: arl_assn_def is_array_list_def)

    ultimately show \<open>(the_state \<sigma>, new_addrs h as (the_state \<sigma>)) \<Turnstile>
        arlO_assn_except (array_assn R) [i] a ai (\<lambda>r'. array_assn R (a ! i) r * \<up> (r = r' ! i))\<close>
      using assms ai i_le r p
      by (fastforce simp: hoare_triple_def Let_def execute_simps relH_def in_range.simps
          arlO_assn_except_array0_index[of i, symmetric] arl_get_def
          arlO_assn_except_array0_index arlO_assn_except_def
          elim!: run_elims
          intro!: norm_pre_ex_rule)
  qed ((solves \<open>use assms ai i_le in \<open>auto simp: hoare_triple_def Let_def execute_simps relH_def
    in_range.simps arlO_assn_except_array0_index[of i, symmetric] arl_get_def
        elim!: run_elims
        intro!: norm_pre_ex_rule\<close>\<close>)+)[3]
qed

definition length_ra :: \<open>'a::heap arrayO_raa \<Rightarrow> nat Heap\<close> where
  \<open>length_ra xs = arl_length xs\<close>

lemma length_ra_rule[sep_heap_rules]:
   \<open><arlO_assn R x xi> length_ra xi <\<lambda>r. arlO_assn R x xi * \<up>(r = length x)>\<^sub>t\<close>
  by (sep_auto simp: arlO_assn_def length_ra_def mod_star_conv arl_assn_def
      dest: heap_list_add_same_length)

lemma length_ra_hnr[sepref_fr_rules]:
  \<open>(length_ra, RETURN o op_list_length) \<in> (arlO_assn R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

definition length_rll :: \<open>'a list_rll \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>length_rll l i = length (l!i)\<close>

lemma le_length_rll_nemptyD: \<open>b < length_rll a ba \<Longrightarrow> a ! ba \<noteq> []\<close>
  by (auto simp: length_rll_def)

definition length_raa :: \<open>'a::heap arrayO_raa \<Rightarrow> nat \<Rightarrow> nat Heap\<close> where
  \<open>length_raa xs i = do {
     x \<leftarrow> arl_get xs i;
    Array.len x}\<close>

lemma length_raa_rule[sep_heap_rules]:
  \<open>b < length xs \<Longrightarrow> <arlO_assn (array_assn R) xs a> length_raa a b
   <\<lambda>r. arlO_assn (array_assn R) xs a * \<up> (r = length_rll xs b)>\<^sub>t\<close>
  unfolding length_raa_def
  apply (cases a)
  apply sep_auto
  apply (sep_auto simp: arlO_assn_except_def arl_length_def array_assn_def
      eq_commute[of \<open>(_, _)\<close>] is_array_def hr_comp_def length_rll_def
      dest: list_all2_lengthD)
   apply (sep_auto simp: arlO_assn_except_def arl_length_def arl_assn_def
      eq_commute[of \<open>(_, _)\<close>] is_array_list_def hr_comp_def length_rll_def list_rel_def
      dest: list_all2_lengthD)[]
  unfolding arlO_assn_def[symmetric] arl_assn_def[symmetric]
  apply (subst arlO_assn_except_array0_index[symmetric, of b])
   apply simp
  unfolding arlO_assn_except_def arl_assn_def hr_comp_def is_array_def
  apply sep_auto
  done

lemma length_raa_hnr[sepref_fr_rules]: \<open>(uncurry length_raa, uncurry (RETURN \<circ>\<circ> length_rll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare sep_auto

definition nth_raa :: \<open>'a::heap arrayO_raa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Heap\<close> where
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
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have H: \<open>list_all2 (\<lambda>x x'. (x, x') \<in> the_pure (\<lambda>a c. \<up> ((c, a) \<in> R'))) bc (a ! ba) \<Longrightarrow>
       b < length (a ! ba) \<Longrightarrow>
       (bc ! b, a ! ba ! b) \<in> R'\<close> for bc a ba b
    by (auto simp add: ent_refl_true list_all2_conv_all_nth is_pure_alt_def pure_app_eq[symmetric])
  show ?thesis
    supply nth_rule[sep_heap_rules]
    apply sepref_to_hoare
    apply (subst (2) arlO_assn_except_array0_index[symmetric])
     apply (solves \<open>auto\<close>)[]
    apply (sep_auto simp: nth_raa_def nth_rll_def length_rll_def)
    apply (sep_auto simp: arlO_assn_except_def arlO_assn_def arl_assn_def hr_comp_def list_rel_def
        list_all2_lengthD array_assn_def is_array_def hr_comp_def[abs_def]
        star_aci(3) R R' pure_def H)
    done
qed

definition update_raa :: "('a::{heap,default}) arrayO_raa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a arrayO_raa Heap" where
  \<open>update_raa a i j y = do {
      x \<leftarrow> arl_get a i;
      a' \<leftarrow> Array.upd j y x;
      arl_set a i a'
    }\<close> \<comment> \<open>is the Array.upd really needed?\<close>

definition update_rll :: "'a list_rll \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  \<open>update_rll xs i j y = xs[i:= (xs ! i)[j := y]]\<close>

declare nth_rule[sep_heap_rules del]
declare arrayO_raa_nth_rule[sep_heap_rules]

text \<open>TODO: is it possible to be more precise and not drop the \<^term>\<open>\<up> ((aa, bc) = r' ! bb)\<close>\<close>
lemma arlO_assn_except_arl_set[sep_heap_rules]:
  fixes R :: \<open>'a \<Rightarrow> 'b :: {heap} \<Rightarrow> assn\<close>
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and
    \<open>ba < length_rll a bb\<close>
  shows \<open>
       <arlO_assn_except (array_assn R) [bb] a ai (\<lambda>r'. array_assn R (a ! bb) aa *
         \<up> (aa = r' ! bb)) * R b bi>
       Array.upd ba bi aa
      <\<lambda>aa. arlO_assn_except (array_assn R) [bb] a ai
        (\<lambda>r'. array_assn R ((a ! bb)[ba := b]) aa) * R b bi * true>\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  show ?thesis
    using assms
    by (cases ai)
      (sep_auto simp: arlO_assn_except_def arl_assn_def hr_comp_def list_rel_imp_same_length
        list_rel_update length_rll_def array_assn_def is_array_def)
qed

lemma update_raa_rule[sep_heap_rules]:
  assumes p: \<open>is_pure R\<close> and \<open>bb < length a\<close> and \<open>ba < length_rll a bb\<close>
  shows \<open><R b bi * arlO_assn (array_assn R) a ai> update_raa ai bb ba bi
      <\<lambda>r. R b bi * (\<exists>\<^sub>Ax. arlO_assn (array_assn R) x r * \<up> (x = update_rll a bb ba b))>\<^sub>t\<close>
  using assms
  apply (sep_auto simp add: update_raa_def update_rll_def p)
  apply (sep_auto simp add: update_raa_def arlO_assn_except_def array_assn_def is_array_def hr_comp_def
      arl_assn_def)
  apply (subst_tac i=bb in arlO_assn_except_array0_index[symmetric])
   apply (solves \<open>simp\<close>)
  apply (subst arlO_assn_except_def)
  apply (auto simp add: update_raa_def arlO_assn_except_def array_assn_def is_array_def hr_comp_def)

  apply (rule_tac x=\<open>p[bb := xa]\<close> in ent_ex_postI)
  apply (rule_tac x=\<open>bc\<close> in ent_ex_postI)
  apply (subst_tac (2)xs'=a and ys'=p in heap_list_all_nth_cong)
    apply (solves \<open>auto\<close>)
   apply (solves \<open>auto\<close>)
  by (sep_auto simp: arl_assn_def)

lemma update_raa_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry3 update_raa, uncurry3 (RETURN oooo update_rll)) \<in>
     [\<lambda>(((l,i), j), x). i < length l \<and> j < length_rll l i]\<^sub>a (arlO_assn (array_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> (arlO_assn (array_assn R))\<close>
  by sepref_to_hoare (sep_auto simp: assms)

 definition swap_aa :: "('a::{heap,default}) arrayO_raa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a arrayO_raa Heap" where
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
   <arlO_assn (array_assn R) aa a>
   nth_raa a b ba
   <\<lambda>r. \<exists>\<^sub>Ax. arlO_assn (array_assn R) aa a *
               (R x r *
                \<up> (x = nth_rll aa b ba)) *
               true>\<close>
proof -
  have \<open><arlO_assn (array_assn R) aa a *
        nat_assn b b *
        nat_assn ba ba>
       nth_raa a b ba
       <\<lambda>r. \<exists>\<^sub>Ax. arlO_assn (array_assn R) aa a *
                   nat_assn b b *
                   nat_assn ba ba *
                   R x r *
                   true *
                   \<up> (x = nth_rll aa b ba)>\<close>
    using p assms nth_raa_hnr[of R] unfolding hfref_def hn_refine_def
    by (cases a) auto
  then show ?thesis
    unfolding hoare_triple_def
    by (auto simp: Let_def pure_def)
qed

lemma update_raa_rule_pure:
  assumes p: \<open>is_pure R\<close> and \<open>b < length aa\<close> and \<open>ba < length_rll aa b\<close> and
    b: \<open>(bb, be) \<in> the_pure R\<close>
  shows \<open>
   <arlO_assn (array_assn R) aa a>
           update_raa a b ba bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arlO_assn (array_assn R)) aa a * arlO_assn (array_assn R) x r *
                       true *
                       \<up> (x = update_rll aa b ba be)>\<close>
proof -
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using p by fastforce
  have bb: \<open>pure R' be bb = \<up>((bb, be) \<in> R')\<close>
    by (auto simp: pure_def)
  have \<open> <arlO_assn (array_assn R) aa a * nat_assn b b * nat_assn ba ba * R be bb>
           update_raa a b ba bb
           <\<lambda>r. \<exists>\<^sub>Ax. invalid_assn (arlO_assn (array_assn R)) aa a * nat_assn b b * nat_assn ba ba *
                       R be bb *
                       arlO_assn (array_assn R) x r *
                       true *
                       \<up> (x = update_rll aa b ba be)>\<close>
    using p assms update_raa_hnr[of R] unfolding hfref_def hn_refine_def
    by (cases a) auto
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
  (arlO_assn (array_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> (arlO_assn (array_assn R))\<close>
proof -
  note update_raa_rule_pure[sep_heap_rules]
  obtain R' where R': \<open>R' = the_pure R\<close> and RR': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>the_pure (\<lambda>a b. \<up> ((b, a) \<in> R')) = R'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    using assms unfolding R'[symmetric] unfolding RR'
    apply sepref_to_hoare
    apply (sep_auto simp: swap_aa_def swap_ll_def arlO_assn_except_def
        length_rll_update_rll)
    by (sep_auto simp: update_rll_def swap_def nth_rll_def list_update_swap)
qed

definition update_ra :: \<open>'a arrayO_raa \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> 'a arrayO_raa Heap\<close> where
  \<open>update_ra xs n x = arl_set xs n x\<close>


lemma update_ra_list_update_rules[sep_heap_rules]:
  assumes \<open>n < length l\<close>
  shows \<open><R y x * arlO_assn R l xs> update_ra xs n x <arlO_assn R (l[n:=y])>\<^sub>t\<close>
proof -
  have H: \<open>heap_list_all R l p = heap_list_all R l p * \<up> (n < length p)\<close> for p
    using assms by (simp add: ent_iffI heap_list_add_same_length)
  have [simp]: \<open>heap_list_all_nth R (remove1 n [0..<length p]) (l[n := y]) (p[n := x]) =
    heap_list_all_nth R (remove1 n [0..<length p]) (l) (p)\<close> for p
    by (rule heap_list_all_nth_cong) auto
  show ?thesis
    using assms
    apply (cases xs)
    supply arl_set_rule[sep_heap_rules del]
    apply (sep_auto simp: arlO_assn_def update_ra_def Let_def arl_assn_def
        dest!: heap_list_add_same_length
        elim!: run_elims)
    apply (subst H)
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst heap_list_all_nth_remove1[where i = n])
      apply (solves \<open>simp\<close>)
    apply (subst heap_list_all_heap_list_all_nth_eq)
    apply (subst (2) heap_list_all_nth_remove1[where i = n])
      apply (solves \<open>simp\<close>)
    supply arl_set_rule[sep_heap_rules]
    apply (sep_auto (plain))
     apply (subgoal_tac \<open>length (l[n := y]) = length (p[n := x])\<close>)
      apply assumption
     apply auto[]
    apply sep_auto
    done
qed
lemma ex_assn_up_eq: \<open>(\<exists>\<^sub>Ax. P x * \<up>(x = a) * Q) = (P a * Q)\<close>
  by (smt ex_one_point_gen mod_pure_star_dist mod_starE mult.right_neutral pure_true)
lemma update_ra_list_update[sepref_fr_rules]:
  \<open>(uncurry2 update_ra, uncurry2 (RETURN ooo list_update)) \<in>
   [\<lambda>((xs, n), _). n < length xs]\<^sub>a (arlO_assn R)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a R\<^sup>d \<rightarrow> (arlO_assn R)\<close>
proof -
  have [simp]: \<open>(\<exists>\<^sub>Ax. arlO_assn R x r * true * \<up> (x = list_update a ba b)) =
        arlO_assn R (a[ba := b]) r * true\<close>
    for a ba b r
    apply (subst assn_aci(10))
    apply (subst ex_assn_up_eq)
    ..
  show ?thesis
    by sepref_to_hoare sep_auto
qed
term arl_append
definition arrayO_raa_append where
"arrayO_raa_append \<equiv> \<lambda>(a,n) x. do {
    len \<leftarrow> Array.len a;
    if n<len then do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    } else do {
      let newcap = 2 * len;
      default \<leftarrow> Array.new 0 default;
      a \<leftarrow> array_grow a newcap default;
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    }
  }"

lemma heap_list_all_append_Nil:
  \<open>y \<noteq> [] \<Longrightarrow> heap_list_all R (va @ y) [] = false\<close>
  by (cases va; cases y) auto

lemma heap_list_all_Nil_append:
  \<open>y \<noteq> [] \<Longrightarrow> heap_list_all R [] (va @ y) = false\<close>
  by (cases va; cases y) auto

lemma heap_list_all_append: \<open>heap_list_all R (l @ [y]) (l' @ [x])
  = heap_list_all R (l) (l') * R y x\<close>
  by (induction R l l' rule: heap_list_all.induct)
    (auto simp: ac_simps heap_list_all_Nil_append heap_list_all_append_Nil)
term arrayO_raa
lemma arrayO_raa_append_rule[sep_heap_rules]:
  \<open><arlO_assn R l a * R y x>  arrayO_raa_append a x <\<lambda>a. arlO_assn R (l@[y]) a >\<^sub>t\<close>
proof -
  have 1: \<open>arl_assn id_assn p a * heap_list_all R l p =
       arl_assn id_assn p a *  heap_list_all R l p * \<up> (length l = length p)\<close> for p
    by (smt ent_iffI ent_pure_post_iff entailsI heap_list_add_same_length mult.right_neutral
        pure_false pure_true star_false_right)

  show ?thesis
    unfolding arrayO_raa_append_def arrayO_raa_append_def arlO_assn_def
      length_ra_def arl_length_def hr_comp_def
    apply (subst 1)
    unfolding arl_assn_def is_array_list_def hr_comp_def
    apply (cases a)
    apply sep_auto
       apply (rule_tac psi=\<open>Suc (length l) \<le> length (l'[length l := x])\<close> in asm_rl)
       apply simp
      apply simp
     apply (sep_auto simp: take_update_last heap_list_all_append)
    apply (sep_auto (plain))
     apply sep_auto
    apply (sep_auto (plain))
     apply sep_auto
    apply (sep_auto (plain))
      apply sep_auto
      apply (rule_tac psi = \<open>Suc (length p) \<le> length ((p @ replicate (length p) xa)[length p := x])\<close>
        in asm_rl)
      apply sep_auto
     apply sep_auto
    apply (sep_auto simp: heap_list_all_append)
    done
qed

lemma arrayO_raa_append_op_list_append[sepref_fr_rules]:
  \<open>(uncurry arrayO_raa_append, uncurry (RETURN oo op_list_append)) \<in>
   (arlO_assn R)\<^sup>d *\<^sub>a R\<^sup>d \<rightarrow>\<^sub>a arlO_assn R\<close>
  apply sepref_to_hoare
  apply (subst mult.commute)
  apply (subst mult.assoc)
  by (sep_auto simp: ex_assn_up_eq)

definition array_of_arl :: \<open>'a list \<Rightarrow> 'a list\<close> where
  \<open>array_of_arl xs = xs\<close>

definition array_of_arl_raa :: "'a::heap array_list \<Rightarrow> 'a array Heap" where
  \<open>array_of_arl_raa = (\<lambda>(a, n). array_shrink a n)\<close>

lemma array_of_arl[sepref_fr_rules]:
   \<open>(array_of_arl_raa, RETURN o array_of_arl) \<in> (arl_assn R)\<^sup>d \<rightarrow>\<^sub>a (array_assn R)\<close>
  by sepref_to_hoare
   (sep_auto simp: array_of_arl_raa_def arl_assn_def is_array_list_def hr_comp_def
      array_assn_def is_array_def array_of_arl_def)

definition "arrayO_raa_empty \<equiv> do {
    a \<leftarrow> Array.new initial_capacity default;
    return (a,0)
  }"

lemma arrayO_raa_empty_rule[sep_heap_rules]: "< emp > arrayO_raa_empty <\<lambda>r. arlO_assn R [] r>"
  by (sep_auto simp: arrayO_raa_empty_def is_array_list_def initial_capacity_def
      arlO_assn_def arl_assn_def)

definition arrayO_raa_empty_sz where
"arrayO_raa_empty_sz init_cap \<equiv> do {
    default \<leftarrow> Array.new 0 default;
    a \<leftarrow> Array.new (max init_cap minimum_capacity) default;
    return (a,0)
  }"

lemma arl_empty_sz_array_rule[sep_heap_rules]: "< emp > arrayO_raa_empty_sz N <\<lambda>r. arlO_assn R [] r>\<^sub>t"
proof -
  have [simp]: \<open>(xa \<mapsto>\<^sub>a replicate (max N 16) x) * x \<mapsto>\<^sub>a [] = (xa \<mapsto>\<^sub>a (x # replicate (max N 16 - 1) x)) * x \<mapsto>\<^sub>a []\<close>
    for xa x
    by (cases N) (sep_auto simp: arrayO_raa_empty_sz_def is_array_list_def minimum_capacity_def max_def)+
  show ?thesis
    by (sep_auto simp: arrayO_raa_empty_sz_def is_array_list_def minimum_capacity_def
        arlO_assn_def arl_assn_def)
qed

definition nth_rl :: \<open>'a::heap arrayO_raa \<Rightarrow> nat \<Rightarrow> 'a array Heap\<close> where
  \<open>nth_rl xs n = do {x \<leftarrow> arl_get xs n; array_copy x}\<close>

lemma nth_rl_op_list_get:
  \<open>(uncurry nth_rl, uncurry (RETURN oo op_list_get)) \<in>
    [\<lambda>(xs, n). n < length xs]\<^sub>a (arlO_assn (array_assn R))\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_assn R\<close>
  apply sepref_to_hoare
  unfolding arlO_assn_def heap_list_all_heap_list_all_nth_eq
  apply (subst_tac i=b in heap_list_all_nth_remove1)
   apply (solves \<open>simp\<close>)
  apply (subst_tac (2) i=b in heap_list_all_nth_remove1)
   apply (solves \<open>simp\<close>)
  by (sep_auto simp: nth_rl_def arlO_assn_def heap_list_all_heap_list_all_nth_eq array_assn_def
      hr_comp_def[abs_def] is_array_def arl_assn_def)

definition arl_of_array :: "'a list list \<Rightarrow> 'a list list" where
  \<open>arl_of_array xs = xs\<close>

definition arl_of_array_raa :: "'a::heap array \<Rightarrow> ('a array_list) Heap" where
  \<open>arl_of_array_raa xs = do {
     n \<leftarrow> Array.len xs;
     return (xs, n)
  }\<close>

lemma arl_of_array_raa: \<open>(arl_of_array_raa, RETURN o arl_of_array) \<in>
       [\<lambda>xs. xs \<noteq> []]\<^sub>a (array_assn R)\<^sup>d \<rightarrow> (arl_assn R)\<close>
  by sepref_to_hoare (sep_auto simp: arl_of_array_raa_def arl_assn_def is_array_list_def hr_comp_def
      array_assn_def is_array_def arl_of_array_def)

end
