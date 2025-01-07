theory Nonground_Term_Order
  imports
    Nonground_Term
    Nonground_Context
    Ground_Order
begin

locale ground_context_compatible_order =
  nonground_term_with_context +
  restricted_total_strict_order where restriction = "range term.from_ground" +
assumes ground_context_compatibility: 
  "\<And>c t\<^sub>1 t\<^sub>2. 
      term.is_ground t\<^sub>1 \<Longrightarrow>
      term.is_ground t\<^sub>2 \<Longrightarrow>
      context.is_ground c \<Longrightarrow>
      t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow>
      c\<langle>t\<^sub>1\<rangle> \<prec> c\<langle>t\<^sub>2\<rangle>"
begin

sublocale context_compatible_restricted_order where 
  restriction = "range term.from_ground" and context_restriction = "range context.from_ground" and
  Fun = Fun and restricted = term.is_ground and restricted_context = context.is_ground
  using ground_context_compatibility
  by unfold_locales 
    (auto simp: term.is_ground_iff_range_from_ground context.is_ground_iff_range_from_ground)

end

locale ground_subterm_property =
  nonground_term_with_context +
  fixes R
  assumes ground_subterm_property: 
    "\<And>t\<^sub>G c\<^sub>G. 
      term.is_ground t\<^sub>G \<Longrightarrow>
      context.is_ground c\<^sub>G \<Longrightarrow>
      c\<^sub>G \<noteq> \<box> \<Longrightarrow>
      R t\<^sub>G c\<^sub>G\<langle>t\<^sub>G\<rangle>"

locale base_grounded_order = 
  order: base_subst_update_stable_grounded_order  +
  order: grounded_restricted_total_strict_order +
  order: grounded_restricted_wellfounded_strict_order +
  order: ground_subst_stable_grounded_order +
  grounding

locale nonground_term_order = 
  nonground_term_with_context +
  order: restricted_wellfounded_total_strict_order where 
  less = less\<^sub>t and restriction = "range term.from_ground" +
  order: ground_subst_stability where R = less\<^sub>t and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and 
  vars = term.vars and id_subst = Var and to_ground = term.to_ground and 
  from_ground = "term.from_ground" + 
  order: ground_context_compatible_order where less = less\<^sub>t  +
  order: ground_subterm_property where R = less\<^sub>t
for less\<^sub>t :: "('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> bool"
begin

interpretation term_order_notation.

sublocale base_grounded_order where
  comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and vars = term.vars and id_subst = Var and 
  to_ground = term.to_ground and from_ground = "term.from_ground" and less = "(\<prec>\<^sub>t)"
proof unfold_locales
  fix update x \<gamma> and t :: "('f, 'v) term"
  assume 
    update_is_ground: "term.is_ground update" and 
    update_less: "update \<prec>\<^sub>t \<gamma> x" and 
    term_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    var: "x \<in> term.vars t"

  from term_grounding var 
  show "t \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t t \<cdot>t \<gamma>" 
  proof(induction t)
    case Var
    then show ?case 
      using update_is_ground update_less
      by simp
  next
    case (Fun f subs)

    then have "\<forall>sub \<in> set subs. sub \<cdot>t \<gamma>(x := update) \<preceq>\<^sub>t sub \<cdot>t \<gamma>"
      by (metis eval_with_fresh_var is_ground_iff reflclp_iff term.set_intros(4))

    moreover then have "\<exists>sub \<in> set subs. sub \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t sub \<cdot>t \<gamma>"
      using Fun update_less
      by (metis (full_types) fun_upd_same term.distinct(1) term.sel(4) term.set_cases(2)
          order.dual_order.strict_iff_order term_subst_eq_rev)

    ultimately show ?case
      using Fun(2, 3)
    proof(induction "filter (\<lambda>sub. sub \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t sub \<cdot>t \<gamma>) subs" arbitrary: subs)
      case Nil
      then show ?case
        unfolding empty_filter_conv
        by blast
    next
      case first: (Cons s ss)

      have groundings [simp]: "term.is_ground (s \<cdot>t \<gamma>(x := update))" "term.is_ground (s \<cdot>t \<gamma>)"
        using term.ground_subst_update update_is_ground
        by (metis (lifting) filter_eq_ConsD first.hyps(2) first.prems(3) in_set_conv_decomp 
            is_ground_iff term.set_intros(4))+

      show ?case
      proof(cases ss)
        case Nil
        then obtain ss1 ss2 where subs: "subs = ss1 @ s # ss2"
          using filter_eq_ConsD[OF first.hyps(2)[symmetric]]
          by blast

        have ss1: "\<forall>s \<in> set ss1. s \<cdot>t \<gamma>(x := update) = s \<cdot>t \<gamma>"
          using first.hyps(2) first.prems(1) 
          unfolding Nil subs
          by (smt (verit, del_insts) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD 
              set_append order.antisym_conv2)

        have ss2: "\<forall>s \<in> set ss2. s \<cdot>t \<gamma>(x := update) = s \<cdot>t \<gamma>"
          using first.hyps(2) first.prems(1) 
          unfolding Nil subs
          by (smt (verit, ccfv_SIG) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD 
              list.set_intros(2) set_append order.antisym_conv2)

        let ?c = "More f ss1 \<box> ss2 \<cdot>t\<^sub>c \<gamma>"

        have "context.is_ground ?c"
          using subs first(5)
          by auto

        moreover have "s \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t s \<cdot>t \<gamma>" 
          using first.hyps(2)
          by (meson Cons_eq_filterD)

        ultimately have "?c\<langle>s \<cdot>t \<gamma>(x := update)\<rangle> \<prec>\<^sub>t ?c\<langle>s \<cdot>t \<gamma>\<rangle>"
          using order.ground_context_compatibility groundings
          by blast

        moreover have "Fun f subs \<cdot>t \<gamma>(x := update) = ?c\<langle>s \<cdot>t \<gamma>(x := update)\<rangle>"
          unfolding subs
          using ss1 ss2
          by simp

        moreover have "Fun f subs \<cdot>t \<gamma> = ?c\<langle>s \<cdot>t \<gamma>\<rangle>"
          unfolding subs
          by auto

        ultimately show ?thesis
          by argo
      next
        case (Cons t' ts')

        from first(2)
        obtain ss1 ss2 where
          subs: "subs = ss1 @ s # ss2" and
          ss1: "\<forall>s\<in>set ss1. \<not> s \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t s \<cdot>t \<gamma>" and
          less: "s \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t s \<cdot>t \<gamma>" and 
          ss: "ss = filter (\<lambda>term. term \<cdot>t \<gamma>(x := update)\<prec>\<^sub>t term \<cdot>t \<gamma>) ss2"
          using Cons_eq_filter_iff[of s ss "(\<lambda>s. s \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t s \<cdot>t \<gamma>)"]
          by blast

        let ?subs' = "ss1 @ (s \<cdot>t \<gamma>(x := update)) # ss2"

        have [simp]: "s \<cdot>t \<gamma>(x := update) \<cdot>t \<gamma> = s \<cdot>t \<gamma>(x := update)"
          using first.prems(3) update_is_ground
          unfolding subs
          by (simp add: is_ground_iff)

        have [simp]: "s \<cdot>t \<gamma>(x := update) \<cdot>t \<gamma>(x := update) = s \<cdot>t \<gamma>(x := update)"
          using first.prems(3) update_is_ground
          unfolding subs
          by (simp add: is_ground_iff)

        have ss: "ss = filter (\<lambda>sub. sub \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t sub \<cdot>t \<gamma>) ?subs'" 
          using ss1 ss
          by auto

        moreover have "\<forall>sub \<in> set ?subs'. sub \<cdot>t \<gamma>(x := update) \<preceq>\<^sub>t sub \<cdot>t \<gamma>"
          using first.prems(1)
          unfolding subs
          by simp

        moreover have ex_less: "\<exists>sub \<in> set ?subs'. sub \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t sub \<cdot>t \<gamma>"
          using ss Cons neq_Nil_conv 
          by force

        moreover have subs'_grounding: "term.is_ground (Fun f ?subs' \<cdot>t \<gamma>)"
          using first.prems(3)
          unfolding subs
          by simp

        moreover have "x \<in> term.vars (Fun f ?subs')"
          by (metis ex_less eval_with_fresh_var term.set_intros(4) order.less_irrefl)

        ultimately have less_subs': "Fun f ?subs' \<cdot>t \<gamma>(x := update) \<prec>\<^sub>t Fun f ?subs' \<cdot>t \<gamma>"
          using first.hyps(1) first.prems(3) 
          by blast

        have context_grounding: "context.is_ground (More f ss1 \<box> ss2 \<cdot>t\<^sub>c \<gamma>)"
          using subs'_grounding
          by auto

        have "Fun f (ss1 @ s \<cdot>t \<gamma>(x := update) # ss2) \<cdot>t \<gamma> \<prec>\<^sub>t Fun f subs \<cdot>t \<gamma>"
          unfolding subs
          using order.ground_context_compatibility[OF _ _ context_grounding less]
          by simp

        with less_subs' show ?thesis 
          unfolding subs
          by simp
      qed
    qed
  qed
qed

(* TODO: Find way to not have this twice \<longrightarrow> Use here just with G when up the t are also removed *)
notation order.less\<^sub>G (infix "\<prec>\<^sub>t\<^sub>G" 50)
notation order.less_eq\<^sub>G (infix "\<preceq>\<^sub>t\<^sub>G" 50)

sublocale restriction: ground_term_order "(\<prec>\<^sub>t\<^sub>G)"
proof unfold_locales
  fix c t t'
  assume "t \<prec>\<^sub>t\<^sub>G t'"
  then show "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G c\<langle>t'\<rangle>\<^sub>G"
    using order.ground_context_compatibility[OF
        term.ground_is_ground term.ground_is_ground context.ground_is_ground]
    unfolding order.less\<^sub>G_def
    by simp
next
  fix t :: "'f gterm" and c :: "'f ground_context"
  assume "c \<noteq> \<box>"
  then show "t \<prec>\<^sub>t\<^sub>G c\<langle>t\<rangle>\<^sub>G"
    using order.ground_subterm_property[OF term.ground_is_ground context.ground_is_ground]
    unfolding order.less\<^sub>G_def
    by simp
qed

end

end
