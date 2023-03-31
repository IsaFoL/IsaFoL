theory Splitting_Calculi
  imports
    Preliminaries_With_Zorn
    Light_Lifting_to_Non_Ground_Calculi
begin

section \<open>Splitting calculi\<close>

locale splitting_calculus = AF_calculus bot Inf entails entails_sound Red_I Red_F V fml
  for
    bot :: 'f and
    Inf :: \<open>'f inference set\<close> and
    entails :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
    entails_sound :: \<open>[ 'f set, 'f set ] \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
    Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
    Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
    V :: \<open>'v :: countable itself\<close> and
    fml :: \<open>'v \<Rightarrow> 'f\<close>
  + assumes
      (* D6 *)
      entails_sound_nontrivial: \<open>\<not> {} \<Turnstile>s {}\<close> and
      (* /!\ This needs to be approved, but we need it for theorem 21 (currently) /!\ *)
      (* entails_nontrivial: \<open>\<not> {} \<Turnstile> {}\<close> and *)
      (* R5 *)
      reducedness: \<open>Inf_between UNIV (Red_F N) \<subseteq> Red_I N\<close> and
      (* R6 *)
      complete: \<open>bot \<notin> Red_F N\<close> and
      (* R7 *)
      all_red_to_bot: \<open>\<C> \<noteq> bot \<Longrightarrow> \<C> \<in> Red_F {bot}\<close>
begin

(* TODO: remove proof once this is done in Preliminaries_With_Zorn.thy *)
interpretation neg_ext_sound_cons_rel: consequence_relation "Pos bot" sound_cons.entails_neg
  using sound_cons.ext_cons_rel by simp

interpretation AF_sound_cons_rel: consequence_relation "to_AF bot" AF_entails_sound
proof
  show \<open>{to_AF bot} \<Turnstile>s\<^sub>A\<^sub>F {}\<close>
   (* using sound_cons.bot_entails_empty sound_cons.entails_subsets *)
   unfolding AF_entails_sound_def enabled_def enabled_projection_def
  proof clarsimp
   fix J
   assume \<open>enabled_set {} J\<close>
   have bot_in: \<open>{Pos bot} \<subseteq> Pos ` {C. C = F_of (to_AF bot) \<and> fset (A_of (to_AF bot)) \<subseteq> total_strip J}\<close>
     unfolding to_AF_def by simp
   show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
     Pos ` {C. C = F_of (to_AF bot) \<and> fset (A_of (to_AF bot)) \<subseteq> total_strip J}) {}\<close>
     using sound_cons.bot_entails_empty sound_cons.entails_subsets bot_in
     by (smt (verit, ccfv_threshold) AF.sel(2) Un_iff bot_fset.rep_eq
       consequence_relation.bot_entails_empty consequence_relation.entails_subsets empty_subsetI
       image_iff mem_Collect_eq sound_cons.ext_cons_rel subset_eq to_AF_def)
 qed
next
  fix \<C> :: "('f, 'v) AF"
  have \<open>Pos ` {F_of Ca |Ca. Ca \<in> {\<C>} \<and> fset (A_of Ca) \<subseteq> total_strip J} \<subseteq> (Pos ` F_of ` {\<C>})\<close>
    by auto
  show \<open>{\<C>} \<Turnstile>s\<^sub>A\<^sub>F {\<C>}\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof clarsimp
    fix J
    assume \<open>fset (A_of \<C>) \<subseteq> total_strip J\<close>
    show \<open>sound_cons.entails_neg (Pos (F_of \<C>) \<triangleright> fml_ext ` total_strip J) {Pos (F_of \<C>)}\<close>
      using sound_cons.entails_reflexive[of "F_of \<C>"]
      by (smt (verit, best) Set.insert_mono bot.extremum consequence_relation.entails_reflexive
        consequence_relation.entails_subsets sound_cons.ext_cons_rel)
  qed
next
  fix \<M> \<N> \<P> \<Q>
  assume m_in_n: \<open>\<M> \<subseteq> \<N>\<close> and
    p_in_q: \<open>\<P> \<subseteq> \<Q>\<close> and
    m_entails_p: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F \<P>\<close>
  show \<open>\<N> \<Turnstile>s\<^sub>A\<^sub>F \<Q>\<close>
    unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
  proof clarsimp
    fix J
    assume q_enabled: \<open>\<forall>\<C>\<in>\<Q>. fset (A_of \<C>) \<subseteq> total_strip J\<close>
    have \<open>{F_of \<C> |\<C>. \<C> \<in> \<M> \<and> fset (A_of \<C>) \<subseteq> total_strip J} \<subseteq>
      {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}\<close>
      using m_in_n by blast
    moreover have \<open>F_of ` \<P> \<subseteq> F_of ` \<Q>\<close>
      using p_in_q by blast
    ultimately show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union>
      Pos ` {F_of \<C> |\<C>. \<C> \<in> \<N> \<and> fset (A_of \<C>) \<subseteq> total_strip J}) (Pos ` F_of ` \<Q>)\<close>
      using m_entails_p sound_cons.entails_subsets m_in_n p_in_q q_enabled
      unfolding AF_entails_sound_def enabled_def enabled_projection_def enabled_set_def
      by (smt (z3) Un_iff consequence_relation.entails_subsets image_iff mem_Collect_eq
        sound_cons.ext_cons_rel subset_eq)
  qed
next
  fix \<M> \<N> \<C> \<M>' \<N>'
  assume
    entails_c: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F \<N> \<union> {\<C>}\<close> and
    c_entails: \<open>\<M>' \<union> {\<C>} \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close>
  show \<open>\<M> \<union> \<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N> \<union> \<N>'\<close>
    unfolding AF_entails_sound_def
  proof (intro allI impI)
    fix J
    assume enabled_n: \<open>enabled_set (\<N> \<union> \<N>') J\<close>
    {
      assume enabled_c: \<open>enabled_set {\<C>} J\<close>
      then have proj_enabled_c: \<open>{\<C>} proj\<^sub>J J = {F_of \<C>}\<close>
        unfolding enabled_projection_def using enabled_set_def by blast
      have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J))
        (Pos ` F_of ` (\<N> \<union> {\<C>}))\<close>
        using entails_c enabled_n enabled_c unfolding AF_entails_sound_def
        by (metis Un_iff enabled_set_def)
      then have cut_hyp1: \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J))
        (Pos ` F_of ` \<N> \<union> {Pos (F_of \<C>)})\<close>
        by force
      have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M>' \<union> {\<C>} proj\<^sub>J J))
        (Pos ` F_of ` \<N>')\<close>
        using c_entails enabled_n enabled_union2 unfolding AF_entails_sound_def by blast
      then have cut_hyp2: \<open>sound_cons.entails_neg
        (fml_ext ` total_strip J \<union> Pos ` (\<M>' proj\<^sub>J J) \<union> {Pos (F_of \<C>)}) (Pos ` F_of ` \<N>')\<close>
       by (metis Un_empty_right Un_insert_right distrib_proj image_insert proj_enabled_c)
       have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> \<union> \<M>' proj\<^sub>J J))
         (Pos ` F_of ` (\<N> \<union> \<N>'))\<close>
         using neg_ext_sound_cons_rel.entails_cut[OF cut_hyp1 cut_hyp2]  distrib_proj[of \<M> \<M>' J]
           image_Un by (smt (verit, del_insts) Un_commute Un_left_absorb Un_left_commute)
    }
    moreover
    {
      assume not_enabled_c: \<open>\<not> enabled_set {\<C>} J\<close>
      then have \<open>\<M>' \<union> {\<C>} proj\<^sub>J J = \<M>' proj\<^sub>J J\<close>
        unfolding enabled_projection_def enabled_set_def by auto
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M>' proj\<^sub>J J))
        (Pos ` F_of ` \<N>')\<close>
        using c_entails enabled_n enabled_union2 unfolding AF_entails_sound_def by metis
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> \<union> \<M>' proj\<^sub>J J))
        (Pos ` F_of ` (\<N> \<union> \<N>'))\<close>
        using neg_ext_sound_cons_rel.entails_subsets
        by (smt (verit, del_insts) Un_iff distrib_proj image_Un subsetI)
    }
    ultimately
    show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> \<union> \<M>' proj\<^sub>J J))
      (Pos ` F_of ` (\<N> \<union> \<N>'))\<close>
      by blast
  qed
next
  fix \<M> \<N>
  assume m_entails_n: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F \<N>\<close>
  consider (NotEnabled) \<open>\<forall>J. \<not> enabled_set \<N> J\<close> | (Enabled) \<open>\<exists>J. enabled_set \<N> J\<close> by blast
  then show \<open>\<exists>M' N'. M' \<subseteq> \<M> \<and> N' \<subseteq> \<N> \<and> finite M' \<and> finite N' \<and> M' \<Turnstile>s\<^sub>A\<^sub>F N'\<close>
  proof cases
    case NotEnabled
    then obtain \<N>' where N'_sub: \<open>\<N>' \<subseteq> \<N>\<close> and N'_fin: \<open>finite \<N>'\<close> and
      sub_not_enab: \<open>\<forall>J. \<not> enabled_set \<N>' J\<close>
      using never_enabled_finite_subset[of \<N>] by blast
    obtain \<M>' where \<open>\<M>' \<subseteq> \<M>\<close> and \<open>finite \<M>'\<close> and \<open>\<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close>
      using sub_not_enab unfolding AF_entails_sound_def by blast
    then show ?thesis using N'_sub N'_fin by blast
  next
    case Enabled
    then obtain J' where J'_is: \<open>enabled_set \<N> J'\<close> by auto
    {
      fix J
      assume enabled_N: \<open>enabled_set \<N> J\<close>
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J)) (Pos ` F_of ` \<N>)\<close>
        using m_entails_n unfolding AF_entails_sound_def by blast
      then obtain MJ' N' where mj_in: \<open>MJ' \<subseteq> fml_ext ` total_strip J \<union> Pos ` (\<M> proj\<^sub>J J)\<close> and
        np_proj: \<open>N' \<subseteq> Pos ` F_of ` \<N>\<close> and mjp_fin: \<open>finite MJ'\<close> and np_fin: \<open>finite N'\<close> and
        mjp_entails_np: \<open>sound_cons.entails_neg  MJ' N'\<close>
        using neg_ext_sound_cons_rel.entails_compactness by metis

      define M' where "M' = MJ' \<inter> Pos ` (\<M> proj\<^sub>J J)"
      then have mp_fin: \<open>finite M'\<close>
        using mjp_fin by auto
      have mp_with_f_of: \<open>\<forall>C \<in> M'. \<exists>\<C> \<in> \<M>. Pos (F_of \<C>) = C \<and> enabled \<C> J\<close>
        using mj_in unfolding enabled_projection_def M'_def by blast
      have \<open>\<exists>\<M>'\<subseteq> \<M>. finite \<M>' \<and> M' = Pos ` F_of ` \<M>' \<and> enabled_set \<M>' J\<close>
        using finite_subset_image_strong[of M' \<M> "(\<lambda>x. Pos (F_of x))" "\<lambda>x. enabled x J", OF mp_fin mp_with_f_of]
        unfolding enabled_set_def by blast
      then have ex_mp: \<open>\<exists>\<M>'\<subseteq>\<M>. finite \<M>' \<and> Pos ` (\<M>' proj\<^sub>J J) = M'\<close>
        unfolding enabled_projection_def enabled_set_def by blast
      then obtain \<M>' where mp_props: \<open>\<M>' \<subseteq> \<M>\<close> \<open>finite \<M>'\<close> \<open>Pos ` (\<M>' proj\<^sub>J J) = M'\<close> by auto

      let ?\<M>'_sel\<^sub>J = \<open>{\<C>. \<C> \<in> \<M>' \<and> enabled \<C> J}\<close>
      have \<open>?\<M>'_sel\<^sub>J \<subseteq> \<M>'\<close> by simp
      have \<open>finite (\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> ?\<M>'_sel\<^sub>J})\<close> (*{a. \<exists>\<C>\<in>\<N>'. a \<in> (fset (A_of \<C>)) }\<close>*)
        using mp_props by auto
      then obtain \<A>\<^sub>\<M>\<^sub>' where AM_is: \<open>fset \<A>\<^sub>\<M>\<^sub>' = (\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> ?\<M>'_sel\<^sub>J})\<close>
        using fin_set_fset by fastforce
      then have AM_in_J: \<open>fset \<A>\<^sub>\<M>\<^sub>' \<subseteq> total_strip J\<close>
        unfolding enabled_def by blast
      define J' where "J' = (MJ' \<inter> fml_ext ` total_strip J)"
      then have jp_fin: \<open>finite J'\<close>
        using mjp_fin by blast
      then obtain \<J>' where jp_props: "\<J>' \<subseteq> total_strip J" "fml_ext ` \<J>' = J'" "finite \<J>'"
        using J'_def by (metis Int_lower2 finite_subset_image)
      then obtain \<A>\<^sub>\<J>\<^sub>' where AJ_is: \<open>fset \<A>\<^sub>\<J>\<^sub>' = \<J>'\<close>
        using fin_set_fset by blast
      then have AJ_in_J: \<open>fset \<A>\<^sub>\<J>\<^sub>' \<subseteq> total_strip J\<close>
        using jp_props by auto
      define \<J>\<^sub>f' where \<open>\<J>\<^sub>f' = Pair bot (\<A>\<^sub>\<J>\<^sub>' |\<union>| \<A>\<^sub>\<M>\<^sub>')\<close>
      then have Jf_in: \<open>fset (A_of \<J>\<^sub>f') \<subseteq> total_strip J\<close> using AM_in_J AJ_in_J by simp
      have Jf_bot: \<open>F_of \<J>\<^sub>f' = bot\<close> using \<J>\<^sub>f'_def by auto
      have AM_in_Jf: \<open>\<forall>\<C>\<in>\<M>'. enabled \<C> J \<longrightarrow> fset (A_of \<C>) \<subseteq> fset (A_of \<J>\<^sub>f')\<close>
        using \<J>\<^sub>f'_def AM_is by auto

      have np_with_f_of: \<open>\<forall>C \<in> N'. \<exists>\<C> \<in> \<N>. Pos (F_of \<C>) = C\<close>
        using np_proj unfolding enabled_projection_def by blast
      have n_fin_subset: \<open>\<exists>\<N>'\<subseteq> \<N>. finite \<N>' \<and> N' = Pos ` F_of ` \<N>'\<close>
        using finite_subset_image[OF np_fin, of "\<lambda>x. Pos (F_of x)" \<N>] np_proj by auto
      then obtain \<N>' where np_props: \<open>\<N>' \<subseteq> \<N>\<close> \<open>finite \<N>'\<close> \<open>N' = Pos ` F_of ` \<N>'\<close>
        by blast
      have enab_np: \<open>enabled_set \<N>' J\<close>
        using enabled_N np_props unfolding enabled_set_def by blast

      have mjp_is: \<open>MJ' = Pos ` (\<M>' proj\<^sub>J J) \<union> fml_ext ` \<J>'\<close>
        using mj_in M'_def J'_def mp_props jp_props by auto
      have \<open>sound_cons.entails_neg ((Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` \<J>') (Pos ` F_of ` \<N>')\<close>
        using np_props mjp_entails_np unfolding mjp_is by blast
      then have fin_entail: \<open>sound_cons.entails_neg ((Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` (fset (A_of \<J>\<^sub>f'))) (Pos ` F_of ` \<N>')\<close>
        using neg_ext_sound_cons_rel.entails_subsets[of
          "(Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` \<J>'" "(Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` (fset (A_of \<J>\<^sub>f'))"
          "Pos ` F_of ` \<N>'" "Pos ` F_of ` \<N>'"] AJ_is unfolding \<J>\<^sub>f'_def by (simp add: image_Un subsetI)

      have \<open>\<exists>\<M>' \<N>' \<J>'. \<M>' \<subseteq> \<M> \<and> fset (A_of \<J>') \<subseteq> total_strip J \<and> \<N>' \<subseteq> \<N> \<and>
        finite \<M>'  \<and> finite \<N>' \<and> F_of \<J>' = bot \<and> enabled_set \<N>' J \<and>
        (\<forall>\<C>\<in>\<M>'. enabled \<C> J \<longrightarrow> fset (A_of \<C>) \<subseteq> fset (A_of \<J>')) \<and>
        sound_cons.entails_neg ((Pos ` (\<M>' proj\<^sub>J J))\<union> fml_ext ` (fset (A_of \<J>'))) (Pos ` F_of ` \<N>')\<close>
        using mp_props np_props fin_entail enab_np Jf_in Jf_bot \<J>\<^sub>f'_def AJ_is AM_is AM_in_Jf AF.sel(2) by blast
    }

          (* enabled_set (\<N>'_of J) J could be removed since it is a consequence of enabled_set \<N> J and the subset relation *)
    then obtain \<M>'_of \<N>'_of \<J>'_of where
      fsets_from_J: \<open>enabled_set \<N> J \<Longrightarrow> \<M>'_of J \<subseteq> \<M> \<and> fset (A_of (\<J>'_of J)) \<subseteq> total_strip J \<and> \<N>'_of J \<subseteq> \<N> \<and>
      finite (\<M>'_of J) \<and> finite (\<N>'_of J) \<and> F_of (\<J>'_of J) = bot \<and> enabled_set (\<N>'_of J) J \<and>
      (\<forall>\<C>\<in>(\<M>'_of J). enabled \<C> J \<longrightarrow> fset (A_of \<C>) \<subseteq> fset (A_of (\<J>'_of J))) \<and>
      sound_cons.entails_neg (Pos ` (\<M>'_of J proj\<^sub>J J) \<union> fml_ext ` (fset (A_of (\<J>'_of J)))) (Pos ` F_of ` \<N>'_of J) \<close> for J
      by metis

    let ?\<J>'_set = \<open>{\<J>'_of J |J. enabled_set \<N> J}\<close>
    have ex_Js: \<open>\<exists>Js. ?\<J>'_set = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J)\<close>
      by blast
    have proj_prop_J': \<open>proj\<^sub>\<bottom> ?\<J>'_set = ?\<J>'_set\<close>
      using fsets_from_J unfolding propositional_projection_def by blast
    let ?\<N>'_un = \<open>\<Union>{\<N>'_of J |J. enabled_set \<N> J}\<close>
    let ?\<M>'_un = \<open>\<Union>{{\<C>. \<C> \<in> \<M>'_of J \<and> enabled \<C> J} |J. enabled_set \<N> J}\<close>
 (*   have A_of_enabled: \<open>enabled_set \<N> J \<Longrightarrow> (fset (A_of (\<J>'_of J)) =
      \<Union>{fset (A_of \<C>) |\<C>. \<C> \<in> (\<N>'_of J) \<union> {\<C>. \<C> \<in> (\<M>'_of J) \<and> enabled \<C> J}})\<close> for J
      using fsets_from_J by presburger
    have A_of_eq: \<open>\<Union> (fset ` A_of ` ?\<J>'_set) =
      \<Union> (fset ` A_of ` ?\<N>'_un) \<union> \<Union> (fset ` A_of ` ?\<M>'_un)\<close>
    proof -
      have \<open>\<Union> (fset ` A_of ` ?\<J>'_set) = \<Union>{fset (A_of (\<J>'_of J)) |J. enabled_set \<N> J}\<close>
        by blast
      also have \<open>... = \<Union>{\<Union>{fset (A_of \<C>) |\<C>. \<C> \<in>
        (\<N>'_of J) \<union> {\<C>. \<C> \<in> (\<M>'_of J) \<and> enabled \<C> J}} |J. enabled_set \<N> J}\<close>
        using A_of_enabled by (metis (no_types, lifting))
      also have \<open>... = \<Union>(fset ` A_of ` (?\<N>'_un \<union> ?\<M>'_un))\<close> by blast
      finally show \<open>\<Union>(fset ` A_of ` ?\<J>'_set) =
        \<Union>(fset ` A_of ` ?\<N>'_un) \<union> \<Union> (fset ` A_of ` ?\<M>'_un)\<close>
        by simp
    qed *)

    have \<open>\<forall>J. \<not> (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 (\<E>_from \<N>))\<close>
      using equiv_\<E>_enabled_\<N> by blast
    then have not_enab_case: \<open>\<forall>J. \<not> (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<union> (\<E>_from \<N>))\<close>
      using supset_not_model_p2 Un_upper2 by blast
    have \<open>\<forall>J. enabled_set \<N> J \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set)\<close>
    proof clarsimp
      fix J
      assume
        enab_N_loc: \<open>enabled_set \<N> J\<close> and
        entails_J: \<open>(J \<Turnstile>\<^sub>p2 ?\<J>'_set)\<close>
      have A_ok: \<open>fset (A_of (\<J>'_of J)) \<subseteq> total_strip J\<close>
        using enab_N_loc fsets_from_J by force
      then have \<open>proj\<^sub>\<bottom> {\<J>'_of J} proj\<^sub>J J = {bot}\<close>
        using enab_N_loc fsets_from_J unfolding propositional_projection_def enabled_projection_def
        by (simp add: enabled_def)
      then have \<open>\<not> J \<Turnstile>\<^sub>p2 ?\<J>'_set\<close>
        using A_ok enab_N_loc unfolding propositional_model2_def enabled_def enabled_projection_def
          proj_prop_J' by auto
      then show False
        using entails_J by auto
    qed
    then have enab_case: \<open>\<forall>J. (enabled_set \<N> J) \<longrightarrow> \<not> (J \<Turnstile>\<^sub>p2 ?\<J>'_set \<union> (\<E>_from \<N>))\<close>
      using supset_not_model_p2 Un_upper2 by blast
    have \<open>\<forall>J. \<not> (J \<Turnstile>\<^sub>p2 (?\<J>'_set \<union> (\<E>_from \<N>)))\<close>
      using not_enab_case enab_case by blast

    then obtain \<S> where S_sub: \<open>\<S> \<subseteq> ?\<J>'_set \<union> (\<E>_from \<N>)\<close> and S_fin: \<open>finite \<S>\<close> and
      S_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>\<close>
      using compactness_AF_proj by meson
    have E_sat: \<open>sat (AF_proj_to_formula_set (\<E>_from \<N>))\<close>
      unfolding sat_def using J'_is equiv_\<E>_enabled_\<N> equiv_prop_entail2_sema2 by blast
    define \<S>\<^sub>\<J> where \<open>\<S>\<^sub>\<J> = \<S> \<inter> ?\<J>'_set\<close>
    define \<S>\<^sub>\<E> where \<open>\<S>\<^sub>\<E> = \<S> \<inter> (\<E>_from \<N>)\<close>
    define \<S>\<^sub>\<E>' where \<open>\<S>\<^sub>\<E>' = {\<C>. \<C> \<in> \<S>\<^sub>\<E> \<and> (to_V ` (fset (A_of \<C>))) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))}\<close>
    define \<S>' where \<open>\<S>' = \<S>\<^sub>\<J> \<union> \<S>\<^sub>\<E>'\<close>
    have proj_S':  \<open>proj\<^sub>\<bottom>  \<S>' = \<S>'\<close>
      using proj_prop_J' prop_proj_\<E>_from S_sub prop_proj_sub prop_proj_distrib
      unfolding \<S>'_def \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def
      by (smt (verit) Int_iff mem_Collect_eq subsetI)
    have S_is: \<open>\<S> = (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>') \<union> \<S>'\<close>
      using S_sub \<S>\<^sub>\<J>_def \<S>\<^sub>\<E>_def \<S>'_def \<S>\<^sub>\<E>'_def by blast
    have a_from_E_to_J: \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>') \<Longrightarrow> a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close> for a
    proof -
      fix a
      assume nega_in: \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>')\<close>
      then have \<open>to_V (neg a) \<in> to_V ` \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        unfolding \<S>\<^sub>\<E>'_def by blast
      then have a_or_nega_in: \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<or> neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        by (smt (verit) imageE neg.simps(1) neg.simps(2) to_V.elims)
      obtain \<C>1 where \<open>\<C>1 \<in> \<E>_from \<N>\<close> and \<open>neg a \<in> fset (A_of \<C>1)\<close>
        using nega_in unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def by blast
      then obtain \<C> where \<open>\<C> \<in> \<N>\<close> and \<open>a \<in> fset (A_of \<C>)\<close>
        unfolding \<E>_from_def by (smt (verit) AF.sel(2) bot_fset.rep_eq empty_iff finsert.rep_eq
          insert_iff mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims)
      then have in_N_in_J: \<open>\<forall>J. (enabled_set \<N> J \<longrightarrow> a \<in>\<^sub>t J)\<close>
        using in_total_to_strip unfolding enabled_set_def enabled_def by blast
      have \<open>b \<in>  \<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<Longrightarrow> (\<exists>J. enabled_set \<N> J \<and> b \<in>\<^sub>t J)\<close> for b
      proof clarsimp
        fix \<C>2
        assume C2_in: \<open>\<C>2 \<in> \<S>\<^sub>\<J>\<close> and
          b_in: \<open>b \<in> fset (A_of \<C>2)\<close>
        obtain J where enab_J: \<open>enabled_set \<N> J\<close> and \<open>\<C>2 = \<J>'_of J\<close>
          using C2_in unfolding \<S>\<^sub>\<J>_def by blast
        then have \<open>b \<in> total_strip J\<close>
          using b_in fsets_from_J by (meson basic_trans_rules(31))
        then show \<open>\<exists>J. enabled_set \<N> J \<and> b \<in> total_strip J\<close>
          using enab_J by blast
      qed
      then have \<open>\<not>  neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        using in_N_in_J by fastforce
      then show \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
        using a_or_nega_in by blast
    qed
    have empty_inter_in_S: \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') = {}\<close>
    proof (rule ccontr)
      assume contra: \<open>to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>')) \<inter> to_V ` \<Union> (fset ` A_of ` \<S>') \<noteq> {}\<close>
      then obtain v where v_in1: \<open>v \<in> to_V ` \<Union> (fset ` A_of ` (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
        and v_in2: \<open>v \<in> to_V ` \<Union> (fset ` A_of ` \<S>')\<close> by blast
      obtain \<C> where C_in: \<open>\<C> \<in> \<S>\<^sub>\<E> - \<S>\<^sub>\<E>'\<close> and v_in_C: \<open>v \<in> to_V ` (fset (A_of \<C>))\<close>
        using v_in1 by blast
      obtain a where C_is1: \<open>\<C> = Pair bot {|a|}\<close>
        using C_in unfolding \<S>\<^sub>\<E>_def \<E>_from_def by blast
      then have v_is: \<open>v = to_V a\<close>
        using v_in_C by simp
      obtain \<C>' where C'_in: \<open>\<C>' \<in> \<S>'\<close> and v_in_C': \<open>v \<in> to_V ` (fset (A_of \<C>'))\<close>
        using v_in2 by blast
      then obtain a' where v_is': \<open>v = to_V a'\<close> and a'_in: \<open>a' \<in> fset (A_of \<C>')\<close>
        by blast
      consider (J) \<open>\<C>' \<in> \<S>\<^sub>\<J>\<close> | (E') \<open>\<C>' \<in> \<S>\<^sub>\<E>'\<close>
        using C'_in \<S>'_def by blast
      then show False
      proof cases
        case J
        then have \<open>to_V ` (fset (A_of \<C>')) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))\<close>
          by blast
        then have \<open>to_V ` (fset (A_of \<C>)) \<subseteq> (to_V ` \<Union> (fset ` A_of ` \<S>\<^sub>\<J>))\<close>
          using C_is1 v_in_C' v_is by auto
        then have \<open>\<C> \<in> \<S>\<^sub>\<E>'\<close>
          unfolding \<S>\<^sub>\<E>'_def using C_in by blast
        then show False
          using C_in by blast
      next
        case E'
        then consider (a) \<open>\<C>' = Pair bot {|a|}\<close> | (nega) \<open>\<C>' = Pair bot {|neg a|}\<close>
          unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def using v_in_C' v_is
            AF.sel(2) IntE empty_iff fset_simps(1) fset_simps(2) image_iff insert_iff
            mem_Collect_eq neg.simps(1) neg.simps(2) to_V.elims
          by (smt (verit, del_insts))
          (* by (smt (verit)) (* Solver verit: Solver terminated abnormally with error code 1 *)*)
        then show False
        proof cases
          case a
          then show ?thesis
            using E' a_in_\<E> Enabled equiv_\<E>_enabled_\<N> C_in C_is1 unfolding \<S>\<^sub>\<E>_def \<S>\<^sub>\<E>'_def
            by blast
        next
          case nega
          have \<open>\<C>' \<in> \<E>_from \<N>\<close>
            using E' unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by auto
          moreover have \<open>\<C> \<in> \<E>_from \<N>\<close>
            using C_in unfolding \<S>\<^sub>\<E>_def by auto
          find_theorems \<E>_from
          ultimately show ?thesis
            using a_in_\<E> nega C_is1 Enabled equiv_\<E>_enabled_\<N> by blast
        qed
      qed
    qed
    then have empty_inter: \<open>\<Union> (atoms ` (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))) \<inter>
      \<Union> (atoms ` (AF_proj_to_formula_set \<S>')) = {}\<close>
      using atoms_simp proj_S' prop_proj_distrib prop_proj_sub
      by (smt (verit, ccfv_threshold) S_sub Un_subset_iff \<open>\<S> = \<S>\<^sub>\<E> - \<S>\<^sub>\<E>' \<union> \<S>'\<close> proj_prop_J'
        prop_proj_\<E>_from)
    have sat_rest: \<open>sat (AF_proj_to_formula_set (\<S>\<^sub>\<E> - \<S>\<^sub>\<E>'))\<close>
      using E_sat unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def AF_proj_to_formula_set_def
        propositional_projection_def sat_def by blast
    have S'_unsat: \<open>\<forall>J. \<not> J \<Turnstile>\<^sub>p2 \<S>'\<close>
      using unsat_AF_simp[OF _ sat_rest empty_inter] S_unsat equiv_prop_entail2_sema2 S_is
        val_from_interp unfolding sat_def by metis
    have ex_fin_Js: \<open>\<exists>Js. \<S>\<^sub>\<J> = \<J>'_of ` Js \<and> (\<forall>J\<in>Js. enabled_set \<N> J) \<and> finite Js\<close>
      using finite_subset_with_prop[OF ex_Js S_fin \<S>\<^sub>\<J>_def] .
    then obtain Js where Js_fin: \<open>finite Js\<close> and Js_enab: \<open>\<forall>J\<in>Js. enabled_set \<N> J\<close> and
      Js_is: \<open>\<J>'_of ` Js = \<S>\<^sub>\<J>\<close>
      by blast

    have fin_inter: \<open>finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<inter> \<Union>(fset ` A_of ` \<N>))\<close>
    proof
      have \<open>finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))\<close>
        unfolding \<S>\<^sub>\<J>_def using S_fin image_Int_subset by simp
      then show \<open>(finite (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))) \<or> (finite (\<Union> (fset ` A_of ` \<N>)))\<close>
        by auto
    qed
    have \<open>\<forall>a\<in>(\<Union>(fset ` A_of ` \<N>)). \<exists>\<C>\<in>\<N>. a \<in> fset (A_of \<C>)\<close>
      by blast
    then obtain f where f_def: \<open>\<forall>a\<in>(\<Union>(fset ` A_of ` \<N>)). f a \<in> \<N> \<and> a \<in> fset (A_of (f a))\<close>
      by metis
    define \<N>\<^sub>\<J> where \<open>\<N>\<^sub>\<J> = (f ` (\<Union>(fset ` A_of ` \<S>\<^sub>\<J>) \<inter> \<Union>(fset ` A_of ` \<N>)))\<close>
    have nj_fin: \<open>finite \<N>\<^sub>\<J>\<close>
      unfolding \<N>\<^sub>\<J>_def using fin_inter by blast
    have nj_sub: \<open>\<N>\<^sub>\<J> \<subseteq> \<N>\<close>
      unfolding \<N>\<^sub>\<J>_def using f_def by blast
    have nj_as: \<open>(\<forall>a\<in>(\<Union>(fset ` A_of ` \<S>\<^sub>\<J>))\<inter>(\<Union>(fset ` A_of ` \<N>)).
      a \<in> \<Union>(fset ` A_of ` \<N>\<^sub>\<J>))\<close>
      unfolding \<N>\<^sub>\<J>_def using f_def by fast

    define \<M>' where \<open>\<M>' = \<Union>{\<M>'_of J |J. J \<in> Js}\<close>
    define \<N>' where  \<open>\<N>' = \<Union>{\<N>'_of J |J. J \<in> Js} \<union> \<N>\<^sub>\<J>\<close>
    then have \<open>\<M>' \<subseteq> \<M>\<close>
      unfolding \<M>'_def using fsets_from_J Js_enab by fast
    moreover have \<open>\<N>' \<subseteq> \<N>\<close>
      unfolding \<N>'_def using fsets_from_J Js_enab nj_sub by fast
    moreover have \<open>finite \<M>'\<close>
      unfolding \<M>'_def using fsets_from_J Js_fin Js_enab by auto
    moreover have \<open>finite \<N>'\<close>
      unfolding \<N>'_def using fsets_from_J Js_fin Js_enab nj_fin by auto
    moreover have \<open>\<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close> unfolding AF_entails_sound_def
    proof clarsimp
      fix J
      assume enab_N': \<open>enabled_set \<N>' J\<close>
      then have \<open>J \<Turnstile>\<^sub>p2 \<E>_from \<N>'\<close>
        using equiv_\<E>_enabled_\<N> by auto
      moreover have \<open>\<S>\<^sub>\<E>' \<subseteq> \<E>_from \<N>'\<close>
        proof
          fix \<C>
          assume C_in: \<open>\<C> \<in> \<S>\<^sub>\<E>'\<close>
          then obtain a where C_is: \<open>\<C> = Pair bot {|neg a|}\<close>
            unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def \<E>_from_def by blast
          then have \<open>neg a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<E>')\<close>
            using C_in using image_iff by fastforce
          then have a_in_SJ: \<open>a \<in> \<Union>(fset ` A_of ` \<S>\<^sub>\<J>)\<close>
            using a_from_E_to_J by presburger
          have \<open>\<exists>\<C>'\<in>\<N>. a \<in> fset (A_of \<C>')\<close>
            using C_is C_in unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def by (smt (verit, ccfv_threshold)
              AF.sel(2) IntE J'_is \<E>_from_def a_in_\<E> bot_fset.rep_eq empty_iff equiv_\<E>_enabled_\<N>
              finsert.rep_eq insert_iff mem_Collect_eq to_V.elims to_V_neg)
          then have \<open>a \<in> \<Union>(fset ` A_of ` \<N>)\<close>
            by blast
          then have \<open>a \<in> \<Union>(fset ` A_of ` \<N>')\<close>
            using nj_as a_in_SJ unfolding \<N>'_def by simp
          then show \<open>\<C> \<in> \<E>_from \<N>'\<close>
            using C_is unfolding \<E>_from_def by blast
        qed
      ultimately have \<open>J \<Turnstile>\<^sub>p2 \<S>\<^sub>\<E>'\<close>
        unfolding \<S>\<^sub>\<E>'_def \<S>\<^sub>\<E>_def using subset_model_p2 by (metis (no_types, lifting))
      then have \<open>\<not> J \<Turnstile>\<^sub>p2 \<S>\<^sub>\<J>\<close>
        using subset_not_model S'_unsat unfolding \<S>'_def by blast
      then have  \<open>\<exists>J'\<in>Js. fset (A_of (\<J>'_of J')) \<subseteq> total_strip J\<close>
        unfolding propositional_model2_def \<S>\<^sub>\<J>_def propositional_projection_def
          enabled_projection_def using Js_is
        by (smt (verit) Collect_cong Set.empty_def \<S>\<^sub>\<J>_def enabled_def image_iff mem_Collect_eq)
      then obtain J' where J'_in: \<open>J' \<in> Js\<close> and A_of_J'_in: \<open>fset (A_of (\<J>'_of J')) \<subseteq> total_strip J\<close>
        by blast
      then have enab_nj': \<open>enabled_set \<N> J'\<close>
        using Js_enab by blast
      then have \<open>sound_cons.entails_neg (Pos ` (\<M>'_of J' proj\<^sub>J J') \<union>
        fml_ext ` (fset (A_of (\<J>'_of J')))) (Pos ` F_of ` \<N>'_of J')\<close>
        using fsets_from_J by auto
      moreover have \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close>
      proof -
        have \<open>\<C> \<in> \<M>'_of J' \<Longrightarrow> enabled \<C> J' \<Longrightarrow> enabled \<C> J\<close> for \<C>
        proof -
          assume C_in: \<open>\<C> \<in> \<M>'_of J'\<close> and
            \<open>enabled \<C> J'\<close>
          then have \<open>fset (A_of \<C>) \<subseteq> fset (A_of (\<J>'_of J'))\<close>
            using fsets_from_J[OF enab_nj'] by blast
          then show \<open>enabled \<C> J\<close>
            using A_of_J'_in unfolding enabled_def by auto
        qed
        then have \<open>(\<C> \<in> \<M>'_of J' \<and> enabled \<C> J') \<Longrightarrow> (\<C> \<in> \<M>'_of J' \<and> enabled \<C> J)\<close> for \<C>
          by (smt (verit, ccfv_threshold))
        then have \<open>{\<C>. \<C> \<in> \<M>'_of J' \<and> enabled \<C> J'} \<subseteq> {\<C>. \<C> \<in> \<M>'_of J' \<and> enabled \<C> J}\<close>
          by blast
        then show \<open>(\<M>'_of J') proj\<^sub>J J' \<subseteq> (\<M>'_of J') proj\<^sub>J J\<close>
          unfolding enabled_projection_def by blast
      qed
      ultimately have entails_one:  \<open>sound_cons.entails_neg
        (Pos ` (\<M>'_of J' proj\<^sub>J J) \<union> fml_ext ` (fset (A_of (\<J>'_of J')))) (Pos ` F_of ` \<N>'_of J')\<close>
        using sound_cons.entails_subsets
        by (smt (verit, ccfv_SIG) Un_absorb1 Un_assoc Un_left_commute image_Un
          neg_ext_sound_cons_rel.entails_subsets subset_refl sup.cobounded1)
      have subs_MJ: \<open>Pos ` (\<M>'_of J' proj\<^sub>J J) \<union>
        fml_ext ` (fset (A_of (\<J>'_of J'))) \<subseteq> Pos ` (\<M>' proj\<^sub>J J) \<union> fml_ext ` (total_strip J)\<close>
        using J'_in A_of_J'_in using enabled_projection_def unfolding \<M>'_def by auto
      have subs_N: \<open>Pos ` F_of ` (\<N>'_of J') \<subseteq> Pos ` F_of ` \<N>'\<close>
        using J'_in unfolding \<N>'_def by blast
      show \<open>sound_cons.entails_neg (fml_ext ` total_strip J \<union> Pos ` (\<M>' proj\<^sub>J J))
        (Pos ` F_of ` \<N>')\<close>
        using neg_ext_sound_cons_rel.entails_subsets[OF subs_MJ subs_N entails_one]
        by (simp add: Un_commute)
    qed

    ultimately
    show \<open>\<exists>\<M>' \<N>'. \<M>' \<subseteq> \<M> \<and> \<N>' \<subseteq> \<N> \<and> finite \<M>' \<and> finite \<N>' \<and> \<M>' \<Turnstile>s\<^sub>A\<^sub>F \<N>'\<close>
      by blast
  qed
qed
















  
subsection \<open>The inference rules\<close>

text \<open>We define SInf, our inference system comprising two rules:\<close>

(* The basic SInf inference system, with the two basic rules BASE and UNSAT.
 *
 * \<open>S \<iota>\<close> means that \<open>\<iota>\<close> is an inference rule of the system S *)

abbreviation base_pre :: \<open>('f, 'v) AF list \<Rightarrow> 'f \<Rightarrow> bool\<close> where
  \<open>base_pre \<N> D \<equiv> Infer (map F_of \<N>) D \<in> Inf\<close>

abbreviation base_inf :: \<open>('f, 'v) AF list \<Rightarrow> 'f \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>base_inf \<N> D \<equiv> Infer \<N> (Pair D (ffUnion (fset_of_list (map A_of \<N>))))\<close>

abbreviation unsat_pre :: \<open>('f, 'v) AF list \<Rightarrow> bool\<close> where
  \<open>unsat_pre \<N> \<equiv> (\<forall> x \<in> set \<N>. F_of x = bot) \<and> propositionally_unsatisfiable (set \<N>) \<and> \<N> \<noteq> []\<close>

abbreviation unsat_inf :: \<open>('f, 'v) AF list \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>unsat_inf \<N> \<equiv> Infer \<N> (to_AF bot)\<close>

inductive Splitting_rules :: \<open>('f, 'v) AF inference \<Rightarrow> bool\<close> where
  base: \<open>base_pre \<N> D \<Longrightarrow> Splitting_rules (base_inf \<N> D)\<close>
| unsat: \<open>unsat_pre \<N> \<Longrightarrow> Splitting_rules (unsat_inf \<N>)\<close>
     (* NOTE: can we have that \<open>\<N>\<close> is \<open>[]\<close>? *)
(* | strong_unsat: \<open>\<lbrakk> \<forall> x \<in> set \<N>. propositional_clause x; set \<N> \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot} \<rbrakk> \<Longrightarrow> S (Infer \<N> (to_AF bot))\<close>
| approx: \<open>\<lbrakk> a \<in> asn (to_F \<C>) \<rbrakk> \<Longrightarrow> S (Infer [\<C>] (Pair bot (finsert (neg a) (to_A \<C>))))\<close>
| tauto: \<open>\<lbrakk> \<not> propositional_clause \<C>; {} \<Turnstile>s\<^sub>A\<^sub>F {\<C>} \<rbrakk> \<Longrightarrow> S (Infer [] \<C>)\<close> *)

(* All the simplification rules of the SInf inference system: SPLIT, COLLECT and TRIM. *)
(* inductive S_simps :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close>
  (infix \<open>\<equiv>\<^sub>S\<close> 50) where
  collect: \<open>\<lbrakk> \<not> propositional_clause \<C>; \<N> \<Turnstile>s\<^sub>A\<^sub>F {Pair bot (to_A \<C>)} \<rbrakk> \<Longrightarrow> \<N> \<union> {\<C>} \<equiv>\<^sub>S \<N>\<close> |
  trim: \<open>\<lbrakk> \<not> propositional_clause \<C>; to_A \<C> = A |\<union>| B; \<N> \<union> {Pair bot A} \<Turnstile>s\<^sub>A\<^sub>F {Pair bot B} \<rbrakk> \<Longrightarrow> \<N> \<union> {\<C>} \<equiv>\<^sub>S \<N> \<union> {Pair (to_F \<C>) B}\<close> |
        (* Should we require here that A and B be non empty? It doesn't really make sense to apply those rules
        * if this is not the case, though it does not cause any error... *)
  split: \<open>\<lbrakk> \<not> propositional_clause \<C>; split C Cs \<rbrakk> \<Longrightarrow> \<N> \<union> {\<C>} \<equiv>\<^sub>S \<N> \<union> {Pair bot (Abs_fset (neg ` snd ` Cs))} \<union> {Pair C {|neg a|} | C a. (C, a) \<in> Cs}\<close>

inductive_set SInf :: \<open>('f, 'v) AF inference set\<close> where
  infer: \<open>S I \<Longrightarrow> I \<in> SInf\<close> |
  simp: \<open>\<lbrakk> set P \<equiv>\<^sub>S set P'; Infer P C \<in> SInf \<rbrakk> \<Longrightarrow> Infer P' C \<in> SInf\<close> *)

abbreviation SInf :: \<open>('f, 'v) AF inference set\<close> where
  \<open>SInf \<equiv> {I. Splitting_rules I}\<close>

interpretation SInf_inf_system: inference_system SInf .

lemma F_of_to_AF [simp]: \<open>F_of (to_AF \<C>) = \<C>\<close>
  unfolding to_AF_def
  by auto

lemma A_of_to_AF [simp]: \<open>A_of (to_AF \<C>) = {||}\<close>
  unfolding to_AF_def
  by auto

lemma F_of_propositional_clauses [simp]: \<open>(\<forall> x \<in> set \<N>. F_of x = bot) \<Longrightarrow> map F_of \<N> = map (\<lambda> _. bot) \<N>\<close>
  using map_eq_conv
  by blast

lemma set_map_is_image: \<open>set (map f l) = f ` set l\<close>
  by fastforce

(* Report lemma 13 1/2 *)
lemma SInf_commutes_Inf1: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J \<subseteq> Inf_from (\<N> proj\<^sub>J J)\<close>
proof (intro subsetI)
  fix \<iota>\<^sub>S
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         \<iota>\<^sub>S_is_inf: \<open>\<iota>\<^sub>S \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>

  have no_enabled_prop_clause_in_\<N>: \<open>\<forall> \<C> \<in> \<N>. enabled \<C> J \<longrightarrow> F_of \<C> \<noteq> bot\<close>
    using bot_not_in_proj
    unfolding enabled_projection_def
    by blast

  obtain \<iota>\<^sub>F where \<iota>\<^sub>S_is: \<open>\<iota>\<^sub>S = \<iota>F_of \<iota>\<^sub>F\<close> and
                 \<iota>\<^sub>F_is_inf: \<open>\<iota>\<^sub>F \<in> inference_system.Inf_from SInf \<N>\<close> and
                 \<iota>\<^sub>F_is_enabled: \<open>enabled_inf \<iota>\<^sub>F J\<close>
    using \<iota>\<^sub>S_is_inf enabled_projection_Inf_def
    by auto
  then have \<iota>\<^sub>F_in_S: \<open>Splitting_rules \<iota>\<^sub>F\<close>
    by (simp add: inference_system.Inf_from_def)
  moreover have prems_of_\<iota>\<^sub>F_subset_\<N>: \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N>\<close>
    using \<iota>\<^sub>F_is_inf
    by (simp add: inference_system.Inf_from_def)
  moreover have \<open>\<iota>F_of \<iota>\<^sub>F \<in> Inf\<close>
    unfolding \<iota>F_of_def
  proof (cases \<iota>\<^sub>F rule: Splitting_rules.cases)
    (* NOTE: using \<open>case ...\<close> does not work here because of the first case.
     * May this come from the definition of \<open>S\<close>? *)
    show \<open>Splitting_rules \<iota>\<^sub>F\<close>
      by (simp add: \<iota>\<^sub>F_in_S)
  next
    fix \<N> D
    assume \<iota>\<^sub>F_def: \<open>\<iota>\<^sub>F = base_inf \<N> D\<close>
       and \<open>base_pre \<N> D\<close>
    then show \<open>base_pre (prems_of \<iota>\<^sub>F) (F_of (concl_of \<iota>\<^sub>F))\<close>
      by auto
  next
    fix \<N> D
    assume \<iota>\<^sub>F_def: \<open>\<iota>\<^sub>F = unsat_inf \<N>\<close> and
           pre_cond: \<open>unsat_pre \<N>\<close>
    moreover have \<open>enabled_inf \<iota>\<^sub>F J\<close>
      using \<iota>\<^sub>F_is_enabled
      by fastforce
    then have \<open>\<forall> \<C> \<in> set \<N>. F_of \<C> \<noteq> bot\<close>
      by (metis \<iota>\<^sub>F_def enabled_inf_def inference.sel(1) no_enabled_prop_clause_in_\<N> prems_of_\<iota>\<^sub>F_subset_\<N> subset_iff)
    then have \<open>False\<close>
      using pre_cond
      by fastforce
    ultimately show \<open>base_pre (prems_of \<iota>\<^sub>F) (F_of (concl_of \<iota>\<^sub>F))\<close>
      by blast
  qed
  moreover have \<open>set (prems_of (\<iota>F_of \<iota>\<^sub>F)) \<subseteq> \<N> proj\<^sub>J J\<close>
    using \<iota>\<^sub>F_is_enabled prems_of_\<iota>\<^sub>F_subset_\<N>
    by (auto simp add: enabled_inf_def enabled_projection_def \<iota>F_of_def)
  ultimately have \<open>\<iota>F_of \<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: Inf_from_def)
  then show \<open>\<iota>\<^sub>S \<in> Inf_from (\<N> proj\<^sub>J J)\<close>
    by (simp add: \<iota>\<^sub>S_is)
qed

lemma map2_first_is_first [simp]: \<open>length x = length y \<Longrightarrow> map2 (\<lambda>x y. x) x y = x\<close>
  by (metis fst_def map_eq_conv map_fst_zip)

lemma map2_second_is_second [simp]: \<open>length A = length B \<Longrightarrow> map2 (\<lambda> x y. y) A B = B\<close>
  by (metis map_eq_conv map_snd_zip snd_def)

lemma fimage_snd_zip_is_snd [simp]: \<open>length x = length y \<Longrightarrow> (\<lambda>(x, y). y) |`| fset_of_list (zip x y) = fset_of_list y\<close>
proof -
  assume length_x_eq_length_y: \<open>length x = length y\<close>
  have \<open>(\<lambda>(x, y). y) |`| fset_of_list A = fset_of_list (map (\<lambda>(x, y). y) A)\<close> for A
    by auto
  then show ?thesis
    using length_x_eq_length_y
    by (smt (verit, ccfv_SIG) cond_case_prod_eta map_snd_zip snd_conv)
qed

lemma F_of_Pair [simp]: \<open>F_of \<circ> (\<lambda>(x, y). Pair x y) = (\<lambda>(x, y). x)\<close>
  by (smt (verit, ccfv_SIG) AF.sel(1) comp_apply cond_case_prod_eta old.prod.case)

lemma A_of_Pair [simp]: \<open>A_of \<circ> (\<lambda>(x, y). Pair x y) = (\<lambda>(x, y). y)\<close>
  by fastforce

lemma list_all_exists_is_exists_list_all2:
  assumes \<open>list_all (\<lambda> x. \<exists> y. P x y) xs\<close>
  shows \<open>\<exists> ys. list_all2 P xs ys\<close>
  using assms
  by (induct xs, auto)

(* Report lemma 13 2/2 *)
lemma SInf_commutes_Inf2: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> Inf_from (\<N> proj\<^sub>J J) \<subseteq> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
proof (intro subsetI)
  fix \<iota>\<^sub>F
  assume bot_not_in_proj: \<open>bot \<notin> \<N> proj\<^sub>J J\<close> and
         \<iota>\<^sub>F_in_inf: \<open>\<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J J)\<close>

  have \<iota>\<^sub>F_is_Inf: \<open>\<iota>\<^sub>F \<in> Inf\<close>
    using Inf_if_Inf_from \<iota>\<^sub>F_in_inf
    by blast
  have \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N> proj\<^sub>J J\<close>
    using Inf_from_def \<iota>\<^sub>F_in_inf
    by blast
  then have \<open>\<forall> \<C> \<in> set (prems_of \<iota>\<^sub>F). \<exists> A. Pair \<C> A \<in> \<N> \<and> enabled (Pair \<C> A) J\<close>
    by (smt (verit, ccfv_SIG) AF.collapse enabled_projection_def mem_Collect_eq subsetD)
  then have \<open>list_all (\<lambda> \<C>. \<exists> A. Pair \<C> A \<in> \<N> \<and> enabled (Pair \<C> A) J) (prems_of \<iota>\<^sub>F)\<close>
    using Ball_set
    by blast
(*  then have \<open>\<exists> As. list_all2 (\<lambda> C A. Pair C A \<in> \<N> \<and> enabled (Pair C A) J) (prems_of \<iota>\<^sub>F) As\<close>
     by (simp add: list_all_exists_is_exists_list_all2) *)
(*  then have \<open>\<exists> As. length (prems_of \<iota>\<^sub>F) = length As \<and> (\<forall> (C, A) \<in> set (zip (prems_of \<iota>\<^sub>F) As). Pair C A \<in> \<N> \<and> enabled (Pair C A) J)\<close>
    by (meson list_all2_iff) *)
  then obtain As where length_As_is_length_prems_\<iota>\<^sub>F: \<open>length (prems_of \<iota>\<^sub>F) = length As\<close> and
                       As_def: \<open>\<forall> (C, A) \<in> set (zip (prems_of \<iota>\<^sub>F) As). Pair C A \<in> \<N> \<and> enabled (Pair C A) J\<close>
    by (smt (verit, del_insts) Ball_set_list_all list_all2_iff list_all_exists_is_exists_list_all2)
  define \<iota>\<^sub>S where
    \<open>\<iota>\<^sub>S \<equiv> Infer [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ] (Pair (concl_of \<iota>\<^sub>F) (ffUnion (fset_of_list As)))\<close>
  have \<iota>\<^sub>F_is_Inf2: \<open>Infer (map F_of [ Pair \<C> A. (\<C>, A) \<leftarrow> zip (prems_of \<iota>\<^sub>F) As ]) (concl_of \<iota>\<^sub>F) \<in> Inf\<close>
    using length_As_is_length_prems_\<iota>\<^sub>F
    by (auto simp add: \<iota>\<^sub>F_is_Inf)
  then have \<iota>\<^sub>S_is_SInf: \<open>\<iota>\<^sub>S \<in> SInf\<close>
    using Splitting_rules.base[OF \<iota>\<^sub>F_is_Inf2] length_As_is_length_prems_\<iota>\<^sub>F
    unfolding \<iota>\<^sub>S_def
    by auto
  moreover have \<open>set (prems_of \<iota>\<^sub>S) \<subseteq> \<N>\<close>
    unfolding \<iota>\<^sub>S_def
    using As_def
    by auto
  then have \<open>\<iota>\<^sub>S \<in> inference_system.Inf_from SInf \<N>\<close>
    using inference_system.Inf_from_def \<iota>\<^sub>S_is_SInf
    by blast
  moreover have \<open>\<iota>F_of \<iota>\<^sub>S = \<iota>\<^sub>F\<close>
    unfolding \<iota>\<^sub>S_def \<iota>F_of_def
    by (simp add: length_As_is_length_prems_\<iota>\<^sub>F)
  moreover have \<open>enabled_inf \<iota>\<^sub>S J\<close>
    unfolding enabled_inf_def \<iota>\<^sub>S_def
    using As_def
    by auto
  ultimately have \<open>\<exists> \<iota>'. \<iota>\<^sub>F = \<iota>F_of \<iota>' \<and> \<iota>' \<in> inference_system.Inf_from SInf \<N> \<and> enabled_inf \<iota>' J\<close>
    by blast
  then show \<open>\<iota>\<^sub>F \<in> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J\<close>
    unfolding enabled_projection_Inf_def
    by simp
qed

(* Report lemma 13 *)
lemma SInf_commutes_Inf: \<open>bot \<notin> \<N> proj\<^sub>J J \<Longrightarrow> (inference_system.Inf_from SInf \<N>) \<iota>proj\<^sub>J J = Inf_from (\<N> proj\<^sub>J J)\<close>
  using SInf_commutes_Inf1 SInf_commutes_Inf2
  by blast

lemma if_in_ffUnion_then_in_subset: \<open>x |\<in>| ffUnion A \<Longrightarrow> \<exists> a. a |\<in>| A \<and> x |\<in>| a\<close>
  by (induct \<open>A\<close> rule: fset_induct, fastforce+)

lemma fset_ffUnion_subset_iff_all_fsets_subset: \<open>fset (ffUnion A) \<subseteq> B \<longleftrightarrow> fBall A (\<lambda> x. fset x \<subseteq> B)\<close>
proof (intro fBallI subsetI iffI)
  fix a x
  assume ffUnion_A_subset_B: \<open>fset (ffUnion A) \<subseteq> B\<close> and
         a_in_A: \<open>a |\<in>| A\<close> and
         x_in_fset_a: \<open>x \<in> fset a\<close>
  then have \<open>x |\<in>| a\<close>
    by (simp add: fmember.rep_eq)
  then have \<open>x |\<in>| ffUnion A\<close>
    by (metis a_in_A ffunion_insert funion_iff set_finsert)
  then show \<open>x \<in> B\<close>
    by (meson ffUnion_A_subset_B fmember.rep_eq subsetD)
next
  fix x
  assume all_in_A_subset_B: \<open>fBall A (\<lambda> x. fset x \<subseteq> B)\<close> and
         \<open>x \<in> fset (ffUnion A)\<close>
  then have \<open>x |\<in>| ffUnion A\<close>
    by (simp add: fmember.rep_eq)
  then obtain a where \<open>a |\<in>| A\<close> and
                      x_in_a: \<open>x |\<in>| a\<close>
    by (meson if_in_ffUnion_then_in_subset)
  then have \<open>fset a \<subseteq> B\<close>
    using all_in_A_subset_B
    by blast
  then show \<open>x \<in> B\<close>
    by (meson fmember.rep_eq subsetD x_in_a)
qed

lemma fBall_fset_of_list_iff_Ball_set: \<open>fBall (fset_of_list A) P \<longleftrightarrow> Ball (set A) P\<close>
  by (simp add: fBall.rep_eq fset_of_list.rep_eq)



(* Report theorem 14 *)
theorem SInf_sound_wrt_entails_sound: \<open>\<iota> \<in> SInf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
proof -
  assume \<open>\<iota> \<in> SInf\<close>
  then have \<open>Splitting_rules \<iota>\<close>
    by simp
  then show \<open>set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
  proof (cases \<iota> rule: Splitting_rules.cases)
    case (base \<N> D)
    assume \<open>base_pre \<N> D\<close>
    then have inf_is_sound: \<open>set (map F_of \<N>) \<Turnstile>s {D}\<close>
      using sound
      by fastforce
    then show ?thesis
      unfolding AF_entails_sound_def sound_cons.entails_neg_def
    proof (intro allI impI)
      fix J
      assume \<open>enabled_set {concl_of \<iota>} J\<close>
      then have Pair_D_A_of_\<N>_is_enabled: \<open>enabled_set {concl_of \<iota>} J\<close>
        using base
        by simp
      then have \<open>F_of ` {concl_of \<iota>} = {D}\<close>
        using base
        by simp
      moreover have \<open>fset (ffUnion (fset_of_list (map A_of \<N>))) \<subseteq> total_strip J\<close>
        using Pair_D_A_of_\<N>_is_enabled
        unfolding enabled_set_def enabled_def
        by (simp add: local.base(1))
      then have \<open>fBall (fset_of_list (map A_of \<N>)) (\<lambda> As. fset As \<subseteq> total_strip J)\<close>
        using fset_ffUnion_subset_iff_all_fsets_subset
        by fast
      then have \<open>\<forall> As \<in> set (map A_of \<N>). fset As \<subseteq> total_strip J\<close>
        by (meson fBall_fset_of_list_iff_Ball_set)
      then have \<open>\<forall> \<C> \<in> set \<N>. enabled \<C> J\<close>
        unfolding enabled_def
        by simp
      then have \<open>set \<N> proj\<^sub>J J = F_of ` set \<N>\<close>
        unfolding enabled_projection_def
        by auto
      moreover have \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` F_of ` set \<N>} \<Turnstile>s {D}\<close>
        using inf_is_sound
        by (smt (verit, ccfv_threshold) UnCI imageI mem_Collect_eq set_map_is_image sound_cons.entails_subsets subsetI)
      moreover have \<open>{C. Neg C \<in> Pos ` F_of ` {concl_of \<iota>}} = {}\<close>
        by fast
      ultimately show \<open>{C. Pos C \<in> fml_ext ` total_strip J \<union> Pos ` (set (prems_of \<iota>) proj\<^sub>J J)} \<union>
                       {C. Neg C \<in> Pos ` F_of ` {concl_of \<iota>}} \<Turnstile>s
                       {C. Pos C \<in> Pos ` F_of ` {concl_of \<iota>}} \<union>
                       {C. Neg C \<in> fml_ext ` total_strip J \<union> Pos ` (set (prems_of \<iota>) proj\<^sub>J J)}\<close>
        (* /!\ Careful, this one is a little bit slow (enough to be noticed) /!\ *)
        using base
        by (smt (verit, del_insts) UnCI imageI inference.sel(1) inference.sel(2) mem_Collect_eq sound_cons.entails_subsets subsetI)
    qed
  next
    case (unsat \<N>)
    assume pre_cond: \<open>unsat_pre \<N>\<close>
    then have heads_of_\<N>_are_bot: \<open>\<forall> x \<in> set \<N>. F_of x = bot\<close> and
              \<N>_is_prop_unsat: \<open>propositionally_unsatisfiable (set \<N>)\<close>
      by blast+
    then have \<open>proj\<^sub>\<bottom> (set \<N>) = set \<N>\<close>
      using heads_of_\<N>_are_bot propositional_projection_def
      by blast
    then have \<open>\<forall> J. bot \<in> (set \<N>) proj\<^sub>J J\<close>
      using \<N>_is_prop_unsat propositional_model_def propositionally_unsatisfiable_def
      by force
    then show ?thesis
      unfolding AF_entails_sound_def sound_cons.entails_neg_def
      using unsat
      by auto
         (metis (no_types, lifting) empty_subsetI image_eqI insert_subset mem_Collect_eq sound_cons.bot_entails_empty
                                    sound_cons.entails_subsets)
  qed
qed

interpretation SInf_sound_inf_system: sound_inference_system SInf \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  by (standard, auto simp add: SInf_sound_wrt_entails_sound)

subsection \<open>The redundancy criterion\<close>

(* Report definition 15: splitting redundancy criterion *)
definition SRed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>SRed\<^sub>F \<N> = { AF.Pair C A | C A. \<forall> \<J>. total_strip \<J> \<supseteq> fset A \<longrightarrow> C \<in> Red_F (\<N> proj\<^sub>J \<J>) }
            \<union> { AF.Pair C A | C A. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A }\<close>

definition SRed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> where
  \<open>SRed\<^sub>I \<N> = { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)) }
           \<union> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> \<N> }\<close>

(* Report lemma 16 *)
lemma sredI_\<N>_proj_J_subset_redI_proj_J: \<open>to_AF bot \<notin> \<N> \<Longrightarrow> (SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J \<subseteq> Red_I (\<N> proj\<^sub>J J)\<close>
proof -
  assume \<open>to_AF bot \<notin> \<N>\<close>
  then have SRed\<^sub>I_\<N>_is: \<open>SRed\<^sub>I \<N> = { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. {base_inf \<M> \<C>} \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)) }\<close>
    using SRed\<^sub>I_def
    by auto
  then show \<open>(SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J \<subseteq> Red_I (\<N> proj\<^sub>J J)\<close>
  proof (cases \<open>(SRed\<^sub>I \<N>) \<iota>proj\<^sub>J J = {}\<close>)
    case True
    then show ?thesis
      by fast
  next
    case False
    then obtain \<iota>\<^sub>S where \<open>\<iota>\<^sub>S \<in> SRed\<^sub>I \<N>\<close>
      using enabled_projection_Inf_def
      by fastforce
    then have \<open>{\<iota>\<^sub>S} \<iota>proj\<^sub>J J \<subseteq> Red_I (\<N> proj\<^sub>J J)\<close>
      using SRed\<^sub>I_\<N>_is
      by auto
    then show ?thesis
      using SRed\<^sub>I_\<N>_is enabled_projection_Inf_def
      by force
  qed
qed

(* Report lemma 17 *)
lemma bot_not_in_sredF_\<N>: \<open>to_AF bot \<notin> SRed\<^sub>F \<N>\<close>
proof -
  have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<forall> \<J>. total_strip \<J> \<supseteq> fset A \<longrightarrow> C \<in> Red_F (\<N> proj\<^sub>J \<J>) }\<close>
    by (simp add: complete to_AF_def)
  moreover have \<open>to_AF bot \<notin> { AF.Pair C A | C A. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A }\<close>
    by (simp add: to_AF_def)
  ultimately show ?thesis
    using SRed\<^sub>F_def
    by auto
qed

definition ARed\<^sub>F :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF set\<close> where
  \<open>ARed\<^sub>F \<N> \<equiv> SRed\<^sub>F \<N>\<close>

text \<open>ARed_I is SRed_I limited to BASE inferences.\<close>

definition ARed\<^sub>I :: \<open>('f, 'v) AF set \<Rightarrow> ('f, 'v) AF inference set\<close> where
  \<open>ARed\<^sub>I \<N> \<equiv> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)) }\<close>

definition AInf :: \<open>('f, 'v) AF inference set\<close> where
  (* AInf is SInf with only the BASE rule. *)
  \<open>AInf \<equiv> { base_inf \<N> D | \<N> D. base_pre \<N> D }\<close>

definition \<G>\<^sub>F :: \<open>'v total_interpretation \<Rightarrow> ('f, 'v) AF \<Rightarrow> 'f set\<close> where
  \<open>\<G>\<^sub>F \<J> \<C> \<equiv> {\<C>} proj\<^sub>J \<J>\<close>

definition \<G>\<^sub>I :: \<open>'v total_interpretation \<Rightarrow> ('f, 'v) AF inference \<Rightarrow> 'f inference set\<close> where
  \<open>\<G>\<^sub>I \<J> \<iota> \<equiv> {\<iota>} \<iota>proj\<^sub>J \<J>\<close>

definition tiebreaker_order :: \<open>('f, 'v :: countable) AF rel\<close> where
  \<open>tiebreaker_order \<equiv> { (\<C>, \<C>'). F_of \<C> = F_of \<C>' \<and> A_of \<C> |\<subset>| A_of \<C>' }\<close>

abbreviation sqsupset_is_tiebreaker_order (infix \<open>\<sqsupset>\<close> 50) where
  \<open>\<C> \<sqsupset> \<C>' \<equiv> (\<C>, \<C>') \<in> tiebreaker_order\<close>

lemma tiebreaker_order_is_strict_partial_order: \<open>po_on (\<sqsupset>) UNIV\<close>
  unfolding po_on_def irreflp_on_def transp_on_def tiebreaker_order_def
  by auto

lemma wf_fsubset: \<open>wfP (|\<subset>|)\<close>
proof -
  have \<open>wfP (\<lambda> A B. fcard A < fcard B)\<close>
    by (metis (no_types, lifting) in_measure wfPUNIVI wf_induct wf_measure)
  then show \<open>wfP (|\<subset>|)\<close>
    by (smt (verit, ccfv_threshold) pfsubset_fcard_mono wfPUNIVI wfP_induct)
qed

lemma wfp_on_fsubset: \<open>wfp_on (|\<subset>|) UNIV\<close>
  using wf_fsubset
  by auto

lemma wfp_on_tiebreaker_order: \<open>wfp_on (\<sqsupset>) (UNIV :: ('f, 'v) AF set)\<close>
  unfolding wfp_on_def
proof (intro notI)
  assume \<open>\<exists> f. \<forall> i. f i \<in> UNIV \<and> f (Suc i) \<sqsupset> f i\<close>
  then obtain f where f_is: \<open>\<forall> i. f i \<in> UNIV \<and> f (Suc i) \<sqsupset> f i\<close>
    by auto
  define f' where \<open>f' = (\<lambda> i. A_of (f i))\<close>

  have \<open>\<forall> i. f' i \<in> UNIV \<and> f' (Suc i) |\<subset>| f' i\<close>
    using f_is
    unfolding f'_def tiebreaker_order_def
    by auto
  then show \<open>False\<close>
    using wfp_on_fsubset
    unfolding wfp_on_def
    by blast
qed

sublocale lift_from_ARed_to_FRed: light_tiebreaker_lifting \<open>{to_AF bot}\<close> AInf \<open>{bot}\<close> \<open>(\<Turnstile>\<inter>)\<close> Inf Red_I
                                                           Red_F \<open>\<G>\<^sub>F \<J>\<close> \<open>Some \<circ> \<G>\<^sub>I \<J>\<close> \<open>\<lambda>_. (\<sqsupset>)\<close>
proof (standard)
  fix N
  show \<open>Red_I N \<subseteq> Inf\<close>
    using Red_I_to_Inf
    by presburger
next
  fix B N
  assume \<open>B \<in> {bot}\<close> and
         \<open>N \<Turnstile>\<inter> {B}\<close>
  then show \<open>N - Red_F N \<Turnstile>\<inter> {B}\<close>
    using Red_F_Bot consequence_relation.entails_conjunctive_def consequence_relation_axioms
    by fastforce
next
  fix N N' :: \<open>'f set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_F N \<subseteq> Red_F N'\<close>
    using Red_F_of_subset
    by presburger
next
  fix N N' :: \<open>'f set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>Red_I N \<subseteq> Red_I N'\<close>
    using Red_I_of_subset
    by presburger
next
  fix N N'
  assume \<open>N' \<subseteq> Red_F N\<close>
  then show \<open>Red_F N \<subseteq> Red_F (N - N')\<close>
    using Red_F_of_Red_F_subset
    by presburger
next
  fix N N'
  assume \<open>N' \<subseteq> Red_F N\<close>
  then show \<open>Red_I N \<subseteq> Red_I (N - N')\<close>
    using Red_I_of_Red_F_subset
    by presburger
next
  fix \<iota> N
  assume \<open>\<iota> \<in> Inf\<close> and
         \<open>concl_of \<iota> \<in> N\<close>
  then show \<open>\<iota> \<in> Red_I N\<close>
    using Red_I_of_Inf_to_N
    by blast
next
  show \<open>{to_AF bot} \<noteq> {}\<close>
    by fast
next
  fix B :: \<open>('f, 'v) AF\<close>
  assume \<open>B \<in> {to_AF bot}\<close>
  then show \<open>\<G>\<^sub>F \<J> B \<noteq> {}\<close>
    by (simp add: \<G>\<^sub>F_def enabled_def enabled_projection_def to_AF_def)
next
  fix B :: \<open>('f, 'v) AF\<close>
  assume \<open>B \<in> {to_AF bot}\<close>
  then show \<open>\<G>\<^sub>F \<J> B \<subseteq> {bot}\<close>
    using \<G>\<^sub>F_def enabled_projection_def
    by auto
next
  fix \<iota>\<^sub>A
  assume \<iota>\<^sub>A_is_ainf: \<open>\<iota>\<^sub>A \<in> AInf\<close> and
         \<open>(Some \<circ> \<G>\<^sub>I \<J>) \<iota>\<^sub>A \<noteq> None\<close>
  have \<open>\<G>\<^sub>I \<J> \<iota>\<^sub>A \<subseteq> Red_I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
  proof (intro subsetI)
    fix x
    assume x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A: \<open>x \<in> \<G>\<^sub>I \<J> \<iota>\<^sub>A\<close>
    then obtain \<N> D where \<iota>\<^sub>A_is: \<open>\<iota>\<^sub>A = base_inf \<N> D\<close> and
                           infer_\<N>_D_is_inf: \<open>base_pre \<N> D\<close>
      using AInf_def \<iota>\<^sub>A_is_ainf
      by auto
    moreover have \<iota>\<^sub>A_is_enabled: \<open>enabled_inf \<iota>\<^sub>A \<J>\<close> and
                  x_is: \<open>x = \<iota>F_of \<iota>\<^sub>A\<close>
      using \<G>\<^sub>I_def enabled_projection_Inf_def x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A
      by auto
    then have \<open>prems_of \<iota>\<^sub>A = \<N>\<close>
      using \<iota>\<^sub>A_is
      by auto
    then have \<open>fBall (fset_of_list (map A_of \<N>)) (\<lambda> As. fset As \<subseteq> total_strip \<J>)\<close>
      using \<iota>\<^sub>A_is \<iota>\<^sub>A_is_enabled
      unfolding enabled_inf_def enabled_def
      by (simp add: fBall_fset_of_list_iff_Ball_set)
    then have \<open>fset (ffUnion (A_of |`| fset_of_list \<N>)) \<subseteq> total_strip \<J>\<close>
      by (simp add: fset_ffUnion_subset_iff_all_fsets_subset)
    then have \<open>enabled (AF.Pair D (ffUnion (A_of |`| fset_of_list \<N>))) \<J>\<close>
      unfolding enabled_def
      by auto
    then have \<open>{AF.Pair D (ffUnion (fset_of_list (map A_of \<N>)))} proj\<^sub>J \<J> = {D}\<close>
      unfolding enabled_projection_def F_of_def
      using \<iota>\<^sub>A_is_enabled \<iota>\<^sub>A_is
      by auto
    then have \<open>x \<in> Red_I (\<G>\<^sub>F \<J> (Pair D (ffUnion (fset_of_list (map A_of \<N>)))))\<close>
      using x_in_\<G>\<^sub>I_of_\<iota>\<^sub>A \<iota>\<^sub>A_is_enabled x_is infer_\<N>_D_is_inf \<iota>\<^sub>A_is
      unfolding \<G>\<^sub>I_def \<G>\<^sub>F_def \<iota>F_of_def
      by (simp add: Red_I_of_Inf_to_N)
    then show \<open>x \<in> Red_I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
      by (simp add: \<iota>\<^sub>A_is)
  qed
  then show \<open>the ((Some \<circ> \<G>\<^sub>I \<J>) \<iota>\<^sub>A) \<subseteq> Red_I (\<G>\<^sub>F \<J> (concl_of \<iota>\<^sub>A))\<close>
    by simp
next
  fix g
  show \<open>po_on (\<sqsupset>) UNIV\<close>
    using tiebreaker_order_is_strict_partial_order
    by blast
next
  fix g
  show \<open>wfp_on (\<sqsupset>) UNIV\<close>
    using wfp_on_tiebreaker_order
    by blast
qed

lemma Union_of_enabled_projection_is_enabled_projection: \<open>(\<Union> \<C> \<in> \<N>. {\<C>} proj\<^sub>J \<J>) = \<N> proj\<^sub>J \<J>\<close>
  unfolding enabled_projection_def
  by blast

(* Check that ARed\<^sub>I and FRed\<^sub>I\<^bsup>\<inter>\<G>\<^esup> coincide *)
lemma ARed\<^sub>I_is_FRed\<^sub>I: \<open>ARed\<^sub>I \<N> = (\<Inter> J. lift_from_ARed_to_FRed.Red_I_\<G> J \<N>)\<close>
proof (intro subset_antisym subsetI)
  fix \<iota>
  assume \<open>\<iota> \<in> ARed\<^sub>I \<N>\<close>
  then obtain \<M> \<C> where \<iota>_is: \<open>\<iota> = base_inf \<M> \<C>\<close> and
                         Infer_\<M>_\<C>_in_Inf: \<open>base_pre \<M> \<C>\<close> and
                         \<iota>_in_Red_I: \<open>\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>)\<close>
    using ARed\<^sub>I_def
    by fastforce
  then have \<iota>_is_AInf: \<open>\<iota> \<in> AInf\<close>
    using AInf_def
    by blast
  then have \<open>\<forall> J. {\<iota>} \<iota>proj\<^sub>J J \<subseteq> Red_I (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
    unfolding \<G>\<^sub>F_def
    using \<iota>_in_Red_I \<iota>_is Union_of_enabled_projection_is_enabled_projection
    by auto
  then have \<open>\<forall> J. \<iota> \<in> lift_from_ARed_to_FRed.Red_I_\<G> J \<N>\<close>
    using \<iota>_is_AInf
    unfolding lift_from_ARed_to_FRed.Red_I_\<G>_def \<G>\<^sub>I_def
    by auto
  then show \<open>\<iota> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_I_\<G> J \<N>)\<close>
    by blast
next
  fix \<iota>
  assume \<iota>_in_Red_I_\<G>: \<open>\<iota> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_I_\<G> J \<N>)\<close>
  then have \<iota>_is_AInf: \<open>\<iota> \<in> AInf\<close> and
            all_J_\<G>\<^sub>I_subset_Red_I: \<open>\<forall> J. \<G>\<^sub>I J \<iota> \<subseteq> Red_I (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
    unfolding lift_from_ARed_to_FRed.Red_I_\<G>_def
    by auto
  then obtain \<M> \<C> where \<iota>_is: \<open>\<iota> = base_inf \<M> \<C>\<close> and
                         Infer_\<M>_\<C>_is_Inf: \<open>base_pre \<M> \<C>\<close>
    using AInf_def
    by auto
  then obtain \<iota>\<^sub>F where \<iota>\<^sub>F_is: \<open>\<iota>\<^sub>F = \<iota>F_of \<iota>\<close>
    by auto
  then have \<open>\<exists> \<M> \<C>. \<iota> = base_inf \<M> \<C> \<and> base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (\<N> proj\<^sub>J \<J>))\<close>
    using \<iota>_is Infer_\<M>_\<C>_is_Inf all_J_\<G>\<^sub>I_subset_Red_I
    unfolding \<G>\<^sub>I_def \<G>\<^sub>F_def
    using Union_of_enabled_projection_is_enabled_projection
    by fastforce
  then show \<open>\<iota> \<in> ARed\<^sub>I \<N>\<close>
    unfolding ARed\<^sub>I_def
    by auto
qed

lemma subformula_of_enabled_formula_is_enabled: \<open>A_of \<C> |\<subset>| A_of \<C>' \<Longrightarrow> enabled \<C>' J \<Longrightarrow> enabled \<C> J\<close>
  unfolding enabled_def
  by (meson less_eq_fset.rep_eq pfsubset_imp_fsubset subset_trans)

(* Check that ARed\<^sub>F and FRed\<^sub>F\<^bsup>\<inter>\<G>,\<sqsupset>\<^esup> coincide *)
lemma ARed\<^sub>F_is_FRed\<^sub>F: \<open>ARed\<^sub>F \<N> = (\<Inter> J. lift_from_ARed_to_FRed.Red_F_\<G> J \<N>)\<close>
proof (intro subset_antisym subsetI)
  fix \<C>
  assume \<C>_in_ARed\<^sub>F: \<open>\<C> \<in> ARed\<^sub>F \<N>\<close>
  then obtain C A where \<C>_is: \<open>\<C> = AF.Pair C A\<close>
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def
    by blast
  consider (a) \<open>\<forall> \<J>. fset A \<subseteq> total_strip \<J> \<longrightarrow> C \<in> Red_F (\<N> proj\<^sub>J \<J>)\<close> |
           (b) \<open>\<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> A_of \<C> |\<subset>| A\<close>
    using \<C>_in_ARed\<^sub>F \<C>_is
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def
    by blast
  then show \<open>\<C> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_F_\<G> J \<N>)\<close>
    unfolding lift_from_ARed_to_FRed.Red_F_\<G>_def
  proof (cases)
    case a
    then have \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>))\<close>
      unfolding Red_F_strict_def \<G>\<^sub>F_def
      using Union_of_enabled_projection_is_enabled_projection \<C>_is enabled_projection_def
            \<C>_is complete enabled_projection_def
      using enabled_def
      by force
    then have \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) })\<close>
      by blast
    then show \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E) })\<close>
      by blast
  next
    case b
    then have \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. \<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> D \<in> \<G>\<^sub>F J E\<close>
      unfolding \<G>\<^sub>F_def tiebreaker_order_def enabled_projection_def
      using subformula_of_enabled_formula_is_enabled
      (* /!\ Careful, a bit slow (\<sim> 1s) /!\ *)
      by (smt (verit, ccfv_SIG) AF.sel(1) AF.sel(2) \<C>_is case_prodI mem_Collect_eq singletonD singletonI)
    then have \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. \<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E })\<close>
      by blast
    then show \<open>\<C> \<in> (\<Inter> J. { C. \<forall> D \<in> \<G>\<^sub>F J C. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> C \<and> D \<in> \<G>\<^sub>F J E) })\<close>
      by blast
  qed
next
  fix \<C>
  assume \<C>_in_Red_F_\<G>: \<open>\<C> \<in> (\<Inter> J. lift_from_ARed_to_FRed.Red_F_\<G> J \<N>)\<close>
  then have \<C>_in_Red_F_\<G>_unfolded: \<open>\<forall> J. \<forall> D \<in> \<G>\<^sub>F J \<C>. D \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> D \<in> \<G>\<^sub>F J E)\<close>
    unfolding lift_from_ARed_to_FRed.Red_F_\<G>_def
    by blast
  then have \<C>_in_Red_F_\<G>_if_enabled: \<open>\<forall> J. enabled \<C> J \<longrightarrow> F_of \<C> \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> F_of \<C> \<in> \<G>\<^sub>F J E)\<close>
    unfolding \<G>\<^sub>F_def enabled_projection_def
    by auto
  obtain C A where \<C>_is: \<open>\<C> = AF.Pair C A\<close>
    by (meson AF.exhaust_sel)
  then have \<open>\<forall> J. fset A \<subseteq> total_strip J \<longrightarrow> C \<in> Red_F (\<Union> (\<G>\<^sub>F J ` \<N>)) \<or> (\<exists> E \<in> \<N>. E \<sqsupset> \<C> \<and> C \<in> \<G>\<^sub>F J E)\<close>
    using \<C>_in_Red_F_\<G>_if_enabled
    unfolding enabled_def
    by simp
  then show \<open>\<C> \<in> ARed\<^sub>F \<N>\<close>
    using \<C>_is \<C>_in_Red_F_\<G>_if_enabled
    unfolding ARed\<^sub>F_def SRed\<^sub>F_def \<G>\<^sub>F_def enabled_def tiebreaker_order_def
    using Union_of_enabled_projection_is_enabled_projection
    by auto
qed

lemma Union_of_singleton_is_setcompr: \<open>(\<Union> x \<in> A. { y. y = f x \<and> P x }) = { f x | x. x \<in> A \<and> P x }\<close>
  by auto

(* Check that both \<Turnstile>\<^sub>A\<^sub>F and \<Turnstile>\<^sub>\<G>\<^sup>\<inter> coincide *)
lemma entails_is_entails_\<G>: \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>} \<longleftrightarrow> (\<forall> \<J>. lift_from_ARed_to_FRed.entails_\<G> \<J> \<M> {\<C>})\<close>
proof (intro iffI allI)
  fix \<J>
  assume \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
  then show \<open>lift_from_ARed_to_FRed.entails_\<G> \<J> \<M> {\<C>}\<close>
    unfolding \<G>\<^sub>F_def AF_entails_def enabled_projection_def enabled_set_def entails_conjunctive_def
    by (simp add: Union_of_singleton_is_setcompr)
next
  assume entails_\<G>_\<M>_\<C>: \<open>\<forall> \<J>. lift_from_ARed_to_FRed.entails_\<G> \<J> \<M> {\<C>}\<close>
  show \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {\<C>}\<close>
    unfolding \<G>\<^sub>F_def AF_entails_def enabled_set_def
    proof (intro allI impI)
      fix J
      assume \<open>\<forall> \<C> \<in> {\<C>}. enabled \<C> J\<close>
      then show \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` {\<C>}\<close>
        using entails_\<G>_\<M>_\<C>
        unfolding \<G>\<^sub>F_def enabled_projection_def entails_conjunctive_def
        by (simp add: Union_of_singleton_is_setcompr)
    qed
qed

lemma SRed\<^sub>F_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
proof -
  fix N

  have And_to_Union: \<open>\<And> J. N - lift_from_ARed_to_FRed.Red_F_\<G> J N \<subseteq> (\<Union> J. N - lift_from_ARed_to_FRed.Red_F_\<G> J N)\<close>
    by blast

  assume N_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  have \<open>lift_from_ARed_to_FRed.entails_\<G> J N {to_AF bot} \<Longrightarrow> lift_from_ARed_to_FRed.entails_\<G> J (N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close> for J
    using lift_from_ARed_to_FRed.Red_F_Bot_F
    by blast
  then have \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - ARed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  proof -
    assume \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close> and
           \<open>\<And> J. lift_from_ARed_to_FRed.entails_\<G> J N {to_AF bot} \<Longrightarrow> lift_from_ARed_to_FRed.entails_\<G> J (N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close>
    then have Red_F_\<G>_entails_\<G>_bot: \<open>\<And> J. lift_from_ARed_to_FRed.entails_\<G> J (N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close>
      using entails_is_entails_\<G>
      by blast
    then have \<open>\<And> J. lift_from_ARed_to_FRed.entails_\<G> J (\<Union> J. N - lift_from_ARed_to_FRed.Red_F_\<G> J N) {to_AF bot}\<close>
      using And_to_Union
      by (meson lift_from_ARed_to_FRed.entails_trans lift_from_ARed_to_FRed.subset_entailed)
    then show \<open>N - ARed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
      using ARed\<^sub>F_is_FRed\<^sub>F entails_is_entails_\<G>
      by fastforce
  qed
  then show \<open>N - SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using ARed\<^sub>F_def N_entails_bot
    by force
qed

lemma SRed\<^sub>F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> SRed\<^sub>F N \<subseteq> SRed\<^sub>F N'\<close>
proof -
  fix N N' :: \<open>('f, 'v) AF set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>SRed\<^sub>F N \<subseteq> SRed\<^sub>F N'\<close>
    unfolding SRed\<^sub>F_def enabled_projection_def
    by (auto, smt (verit, best) Collect_mono Red_F_of_subset subsetD)
qed

lemma SRed\<^sub>I_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> SRed\<^sub>I N \<subseteq> SRed\<^sub>I N'\<close>
proof -
  fix N N' :: \<open>('f, 'v) AF set\<close>
  assume \<open>N \<subseteq> N'\<close>
  then show \<open>SRed\<^sub>I N \<subseteq> SRed\<^sub>I N'\<close>
    unfolding SRed\<^sub>I_def enabled_projection_Inf_def enabled_projection_def enabled_inf_def \<iota>F_of_def
    (* /!\ This is a bit slow (between 5 and 10s), but this works... /!\ *)
    by (auto, (smt (verit, best) Red_I_of_subset mem_Collect_eq subset_iff)+)
qed

lemma SRed\<^sub>F_of_SRed\<^sub>F_subset_F: \<open>N' \<subseteq> SRed\<^sub>F N \<Longrightarrow> SRed\<^sub>F N \<subseteq> SRed\<^sub>F (N - N')\<close>
proof -
  fix N N'
  assume N'_subset_SRed\<^sub>F_N: \<open>N' \<subseteq> SRed\<^sub>F N\<close>
  have \<open>N' \<subseteq> ARed\<^sub>F N \<Longrightarrow> ARed\<^sub>F N \<subseteq> ARed\<^sub>F (N - N')\<close>
    using lift_from_ARed_to_FRed.Red_F_of_Red_F_subset_F
  proof -
    assume N'_subset_ARed\<^sub>F_N: \<open>N' \<subseteq> ARed\<^sub>F N\<close> and
           \<open>(\<And> N' \<J> N. N' \<subseteq> lift_from_ARed_to_FRed.Red_F_\<G> \<J> N \<Longrightarrow>
              lift_from_ARed_to_FRed.Red_F_\<G> \<J> N \<subseteq> lift_from_ARed_to_FRed.Red_F_\<G> \<J> (N - N'))\<close>
    then have \<open>\<And> N' N. N' \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> N) \<Longrightarrow>
                  (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> N) \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> (N - N'))\<close>
      by (meson INF_mono' UNIV_I le_INF_iff)
    then show \<open>ARed\<^sub>F N \<subseteq> ARed\<^sub>F (N - N')\<close>
      using ARed\<^sub>F_is_FRed\<^sub>F N'_subset_ARed\<^sub>F_N
      by presburger
  qed
  then show \<open>SRed\<^sub>F N \<subseteq> SRed\<^sub>F (N - N')\<close>
    by (simp add: ARed\<^sub>F_def N'_subset_SRed\<^sub>F_N)
qed

lemma SRed\<^sub>I_of_SRed\<^sub>F_subset_F: \<open>N' \<subseteq> SRed\<^sub>F N \<Longrightarrow> SRed\<^sub>I N \<subseteq> SRed\<^sub>I (N - N')\<close>
proof -
  fix N N'
  assume N'_subset_SRed\<^sub>F_N: \<open>N' \<subseteq> SRed\<^sub>F N\<close>
  have works_for_ARed\<^sub>I: \<open>N' \<subseteq> ARed\<^sub>F N \<Longrightarrow> ARed\<^sub>I N \<subseteq> ARed\<^sub>I (N - N')\<close>
    using lift_from_ARed_to_FRed.Red_I_of_Red_F_subset_F
  proof -
    assume N'_subset_ARed\<^sub>F_N: \<open>N' \<subseteq> ARed\<^sub>F N\<close> and
           \<open>(\<And> N' \<J> N. N' \<subseteq> lift_from_ARed_to_FRed.Red_F_\<G> \<J> N \<Longrightarrow>
               lift_from_ARed_to_FRed.Red_I_\<G> \<J> N \<subseteq> lift_from_ARed_to_FRed.Red_I_\<G> \<J> (N - N'))\<close>
    then have \<open>\<And> N' N. N' \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_F_\<G> \<J> N) \<Longrightarrow>
                  (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_I_\<G> \<J> N) \<subseteq> (\<Inter> \<J>. lift_from_ARed_to_FRed.Red_I_\<G> \<J> (N - N'))\<close>
      by (metis (no_types, lifting) INF_mono' UNIV_I le_INF_iff)
    then show \<open>ARed\<^sub>I N \<subseteq> ARed\<^sub>I (N - N')\<close>
      using ARed\<^sub>I_is_FRed\<^sub>I ARed\<^sub>F_is_FRed\<^sub>F N'_subset_ARed\<^sub>F_N
      by presburger
  qed
  moreover have \<open>unsat_inf \<N> \<in> SRed\<^sub>I (N - N')\<close> if \<open>unsat_pre \<N>\<close> and
                                                   \<iota>_is_redundant: \<open>unsat_inf \<N> \<in> SRed\<^sub>I N\<close> for \<N>
    using bot_not_in_sredF_\<N> N'_subset_SRed\<^sub>F_N \<iota>_is_redundant
    unfolding SRed\<^sub>I_def SRed\<^sub>F_def
    (* /!\ Quite slow... /!\ *)
    by (smt (verit, del_insts) ARed\<^sub>F_def ARed\<^sub>I_def Diff_iff N'_subset_SRed\<^sub>F_N Un_iff bot_not_in_sredF_\<N> works_for_ARed\<^sub>I mem_Collect_eq subsetD)
  ultimately show \<open>SRed\<^sub>I N \<subseteq> SRed\<^sub>I (N - N')\<close>
    using N'_subset_SRed\<^sub>F_N bot_not_in_sredF_\<N>
    unfolding SRed\<^sub>F_def ARed\<^sub>F_def SRed\<^sub>I_def ARed\<^sub>I_def
    (* /!\ A bit slow /!\ *)
    by (smt (verit, del_insts) Collect_cong Diff_iff N'_subset_SRed\<^sub>F_N Un_iff bot_not_in_sredF_\<N> subset_iff)
qed

lemma SRed\<^sub>I_of_SInf_to_N_F: \<open>\<iota>\<^sub>S \<in> SInf \<Longrightarrow> concl_of \<iota>\<^sub>S \<in> N \<Longrightarrow> \<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
proof -
  fix \<iota>\<^sub>S N
  assume \<open>\<iota>\<^sub>S \<in> SInf\<close> and
         concl_\<iota>\<^sub>S_in_N: \<open>concl_of \<iota>\<^sub>S \<in> N\<close>
  then have \<open>Splitting_rules \<iota>\<^sub>S\<close>
    by blast
  then show \<open>\<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
    unfolding SRed\<^sub>I_def
  proof (cases \<iota>\<^sub>S rule: Splitting_rules.cases)
    case (base \<N> D)
    obtain \<M> \<C> where \<iota>\<^sub>S_is: \<open>\<iota>\<^sub>S = base_inf \<M> \<C>\<close> and
                      Infer_\<M>_\<C>_is_Inf: \<open>base_pre \<M> \<C>\<close>
      using base
      by blast
    have \<open>\<forall> J. { base_inf \<M> \<C> } \<iota>proj\<^sub>J J \<subseteq> Red_I (N proj\<^sub>J J)\<close>
      unfolding enabled_projection_Inf_def enabled_projection_def \<iota>F_of_def enabled_inf_def
    proof (intro allI subsetI, simp)
      fix J
      assume all_enabled_in_\<M>: \<open>\<forall> \<C> \<in> set \<M>. enabled \<C> J\<close>
      then have A_of_\<M>_to_\<C>_in_N: \<open>AF.Pair \<C> (ffUnion (fset_of_list (map A_of \<M>))) \<in> N\<close>
        using \<iota>\<^sub>S_is concl_\<iota>\<^sub>S_in_N
        by auto
      moreover have \<open>fBall (fset_of_list \<M>) (\<lambda> x. fset (A_of x) \<subseteq> total_strip J)\<close>
        using all_enabled_in_\<M>
        unfolding enabled_def
        by (meson fBall_fset_of_list_iff_Ball_set)
      then have \<open>fBall (A_of |`| fset_of_list \<M>) (\<lambda> x. fset x \<subseteq> total_strip J)\<close>
        by auto
      then have \<open>enabled (AF.Pair \<C> (ffUnion (A_of |`| fset_of_list \<M>))) J\<close>
        using A_of_\<M>_to_\<C>_in_N
        unfolding enabled_def
        using fset_ffUnion_subset_iff_all_fsets_subset
        by (metis AF.sel(2))
      ultimately show \<open>Infer (map F_of \<M>) \<C> \<in> Red_I {F_of \<C> |\<C>. \<C> \<in> N \<and> enabled \<C> J}\<close>
        by (metis (mono_tags, lifting) AF.sel(1) Infer_\<M>_\<C>_is_Inf Red_I_of_Inf_to_N fset_of_list_map inference.sel(2) mem_Collect_eq)
    qed
    then have \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall>\<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>))}\<close>
      using \<iota>\<^sub>S_is Infer_\<M>_\<C>_is_Inf
      by auto
    then show \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall>\<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>)) } \<union>
                    { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
      by fast
  next
    case (unsat \<N>)
    then have \<open>\<iota>\<^sub>S \<in> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N}\<close>
      using concl_\<iota>\<^sub>S_in_N
      by fastforce
    then show \<open>\<iota>\<^sub>S \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall>\<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>)) } \<union>
                    { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
      by fast
  qed
qed

(* Report lemma 18 *)
sublocale S_calculus: calculus \<open>to_AF bot\<close> SInf AF_entails SRed\<^sub>I SRed\<^sub>F
proof
  fix N N' \<iota>\<^sub>S
  show \<open>SRed\<^sub>I N \<subseteq> SInf\<close>
    unfolding SRed\<^sub>I_def
    using Splitting_rules.base Splitting_rules.unsat
    by blast
  show \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> N - SRed\<^sub>F N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using SRed\<^sub>F_entails_bot .
  show \<open>N \<subseteq> N' \<Longrightarrow> SRed\<^sub>F N \<subseteq> SRed\<^sub>F N'\<close>
    using SRed\<^sub>F_of_subset_F .
  show \<open>N \<subseteq> N' \<Longrightarrow> SRed\<^sub>I N \<subseteq> SRed\<^sub>I N'\<close>
    using SRed\<^sub>I_of_subset_F .
  show \<open>N' \<subseteq> SRed\<^sub>F N \<Longrightarrow> SRed\<^sub>F N \<subseteq> SRed\<^sub>F (N - N')\<close>
    using SRed\<^sub>F_of_SRed\<^sub>F_subset_F .
  show \<open>N' \<subseteq> SRed\<^sub>F N \<Longrightarrow> SRed\<^sub>I N \<subseteq> SRed\<^sub>I (N - N')\<close>
    using SRed\<^sub>I_of_SRed\<^sub>F_subset_F .
  show \<open>\<iota>\<^sub>S \<in> SInf \<Longrightarrow> concl_of \<iota>\<^sub>S \<in> N \<Longrightarrow> \<iota>\<^sub>S \<in> SRed\<^sub>I N\<close>
    using SRed\<^sub>I_of_SInf_to_N_F .
qed

end (* locale splitting_calculus *)

locale splitting_calculus_with_simps =
  splitting_calculus bot Inf entails entails_sound Red_I Red_F V fml
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close>
  + fixes asn :: \<open>'f \<Rightarrow> 'v sign set\<close>
    assumes
      fml_entails_C: \<open>fml_ext ` asn C \<Turnstile>\<^sub>\<sim> {Pos C}\<close> and
      C_entails_fml: \<open>{Pos C} \<Turnstile>\<^sub>\<sim> fml_ext ` asn C\<close> and
      asn_not_empty: \<open>asn C \<noteq> {}\<close>
begin

definition splittable :: \<open>'f \<Rightarrow> 'f fset \<Rightarrow> bool\<close> where
  \<open>splittable C Cs \<longleftrightarrow> C \<noteq> bot \<and> fcard Cs \<ge> 2 \<and> {C} \<Turnstile>s fset Cs \<and> (\<forall> C'. C' |\<in>| Cs \<longrightarrow> C \<in> Red_F {C'})\<close>

definition split :: \<open>'f \<Rightarrow> 'f fset \<Rightarrow> ('f, 'v) AF fset\<close> where
  \<open>splittable C Cs \<Longrightarrow> split C Cs \<equiv> (\<lambda> C'. AF.Pair C' {| SOME a. a \<in> asn C' |}) |`| Cs\<close>

abbreviation split_pre :: \<open>('f, 'v) AF \<Rightarrow> 'f fset \<Rightarrow> ('f, 'v) AF fset \<Rightarrow> bool\<close> where
  \<open>split_pre \<C> Cs As \<equiv> splittable (F_of \<C>) Cs \<and> split (F_of \<C>) Cs = As\<close>

lemma split_creates_singleton_assertion_sets: \<open>split_pre \<C> Cs As \<Longrightarrow> A |\<in>| As \<Longrightarrow> (\<exists> a. A_of A = {| a |})\<close>
  using split_def
  by force


abbreviation collect_pre :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>collect_pre \<C> \<M> \<equiv> F_of \<C> \<noteq> bot \<and> \<M> \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot (A_of \<C>) } \<and> (\<forall> \<C> \<in> \<M>. F_of \<C> = bot)\<close>



abbreviation trim_pre :: \<open>('f, 'v) AF \<Rightarrow> 'v sign fset \<Rightarrow> 'v sign fset \<Rightarrow> ('f, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>trim_pre \<C> A B \<M> \<equiv> A_of \<C> = A |\<union>| B \<and> F_of \<C> \<noteq> bot \<and> \<M> \<union> { AF.Pair bot A } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot B } \<and>
                       (\<forall> \<C> \<in> \<M>. F_of \<C> = bot) \<and> A |\<inter>| B = {||} \<and> A \<noteq> {||}\<close>

(* Report theorem 14 *)
theorem SInf_with_simps_sound_wrt_entails_sound:
  (* SPLIT *)   \<open>split_pre \<C> Cs As \<Longrightarrow> { \<C> } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) }\<close>
                \<open>split_pre \<C> Cs As \<Longrightarrow> { \<C> } \<Turnstile>s\<^sub>A\<^sub>F fset As\<close>
  (* COLLECT *) \<open>collect_pre \<C> \<M> \<Longrightarrow> \<M> \<Turnstile>s\<^sub>A\<^sub>F { \<C> }\<close> (* May need to be removed *)
  (* TRIM *)    \<open>trim_pre \<C> A B \<M> \<Longrightarrow> \<M> \<union> { \<C> } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair (F_of \<C>) B }\<close>
proof -
  assume \<open>split_pre \<C> Cs As\<close>
  then show \<open>{ \<C> } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) }\<close>
    sorry
next
  assume \<open>split_pre \<C> Cs As\<close>
  then have \<open>\<forall> A \<in> fset As. { \<C> } \<Turnstile>s\<^sub>A\<^sub>F { A }\<close>
    sorry
  then show \<open>{ \<C> } \<Turnstile>s\<^sub>A\<^sub>F fset As\<close>
    unfolding AF_entails_sound_def enabled_set_def
    apply auto
    sorry
next
  assume \<open>collect_pre \<C> \<M>\<close>
  then have \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot (A_of \<C>) }\<close>
    by blast
  then show \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F { \<C> }\<close>
    sorry
next
  assume \<open>trim_pre \<C> A B \<M>\<close>
  then show \<open>\<M> \<union> { \<C> } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair (F_of \<C>) B }\<close>
    sorry
qed

lemma enabled_set_singleton [simp]: \<open>enabled_set {\<C>} J \<longleftrightarrow> enabled \<C> J\<close>
  by (auto simp add: enabled_set_def)

(* Report theorem 19 *)
theorem simplification_to_redundant:
  (* SPLIT *)   \<open>split_pre \<C> Cs As \<Longrightarrow> \<C> \<in> SRed\<^sub>F ({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) } \<union> fset As)\<close>
  (* COLLECT *) \<open>collect_pre \<C> \<M> \<Longrightarrow> \<C> \<in> SRed\<^sub>F \<M>\<close>
  (* TRIM *)    \<open>trim_pre \<C> A B \<M> \<Longrightarrow> \<C> \<in> SRed\<^sub>F (\<M> \<union> { AF.Pair (F_of \<C>) B })\<close>
proof -
  assume pre_cond: \<open>split_pre \<C> Cs As\<close>
  then have F_of_\<C>_not_bot: \<open>F_of \<C> \<noteq> bot\<close> and
            \<open>fcard Cs \<ge> 2\<close> and
            \<open>{ F_of \<C> } \<Turnstile>s fset Cs\<close> and
            \<C>_red_to_splitted_\<C>s: \<open>\<forall> C'. C' |\<in>| Cs \<longrightarrow> F_of \<C> \<in> Red_F {C'}\<close> and
            splittable_pre: \<open>splittable (F_of \<C>) Cs\<close> and
            split_to_As: \<open>split (F_of \<C>) Cs = As\<close>
    using split_def splittable_def
    by blast+
  then have \<open>\<forall> J. enabled \<C> J \<longrightarrow> F_of \<C> \<in> Red_F (({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) } proj\<^sub>J J)
                                                   \<union> (fset As proj\<^sub>J J))\<close>
  proof (intro allI impI)
    fix J
    assume \<C>_enabled: \<open>enabled \<C> J\<close>
    then show \<open>F_of \<C> \<in> Red_F (({ AF.Pair bot (ffUnion (fimage neg |`| A_of |`| As) |\<union>| A_of \<C>) } proj\<^sub>J J) \<union> (fset As proj\<^sub>J J))\<close>
    proof (cases \<open>\<exists> A. A |\<in>| A_of |`| As \<and> (\<exists> a. a |\<in>| A \<and> a \<in> total_strip J)\<close>)
      case True
      then have ex_C_enabled_in_As: \<open>\<exists> C. C |\<in>| As \<and> enabled C J\<close>
        using enabled_def split_creates_singleton_assertion_sets pre_cond
        by fastforce
      then have \<open>\<exists> C. C \<in> fset As proj\<^sub>J J\<close>
        by (simp add: enabled_projection_def fmember.rep_eq)
      then show ?thesis
        using \<C>_red_to_splitted_\<C>s split_to_As Red_F_of_subset[of \<open>fset As proj\<^sub>J J\<close>]
        unfolding split_def[OF splittable_pre]
        by (smt (verit, del_insts) AF.sel(1) CollectI Red_F_of_subset Un_subset_iff ex_C_enabled_in_As enabled_projection_def
                                   fimageE fmember.rep_eq insert_subset subset_iff sup_bot_right)
    next
      case False
      then have \<open>fset As proj\<^sub>J J = {}\<close>
        using split_creates_singleton_assertion_sets[OF pre_cond]
        by (smt (verit, del_insts) Collect_empty_eq enabled_def enabled_projection_def fimage_finsert finsert.rep_eq
                                   finsertCI insert_subset mk_disjoint_finsert notin_fset)
      moreover have \<open>\<forall> A. A |\<in>| A_of |`| As \<longrightarrow> (\<forall> a. a |\<in>| A \<longrightarrow> \<not> a \<in> total_strip J)\<close>
        using False
        by blast
      then have \<open>\<forall> A. A |\<in>| A_of |`| As \<longrightarrow> (\<forall> a. a |\<in>| A \<longrightarrow> neg a \<in> total_strip J)\<close>
        by auto
      then have \<open>fset (ffUnion ((fimage neg \<circ> A_of) |`| As)) \<subseteq> total_strip J\<close>
        (* /!\ Slow enough to be noticed /!\ *)
        by (smt (verit, ccfv_threshold) fimageE fset.map_comp if_in_ffUnion_then_in_subset notin_fset subsetI)
      then have \<open>fset (ffUnion ((fimage neg \<circ> A_of) |`| As) |\<union>| A_of \<C>) \<subseteq> total_strip J\<close>
        using \<C>_enabled
        by (simp add: enabled_def)
      then have \<open>{AF.Pair bot (ffUnion ((fimage neg \<circ> A_of) |`| As) |\<union>| A_of \<C>)} proj\<^sub>J J = {bot}\<close>
        unfolding enabled_projection_def enabled_def
        by auto
      ultimately show ?thesis
        by (simp add: F_of_\<C>_not_bot all_red_to_bot)
    qed
  qed
  then show \<open>\<C> \<in> SRed\<^sub>F ({ AF.Pair bot (ffUnion ((|`|) neg |`| A_of |`| As) |\<union>| A_of \<C>) } \<union> fset As)\<close>
    unfolding SRed\<^sub>F_def enabled_def
    by (intro UnI1)
       (smt (verit, ccfv_threshold) AF.collapse CollectI distrib_proj)
next
  assume \<open>collect_pre \<C> \<M>\<close>
  then have head_\<C>_not_bot: \<open>F_of \<C> \<noteq> bot\<close> and
            \<M>_entails_bot_\<C>: \<open>\<M> \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot (A_of \<C>) }\<close> and
            all_heads_are_bot_in_\<M>: \<open>\<forall> \<C> \<in> \<M>. F_of \<C> = bot\<close>
    by blast+
  have ex_enabled_in_\<M>: \<open>\<And> J. (\<exists> \<C>' \<in> \<M>. enabled \<C>' J) \<Longrightarrow> enabled \<C> J \<Longrightarrow> F_of \<C> \<in> Red_F (\<M> proj\<^sub>J J)\<close> and
       not_ex_enabled_in_\<M>: \<open>\<And> J. \<not> (\<exists> \<C>' \<in> \<M>. enabled \<C>' J) \<Longrightarrow> enabled \<C> J \<Longrightarrow> sound_cons.entails_neg (fml_ext ` total_strip J) {Pos bot}\<close>
  proof -
    fix J
    assume \<C>_enabled: \<open>enabled \<C> J\<close> and
           \<open>\<exists> \<C>' \<in> \<M>. enabled \<C>' J\<close>
    then have \<open>\<M> proj\<^sub>J J = {bot}\<close>
      using all_heads_are_bot_in_\<M>
      unfolding enabled_projection_def
      by fast
    then show \<open>F_of \<C> \<in> Red_F (\<M> proj\<^sub>J J)\<close>
      using all_red_to_bot[OF head_\<C>_not_bot]
      by simp
  next
    fix J
    assume \<C>_enabled: \<open>enabled \<C> J\<close> and
           \<open>\<not> (\<exists> \<C>' \<in> \<M>. enabled \<C>' J)\<close>
    then have \<M>_proj_J_empty: \<open>\<M> proj\<^sub>J J = {}\<close>
      unfolding enabled_projection_def
      by blast
    moreover have \<open>enabled (AF.Pair bot (A_of \<C>)) J\<close>
      using \<C>_enabled
      by (auto simp add: enabled_def)
    then show \<open>sound_cons.entails_neg (fml_ext ` total_strip J) {Pos bot}\<close>
      using \<M>_entails_bot_\<C> \<M>_proj_J_empty
      unfolding AF_entails_sound_def
      by auto
  qed

  have \<open>\<And> J. \<not> (\<exists> C' \<in> \<M>. enabled C' J) \<Longrightarrow> enabled \<C> J \<Longrightarrow> {} \<Turnstile>s {bot}\<close>
  proof -
    fix J
    assume \<open>\<not> (\<exists> C' \<in> \<M>. enabled C' J)\<close> and
           \<open>enabled \<C> J\<close>
    then have J_entails_neg_bot: \<open>sound_cons.entails_neg (fml_ext ` total_strip J) {Pos bot}\<close>
      using not_ex_enabled_in_\<M>
      by blast
    then have J_entails_bot: \<open>{ C. Pos C \<in> fml_ext ` total_strip J } \<Turnstile>s {bot} \<union> { C. Neg C \<in> fml_ext ` total_strip J }\<close>
      unfolding sound_cons.entails_neg_def
      by simp
    have \<open>\<forall> M' N'. {} \<subseteq> M' \<and> {bot} \<subseteq> N' \<and> M' \<union> N' = UNIV \<longrightarrow> M' \<Turnstile>s N'\<close>
    proof (intro allI impI, elim conjE)
      fix M' N'
      assume \<open>{} \<subseteq> M'\<close> and
             \<open>{bot} \<subseteq> N'\<close> and
             \<open>M' \<union> N' = UNIV\<close>
      then have \<open>sound_cons.entails_neg (fml_ext ` total_strip J) (Pos ` N')\<close>
        using J_entails_neg_bot
        by (smt (verit, del_insts) Un_upper2 consequence_relation.entails_subsets imageI insert_subset
                                   sound_cons.ext_cons_rel subsetI sup_bot.right_neutral)
      then have \<open>sound_cons.entails_neg (Pos ` M') (Pos ` N')\<close>
        (* TODO: I'm missing a few steps here *)
        sorry
      moreover have [simp]: \<open>{ C. Neg C \<in> Pos ` A } = {}\<close> for A
        by blast
      moreover have \<open>{ x. Pos x \<in> Pos ` A } = A\<close> for A
        (* Not sure why this needs to be stated explicitly, but sledgehammer does not find a proof
         * for the “ultimately” case if not. *)
        by blast
      ultimately show \<open>M' \<Turnstile>s N'\<close>
        unfolding sound_cons.entails_neg_def
        by (metis sup_bot_right)
    qed
    then show \<open>{} \<Turnstile>s {bot}\<close>
      by (rule sound_cons.entails_supsets[of \<open>{}\<close> \<open>{bot}\<close>])
  qed
  then show \<open>\<C> \<in> SRed\<^sub>F \<M>\<close>
    unfolding SRed\<^sub>F_def enabled_def
    using ex_enabled_in_\<M>
    by (smt (verit, ccfv_threshold) AF.collapse UnI1 enabled_def entails_sound_nontrivial mem_Collect_eq
                                    sound_cons.entails_bot_to_entails_empty)
next
  assume \<open>trim_pre \<C> A B \<M>\<close>
  then have A_of_\<C>_is: \<open>A_of \<C> = A |\<union>| B\<close> and
            \<open>F_of \<C> \<noteq> bot\<close> and
            \<M>_and_A_entail_bot_B: \<open>\<M> \<union> { AF.Pair bot A } \<Turnstile>s\<^sub>A\<^sub>F { AF.Pair bot B }\<close> and
            \<open>\<forall> \<C> \<in> \<M>. F_of \<C> = bot\<close> and
            A_B_disjoint: \<open>A |\<inter>| B = {||}\<close> and
            A_not_empty: \<open>A \<noteq> {||}\<close>
    by blast+
  then show \<open>\<C> \<in> SRed\<^sub>F (\<M> \<union> { AF.Pair (F_of \<C>) B })\<close>
    unfolding SRed\<^sub>F_def
    (* /!\ A little bit slow /!\ *)
    by (intro UnI2)
       (smt (verit, best) AF.collapse AF.sel(1) AF.sel(2) CollectI Un_insert_right inf_sup_absorb insertCI
                          order_le_imp_less_or_eq sup.cobounded2)
qed

end (* locale splitting_calculus_with_simps *)

text \<open>
  We extend our basic splitting calculus with new optional rules: \textsc{StrongUnsat}, \textsc{Approx} and \textsc{Tauto}.
\<close>

locale splitting_calculus_extensions =
  splitting_calculus bot Inf entails entails_sound Red_I Red_F V fml
  for bot :: 'f and
      Inf :: \<open>'f inference set\<close> and
      entails :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) and
      entails_sound :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>s\<close> 50) and
      Red_I :: \<open>'f set \<Rightarrow> 'f inference set\<close> and
      Red_F :: \<open>'f set \<Rightarrow> 'f set\<close> and
      V :: \<open>'v :: countable itself\<close> and
      fml :: \<open>'v \<Rightarrow> 'f\<close>
  + fixes asn :: \<open>'f \<Rightarrow> 'v sign set\<close>
    assumes
      fml_entails_C: \<open>fml_ext ` asn C \<Turnstile>\<^sub>\<sim> {Pos C}\<close> and
      C_entails_fml: \<open>{Pos C} \<Turnstile>\<^sub>\<sim> fml_ext ` asn C\<close> and
      asn_not_empty: \<open>asn C \<noteq> {}\<close>
begin

abbreviation strong_unsat_pre :: \<open>('f, 'v) AF list \<Rightarrow> bool\<close> where
  \<open>strong_unsat_pre \<M> \<equiv> set \<M> \<Turnstile>s\<^sub>A\<^sub>F {to_AF bot} \<and> (\<forall> x \<in> set \<M>. F_of x = bot)\<close>

abbreviation strong_unsat_inf :: \<open>('f, 'v) AF list \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>strong_unsat_inf \<M> \<equiv> Infer \<M> (to_AF bot)\<close>

abbreviation tauto_pre :: \<open>('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>tauto_pre \<C> \<equiv> {} \<Turnstile>s\<^sub>A\<^sub>F { \<C> }\<close>

abbreviation tauto_inf :: \<open>('f, 'v) AF \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>tauto_inf \<C> \<equiv> Infer [] \<C>\<close>

abbreviation approx_pre :: \<open>'v sign \<Rightarrow> ('f, 'v) AF \<Rightarrow> bool\<close> where
  \<open>approx_pre a \<C> \<equiv> a \<in> asn (F_of \<C>)\<close>

abbreviation approx_inf :: \<open>('f, 'v) AF \<Rightarrow> 'v sign \<Rightarrow> ('f, 'v) AF inference\<close> where
  \<open>approx_inf \<C> a \<equiv> Infer [\<C>] (AF.Pair bot (finsert (neg a) (A_of \<C>)))\<close>

inductive Splitting_rules2 :: \<open>('f, 'v) AF inference \<Rightarrow> bool\<close> where
  strong_unsat: \<open>strong_unsat_pre \<M> \<Longrightarrow> Splitting_rules2 (strong_unsat_inf \<M>)\<close> |
  tauto: \<open>tauto_pre \<C> \<Longrightarrow> Splitting_rules2 (tauto_inf \<C>)\<close> |
  approx: \<open>approx_pre a \<C> \<Longrightarrow> Splitting_rules2 (approx_inf \<C> a)\<close>

abbreviation SInf2 :: \<open>('f, 'v) AF inference set\<close> where
  \<open>SInf2 \<equiv> SInf \<union> {\<iota>. Splitting_rules2 \<iota>}\<close>

(* Report theorem 14 (cont) *)
theorem SInf2_sound_wrt_entails_sound: \<open>\<iota> \<in> SInf2 \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>s\<^sub>A\<^sub>F {concl_of \<iota>}\<close>
  sorry

interpretation SInf2_sound_inf_system: sound_inference_system SInf2 \<open>to_AF bot\<close> \<open>(\<Turnstile>s\<^sub>A\<^sub>F)\<close>
  sorry
  (* by (standard, auto simp add: SInf2_sound_wrt_entails_sound) *)
  (* Right... we need the interpretation here too... *)

end (* locale splitting_calculus_extensions *)

subsection \<open>Standard saturation\<close>

context splitting_calculus
begin

alias S_saturated = S_calculus.saturated
alias F_saturated = local.saturated

lemma F_of_circ_to_AF_is_id [simp]: \<open>F_of \<circ> to_AF = id\<close>
  by fastforce

lemma A_of_circ_to_AF_is_empty_set [simp]: \<open>A_of \<circ> to_AF = (\<lambda> _. {||})\<close>
  by fastforce

lemma map_A_of_map2_Pair: \<open>length A = length B \<Longrightarrow> map A_of (map2 AF.Pair A B) = B\<close>
  by auto

lemma ball_set_f_to_ball_set_map: \<open>(\<forall> x \<in> set A. P (f x)) \<longleftrightarrow> (\<forall> x \<in> set (map f A). P x)\<close>
  by simp

lemma list_all_ex_to_ex_list_all2:
  \<open>list_all (\<lambda> x. \<exists> y. P x y) A \<longleftrightarrow> (\<exists> ys. length A = length ys \<and> list_all2 (\<lambda> x y. P x y) A ys)\<close>
  by (metis list_all2_conv_all_nth list_all_exists_is_exists_list_all2 list_all_length)

lemma list_all2_to_map:
  assumes lengths_eq: \<open>length A = length B\<close>
  shows \<open>list_all2 (\<lambda> x y. P (f x y)) A B \<longleftrightarrow> list_all P (map2 f A B)\<close>
proof -
  have \<open>list_all2 (\<lambda> x y. P (f x y)) A B \<longleftrightarrow> list_all (\<lambda> (x, y). P (f x y)) (zip A B)\<close>
    by (simp add: lengths_eq list_all2_iff list_all_iff)
  also have \<open>... \<longleftrightarrow> list_all (\<lambda> x. P x) (map2 f A B)\<close>
    by (simp add: case_prod_beta list_all_iff)
  finally show ?thesis .
qed

(* Report lemma 20 *)
lemma S_saturated_to_F_saturated: \<open>S_saturated \<N> \<Longrightarrow> F_saturated (\<N> proj\<^sub>J \<J>)\<close>
proof -
  assume \<N>_is_S_saturated: \<open>S_calculus.saturated \<N>\<close>
  then show \<open>saturated (\<N> proj\<^sub>J \<J>)\<close>
    unfolding saturated_def S_calculus.saturated_def
  proof (intro subsetI)
    fix \<iota>\<^sub>F
    assume \<open>\<iota>\<^sub>F \<in> Inf_from (\<N> proj\<^sub>J \<J>)\<close>
    then have \<iota>\<^sub>F_is_Inf: \<open>\<iota>\<^sub>F \<in> Inf\<close> and
              prems_of_\<iota>\<^sub>F_in_\<N>_proj_\<J>: \<open>set (prems_of \<iota>\<^sub>F) \<subseteq> \<N> proj\<^sub>J \<J>\<close>
      unfolding Inf_from_def
      by auto
    moreover have \<open>\<forall> C \<in> set (prems_of \<iota>\<^sub>F). \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> enabled \<C> \<J>\<close>
      using prems_of_\<iota>\<^sub>F_in_\<N>_proj_\<J>
      unfolding enabled_projection_def
      by blast
    then have \<open>list_all (\<lambda> C. \<exists> \<C> \<in> \<N>. F_of \<C> = C \<and> enabled \<C> \<J>) (prems_of \<iota>\<^sub>F)\<close>
      using Ball_set
      by blast
    then have \<open>\<exists> \<C>s. length \<C>s = length (prems_of \<iota>\<^sub>F) \<and>
                     list_all2 (\<lambda> C \<C>. \<C> \<in> \<N> \<and> F_of \<C> = C \<and> enabled \<C> \<J>) (prems_of \<iota>\<^sub>F) \<C>s\<close>
      using list_all_ex_to_ex_list_all2
      by (smt (verit, best) Ball_set)
    then have \<open>\<exists> As. length As = length (prems_of \<iota>\<^sub>F) \<and>
                     list_all2 (\<lambda> C A. AF.Pair C A \<in> \<N> \<and> enabled (AF.Pair C A) \<J>) (prems_of \<iota>\<^sub>F) As\<close>
      by (smt (verit, del_insts) AF.exhaust AF.sel(1) list.pred_mono_strong list_all_ex_to_ex_list_all2)
    then have \<open>\<exists> As. length As = length (prems_of \<iota>\<^sub>F) \<and>
                     list_all (\<lambda> \<C>. \<C> \<in> \<N> \<and> enabled \<C> \<J>) (map2 AF.Pair (prems_of \<iota>\<^sub>F) As)\<close>
      using list_all2_to_map[where f = \<open>\<lambda> C A. AF.Pair C A\<close>]
      by (smt (verit) list_all2_mono)
    then obtain As :: \<open>'v sign fset list\<close>
                   where \<open>\<forall> \<C> \<in> set (map2 AF.Pair (prems_of \<iota>\<^sub>F) As). \<C> \<in> \<N> \<and> enabled \<C> \<J>\<close> and
                         length_As_eq_length_prems: \<open>length As = length (prems_of \<iota>\<^sub>F)\<close>
      by (metis (no_types, lifting) Ball_set_list_all)
    then have set_prems_As_subset_\<N>: \<open>set (map2 AF.Pair (prems_of \<iota>\<^sub>F) As) \<subseteq> \<N>\<close> and
              all_enabled: \<open>\<forall> \<C> \<in> set (map2 AF.Pair (prems_of \<iota>\<^sub>F) As). enabled \<C> \<J>\<close>
      by auto

    let ?prems = \<open>map2 AF.Pair (prems_of \<iota>\<^sub>F) As\<close>

    have \<open>set ?prems \<subseteq> \<N>\<close>
      using set_prems_As_subset_\<N> .
    moreover have \<open>length ?prems = length (prems_of \<iota>\<^sub>F)\<close>
      using length_As_eq_length_prems
      by simp
    then have F_of_dummy_prems_is_prems_of_\<iota>\<^sub>F: \<open>map F_of ?prems = prems_of \<iota>\<^sub>F\<close>
      by (simp add: length_As_eq_length_prems)
    moreover have \<open>\<forall> \<C> \<in> set (map A_of (map2 AF.Pair (prems_of \<iota>\<^sub>F) As)). fset \<C> \<subseteq> total_strip \<J>\<close>
      using all_enabled ball_set_f_to_ball_set_map[where P = \<open>\<lambda> x. fset x \<subseteq> total_strip \<J>\<close> and f = A_of]
      unfolding enabled_def
      by blast
    then have \<open>\<forall> \<C> \<in> set As. fset \<C> \<subseteq> total_strip \<J>\<close>
      using map_A_of_map2_Pair length_As_eq_length_prems
      by metis
    then have \<open>fset (ffUnion (fset_of_list As)) \<subseteq> total_strip \<J>\<close>
      using all_enabled
      unfolding enabled_def[of _ \<J>]
      by (simp add: fBall_fset_of_list_iff_Ball_set fset_ffUnion_subset_iff_all_fsets_subset)
    then have base_inf_enabled: \<open>enabled_inf (base_inf ?prems (concl_of \<iota>\<^sub>F)) \<J>\<close>
      using all_enabled enabled_inf_def
      by auto
    moreover have pre_holds: \<open>base_pre ?prems (concl_of \<iota>\<^sub>F)\<close>
      using \<iota>\<^sub>F_is_Inf F_of_dummy_prems_is_prems_of_\<iota>\<^sub>F
      by force
    moreover have \<iota>F_of_base_inf_is_\<iota>\<^sub>F: \<open>\<iota>F_of (base_inf ?prems (concl_of \<iota>\<^sub>F)) = \<iota>\<^sub>F\<close>
      using F_of_dummy_prems_is_prems_of_\<iota>\<^sub>F \<iota>F_of_def
      by force
    ultimately have \<iota>\<^sub>F_in_Inf_\<N>_proj_\<J>: \<open>\<iota>\<^sub>F \<in> (S_calculus.Inf_from \<N>) \<iota>proj\<^sub>J \<J>\<close>
      using Splitting_rules.base[OF pre_holds]
      unfolding enabled_projection_Inf_def S_calculus.Inf_from_def
      by (metis (mono_tags, lifting) inference.sel(1) mem_Collect_eq)
    then have \<open>\<exists> \<M> D. base_inf \<M> D \<in> S_calculus.Inf_from \<N> \<and> \<iota>F_of (base_inf \<M> D) = \<iota>\<^sub>F \<and> enabled_inf (base_inf \<M> D) \<J>\<close>
      using \<iota>F_of_base_inf_is_\<iota>\<^sub>F
      unfolding enabled_projection_Inf_def
      by (metis (mono_tags, lifting) CollectI S_calculus.Inf_from_def Splitting_rules.base base_inf_enabled
                                     inference.sel(1) pre_holds set_prems_As_subset_\<N>)
    then obtain \<M> D where base_inf_in_Inf_\<N>: \<open>base_inf \<M> D \<in> S_calculus.Inf_from \<N>\<close> and
                           \<iota>F_of_base_inf_is_\<iota>\<^sub>F: \<open>\<iota>F_of (base_inf \<M> D) = \<iota>\<^sub>F\<close> and
                           base_inf_enabled: \<open>enabled_inf (base_inf \<M> D) \<J>\<close>
      by blast
    then have \<open>base_inf \<M> D \<in> SRed\<^sub>I \<N>\<close>
      using \<N>_is_S_saturated
      unfolding S_calculus.saturated_def
      by blast
    moreover have \<open>base_pre \<M> D\<close>
      using \<iota>F_of_base_inf_is_\<iota>\<^sub>F \<iota>\<^sub>F_is_Inf
      by (simp add: \<iota>F_of_def)
    ultimately show \<open>\<iota>\<^sub>F \<in> Red_I (\<N> proj\<^sub>J \<J>)\<close>
      using \<iota>\<^sub>F_in_Inf_\<N>_proj_\<J> \<iota>F_of_base_inf_is_\<iota>\<^sub>F base_inf_enabled
      unfolding SRed\<^sub>I_def enabled_projection_Inf_def \<iota>F_of_def enabled_def enabled_projection_def
      by auto
         (metis (mono_tags, lifting) AF.sel(2) F_of_to_AF Red_I_of_Inf_to_N bot_fset.rep_eq empty_subsetI
                                     inference.sel(2) mem_Collect_eq to_AF_def)
  qed
qed

lemma prop_unsat_to_AF_entails_bot: \<open>propositionally_unsatisfiable \<M> \<Longrightarrow> \<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
proof -
  assume prop_unsat_\<M>: \<open>propositionally_unsatisfiable \<M>\<close>
  then show \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    unfolding AF_entails_def
  proof (intro allI impI)
    fix J
    assume \<open>enabled_set {to_AF bot} J\<close>
    have \<open>bot \<in> (proj\<^sub>\<bottom> \<M>) proj\<^sub>J J\<close>
      using prop_unsat_\<M>
      unfolding propositionally_unsatisfiable_def propositional_model_def
      by blast
    then have \<open>bot \<in> \<M> proj\<^sub>J J\<close>
      using enabled_projection_def prop_proj_in
      by fastforce
    then have \<open>\<M> proj\<^sub>J J \<Turnstile> {bot}\<close>
      using bot_entails_empty entails_subsets
      by (meson empty_subsetI insert_subset)
    then show \<open>\<M> proj\<^sub>J J \<Turnstile> F_of ` {to_AF bot}\<close>
      by auto
  qed
qed

(* lemma AF_entails_bot_to_prop_unsat: \<open>(\<forall> x \<in> \<M>. F_of x = bot) \<Longrightarrow> \<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot} \<Longrightarrow> propositionally_unsatisfiable \<M>\<close>
proof -
  assume all_heads_are_bot_in_\<M>: \<open>\<forall> x \<in> \<M>. F_of x = bot\<close> and
         \<open>\<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  then have \<open>\<forall> J. \<M> proj\<^sub>J J \<Turnstile> {bot}\<close>
    unfolding AF_entails_def
    by (metis F_of_to_AF enabled_to_AF_set image_empty image_insert)
  moreover have \<open>proj\<^sub>\<bottom> \<M> = \<M>\<close>
    using all_heads_are_bot_in_\<M>
    unfolding propositional_projection_def
    by blast
  then have \<open>\<forall> J. bot \<in> \<M> proj\<^sub>J J\<close>
    using entails_nontrivial
    unfolding enabled_projection_def
    by (metis calculation enabled_projection_def entails_bot_to_entails_empty equiv_prop_entails
              propositional_model2_def propositional_model_def)
  then have \<open>\<forall> J. \<not> (J \<Turnstile>\<^sub>p \<M>)\<close>
    using \<open>proj\<^sub>\<bottom> \<M> = \<M>\<close>
    unfolding propositional_model_def
    by auto
  then show \<open>propositionally_unsatisfiable \<M>\<close>
    unfolding propositionally_unsatisfiable_def .
qed *)

lemma Union_empty_if_set_empty_or_all_empty: \<open>ffUnion A = {||} \<Longrightarrow> A = {||} \<or> fBall A (\<lambda> x. x = {||})\<close>
  by (metis (mono_tags, lifting) fBallI ffunion_insert finsert_absorb funion_fempty_right)

lemma fBall_fimage_is_fBall: \<open>fBall (f |`| A) P \<longleftrightarrow> fBall A (\<lambda> x. P (f x))\<close>
  by auto

lemma prop_unsat_compactness: \<open>propositionally_unsatisfiable A \<Longrightarrow> \<exists> B \<subseteq> A. finite B \<and> propositionally_unsatisfiable B\<close>
  by (meson compactness_AF_proj equiv_prop_entails propositionally_unsatisfiable_def)

(* Report theorem 21 *)
theorem S_calculus_statically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close>
  shows \<open>statically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
  using F_statically_complete
  unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
proof (intro conjI allI impI; elim conjE)
  show \<open>Preliminaries_With_Zorn.calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
    using S_calculus.calculus_axioms
    by blast
next
  fix N
  assume \<open>Preliminaries_With_Zorn.calculus bot Inf (\<Turnstile>) Red_I Red_F\<close> and
         if_F_saturated_and_N_entails_bot_then_bot_in_N: \<open>\<forall> N. F_saturated N \<longrightarrow> N \<Turnstile> {bot} \<longrightarrow> bot \<in> N\<close> and
         N_is_S_saturated: \<open>S_saturated N\<close> and
         N_entails_bot: \<open>N \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
  then have N_proj_\<J>_entails_bot: \<open>\<forall> \<J>. N proj\<^sub>J \<J> \<Turnstile> {bot}\<close>
    unfolding AF_entails_def
    using F_of_to_AF[of bot]
    by (smt (verit) enabled_to_AF_set image_empty image_insert)
  then have N_proj_\<J>_F_saturated: \<open>\<forall> \<J>. F_saturated (N proj\<^sub>J \<J>)\<close>
    using N_is_S_saturated
    using S_saturated_to_F_saturated
    by blast
  then have \<open>\<forall> \<J>. bot \<in> N proj\<^sub>J \<J>\<close>
    using N_proj_\<J>_entails_bot if_F_saturated_and_N_entails_bot_then_bot_in_N
    by presburger
  then have prop_proj_N_is_prop_unsat: \<open>propositionally_unsatisfiable (proj\<^sub>\<bottom> N)\<close>
    unfolding enabled_projection_def propositional_model_def propositional_projection_def propositionally_unsatisfiable_def
    by fast
  then have \<open>proj\<^sub>\<bottom> N \<noteq> {}\<close>
    unfolding propositionally_unsatisfiable_def propositional_model_def
    using enabled_projection_def prop_proj_in
    by auto
  then have \<open>\<exists> \<M>. set \<M> \<subseteq> proj\<^sub>\<bottom> N \<and> finite (set \<M>) \<and> propositionally_unsatisfiable (set \<M>)\<close>
    by (metis finite_list prop_proj_N_is_prop_unsat prop_unsat_compactness)
  then obtain \<M> where \<M>_subset_prop_proj_N: \<open>set \<M> \<subseteq> proj\<^sub>\<bottom> N\<close> and
                       \<M>_subset_N: \<open>set \<M> \<subseteq> N\<close> and
                       \<open>finite (set \<M>)\<close> and
                       \<M>_prop_unsat: \<open>propositionally_unsatisfiable (set \<M>)\<close> and
                       \<M>_not_empty: \<open>\<M> \<noteq> []\<close>
    by (smt (verit, del_insts) AF_cons_rel.entails_bot_to_entails_empty AF_cons_rel.entails_empty_reflexive_dangerous
                               compactness_AF_proj equiv_prop_entails finite_list image_empty prop_proj_N_is_prop_unsat
                               prop_proj_in propositional_model2_def propositionally_unsatisfiable_def set_empty2
                               subset_empty subset_trans to_AF_proj_J)
(*  then have \<open>\<exists> \<M>. set \<M> \<subseteq> proj\<^sub>\<bottom> N \<and> finite (set \<M>) \<and> set \<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close>
    using AF_cons_rel.entails_compactness[of \<open>proj\<^sub>\<bottom> N\<close> \<open>{to_AF bot}\<close>]
    by (metis (no_types, lifting) AF_cons_rel.entails_subsets finite_list prop_proj_N_is_prop_unsat
                                  prop_unsat_to_AF_entails_bot subset_refl)
  then obtain \<M> where \<M>_subset_prop_proj_N: \<open>set \<M> \<subseteq> proj\<^sub>\<bottom> N\<close> and
                       \<M>_subset_N: \<open>set \<M> \<subseteq> N\<close> and
                       \<open>finite (set \<M>)\<close> and
                       \<M>_entails_bot: \<open>set \<M> \<Turnstile>\<^sub>A\<^sub>F {to_AF bot}\<close> and
                       \<M>_not_empty: \<open>\<M> \<noteq> []\<close>
    by (smt (verit, del_insts) AF_cons_rel.entails_bot_to_entails_empty AF_cons_rel.entails_empty_reflexive_dangerous
                               compactness_AF_proj equiv_prop_entails finite_list image_empty prop_proj_N_is_prop_unsat
                               prop_proj_in propositional_model2_def propositionally_unsatisfiable_def set_empty2
                               subset_empty subset_trans to_AF_proj_J) *)
(*  then have \<M>_prop_unsat: \<open>propositionally_unsatisfiable (set \<M>)\<close>
    by (simp add: AF_entails_bot_to_prop_unsat propositional_projection_def subset_iff) *)
  then have \<open>unsat_inf \<M> \<in> S_calculus.Inf_from N\<close> and
            Infer_\<M>_bot_in_SInf: \<open>unsat_inf \<M> \<in> SInf\<close>
    using \<M>_not_empty \<M>_subset_prop_proj_N Splitting_rules.unsat S_calculus.Inf_if_Inf_from
    unfolding S_calculus.Inf_from_def propositionally_unsatisfiable_def propositional_model_def propositional_projection_def
    by fastforce+
  then have \<open>unsat_inf \<M> \<in> SRed\<^sub>I N\<close>
    using N_is_S_saturated S_calculus.saturated_def
    by blast
  then show \<open>to_AF bot \<in> N\<close>
    unfolding SRed\<^sub>I_def
  proof (elim UnE)
    assume \<open>unsat_inf \<M> \<in> { base_inf \<M> \<C> | \<M> \<C>. base_pre \<M> \<C> \<and> (\<forall> \<J>. { base_inf \<M> \<C> } \<iota>proj\<^sub>J \<J> \<subseteq> Red_I (N proj\<^sub>J \<J>)) }\<close>
    then have \<open>unsat_inf \<M> = base_inf \<M> bot\<close>
      by (smt (verit, best) AF.exhaust_sel AF.sel(2) F_of_to_AF inference.inject mem_Collect_eq)
    then have \<open>to_AF bot = AF.Pair bot (ffUnion (A_of |`| fset_of_list \<M>))\<close>
      by simp
    then have \<open>ffUnion (A_of |`| fset_of_list \<M>) = {||}\<close>
      by (metis AF.sel(2) A_of_to_AF)
    then consider (\<M>_empty) \<open>A_of |`| fset_of_list \<M> = {||}\<close> |
                  (no_assertions_in_\<M>) \<open>fBall (A_of |`| fset_of_list \<M>) (\<lambda> x. x = {||})\<close>
      using Union_empty_if_set_empty_or_all_empty
      by auto
    then show ?thesis
    proof (cases)
      case \<M>_empty
      then have \<open>fset_of_list \<M> = {||}\<close>
        by blast
      then have \<open>\<M> = []\<close>
        by (metis bot_fset.rep_eq fset_of_list.rep_eq set_empty2)
      then show ?thesis
        using \<M>_not_empty
        by contradiction
    next
      case no_assertions_in_\<M>
      then have \<open>fBall (fset_of_list \<M>) (\<lambda> x. A_of x = {||})\<close>
        using fBall_fimage_is_fBall
        by simp
      then have \<open>\<forall> x \<in> set \<M>. A_of x = {||}\<close>
        using fBall_fset_of_list_iff_Ball_set
        by meson
      then have \<open>to_AF bot \<in> set \<M>\<close>
        using \<M>_subset_prop_proj_N \<M>_not_empty
        unfolding propositional_projection_def to_AF_def
        by (metis (mono_tags, lifting) AF.exhaust_sel CollectD ex_in_conv set_empty subset_code(1))
      then show ?thesis
        using \<M>_subset_N
        by blast
    qed
  next
    assume \<open>unsat_inf \<M> \<in> { unsat_inf \<M> | \<M>. unsat_pre \<M> \<and> to_AF bot \<in> N }\<close>
    then show ?thesis
      by fastforce
  qed
qed

(* lemma cons_rel_equiv:
  shows \<open>Preliminaries_With_Zorn.consequence_relation (to_AF bot) (⊨\<^sub>A\<^sub>F) =
         Calculus.consequence_relation {bot} (\<Turnstile>\<inter>)\<close>
  sorry

lemma calculus_equiv:
  shows \<open>Preliminaries_With_Zorn.calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F =
         Calculus.calculus {bot} Inf (\<Turnstile>\<inter>) Red_I Red_F\<close>
  unfolding Preliminaries_With_Zorn.calculus_def Calculus.calculus_def
            Preliminaries_With_Zorn.calculus_axioms_def Calculus.calculus_axioms_def
  using Red_F_Bot cons_rel_equiv lift_from_ARed_to_FRed.ground.Red_F_Bot
  sorry

lemma statically_complete_calculus_equiv:
  shows \<open>Preliminaries_With_Zorn.statically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F =
         Calculus.statically_complete_calculus {bot} Inf (\<Turnstile>\<inter>) Red_I Red_F\<close>
  unfolding Calculus.statically_complete_calculus_def Preliminaries_With_Zorn.statically_complete_calculus_def
            Calculus.statically_complete_calculus_axioms_def Preliminaries_With_Zorn.statically_complete_calculus_axioms_def
  using calculus_equiv
  sorry

lemma dynamically_complete_calculus_equiv:
  shows \<open>Preliminaries_With_Zorn.dynamically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F =
         Calculus.dynamically_complete_calculus {bot} Inf (\<Turnstile>\<inter>) Red_I Red_F\<close>
  unfolding Preliminaries_With_Zorn.dynamically_complete_calculus_def Calculus.dynamically_complete_calculus_def
            Preliminaries_With_Zorn.dynamically_complete_calculus_axioms_def Calculus.dynamically_complete_calculus_axioms_def
  using calculus_equiv
  sorry  *)

corollary S_calculus_dynamically_complete:
  assumes F_statically_complete: \<open>statically_complete_calculus bot Inf (\<Turnstile>) Red_I Red_F\<close>
  shows \<open>dynamically_complete_calculus (to_AF bot) SInf (\<Turnstile>\<^sub>A\<^sub>F) SRed\<^sub>I SRed\<^sub>F\<close>
  (* We'd want to use Calculus_Variations.calculus.dyn_equiv_stat here *)
  sorry

(* @{const Calculus_Variations.calculus.dyn_equiv_stat} states that static and dynamic completeness are equivalent.
 *
 * In our case though, our definition of a calculus does not conform to this one's.
 * So we'd need to prove that both calculi are equivalent.
 *
 * Here's a small problem: the former calculi uses a *conjunctive* entailment, where the latter uses a *disjunctive* entailment.
 *
 * In our proof, we use \<Turnstile>\<^sub>A\<^sub>F (which degenerates to \<Turnstile> on F-formulas, not on \<Turnstile>\<inter>).
 * So we would need to prove the equivalence between both calculi with \<Turnstile>\<inter> (it will not be possible otherwise), but then
 * we'd get stuck because we are using \<Turnstile> not \<Turnstile>\<inter>. *)

subsection \<open>Local saturation\<close>

end (* context splitting_calculus *)

end (* theory Splitting_Calculi *)
