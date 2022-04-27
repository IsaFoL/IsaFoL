theory Abstract_Renaming_Apart
  imports Main
begin

section \<open>Abstract Renaming\<close>

locale renaming_apart =
  fixes
    renaming :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a" and
    inv_renaming :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    renaming_all: "finite V \<Longrightarrow> renaming V x \<noteq> x" and
    renaming_correct: "finite V \<Longrightarrow> renaming V x \<notin> V" and
    inj_renaming: "finite V \<Longrightarrow> inj (renaming V)" and
    inv_renaming_correct: "finite V \<Longrightarrow> inv_renaming V (renaming V x) = x" and
    inv_renaming_idem: "finite V \<Longrightarrow> x \<in> V \<Longrightarrow> inv_renaming V x = x"


subsubsection \<open>Interpretation to Prove That Assumptions Are Consistent\<close>

experiment begin

definition renaming_apart_nats where
  "renaming_apart_nats V = (let m = Max V in (\<lambda>x. Suc (x + m)))"

definition inv_renaming_apart_nats where
  "inv_renaming_apart_nats V = (let m = Max V in (\<lambda>x. if x \<in> V then x else x - m - 1))"

interpretation renaming_apart_nats: renaming_apart renaming_apart_nats
  inv_renaming_apart_nats
proof unfold_locales
  show "\<And>V x. finite V \<Longrightarrow> renaming_apart_nats V x \<noteq> x"
    by (simp add: renaming_apart_nats_def)
next
  show "\<And>V x. finite V \<Longrightarrow> renaming_apart_nats V x \<notin> V"
    unfolding renaming_apart_nats_def Let_def by (meson Max.coboundedI Suc_le_lessD not_add_less2)
next
  show "\<And>V. finite V \<Longrightarrow> inj (renaming_apart_nats V)"
    unfolding renaming_apart_nats_def Let_def by (rule injI) simp
next
  show "\<And>V x. finite V \<Longrightarrow> inv_renaming_apart_nats V (renaming_apart_nats V x) = x"
  unfolding inv_renaming_apart_nats_def
  apply (simp add: Let_def)
  by (metis Max.coboundedI add_Suc_right add_diff_cancel_right' diff_is_0_eq' nat.simps(3)
      plus_nat.simps(2) renaming_apart_nats_def)
next
  show "\<And>V x. finite V \<Longrightarrow> x \<in> V \<Longrightarrow> inv_renaming_apart_nats V x = x"
    unfolding inv_renaming_apart_nats_def
    by (simp add: Let_def)
qed

end

end