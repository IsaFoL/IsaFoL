theory Abstract_Renaming_Apart
  imports Main
begin

section \<open>Abstract Renaming\<close>

locale renaming_apart =
  fixes
    renaming :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    renaming_correct: "finite V \<Longrightarrow> renaming V x \<notin> V" and
    inj_renaming: "finite V \<Longrightarrow> inj (renaming V)"


subsection \<open>Interpretation to Prove That Assumptions Are Consistent\<close>

experiment begin

definition renaming_apart_nats where
  "renaming_apart_nats V = (let m = Max V in (\<lambda>x. Suc (x + m)))"

interpretation renaming_apart_nats: renaming_apart renaming_apart_nats
proof unfold_locales
  show "\<And>V x. finite V \<Longrightarrow> renaming_apart_nats V x \<notin> V"
    unfolding renaming_apart_nats_def Let_def by (meson Max.coboundedI Suc_le_lessD not_add_less2)
next
  show "\<And>V. inj (renaming_apart_nats V)"
    unfolding renaming_apart_nats_def Let_def by (rule injI) simp
qed

end

end