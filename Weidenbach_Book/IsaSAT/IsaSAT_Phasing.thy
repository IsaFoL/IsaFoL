theory IsaSAT_Phasing
  imports IsaSAT_Literals
begin

subsection \<open>Phase saving\<close>

type_synonym phase_saver = \<open>bool list\<close>

definition phase_saving :: \<open>nat multiset \<Rightarrow> phase_saver \<Rightarrow> bool\<close> where
\<open>phase_saving \<A> \<phi> \<longleftrightarrow> (\<forall>L\<in>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>). L < length \<phi>)\<close>

text \<open>Save phase as given (e.g. for literals in the trail):\<close>
definition save_phase :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase L \<phi> = \<phi>[atm_of L := is_pos L]\<close>

lemma phase_saving_save_phase[simp]:
  \<open>phase_saving \<A> (save_phase L \<phi>) \<longleftrightarrow> phase_saving \<A> \<phi>\<close>
  by (auto simp: phase_saving_def save_phase_def)

text \<open>Save opposite of the phase (e.g. for literals in the conflict clause):\<close>
definition save_phase_inv :: \<open>nat literal \<Rightarrow> phase_saver \<Rightarrow> phase_saver\<close> where
  \<open>save_phase_inv L \<phi> = \<phi>[atm_of L := \<not>is_pos L]\<close>
 
end
