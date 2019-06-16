theory WB_Sort_SML
  imports WB_Sort WB_More_IICF_SML
begin

named_theorems isasat_codegen

lemma swap_match[isasat_codegen]: \<open>WB_More_Refinement_List.swap = IICF_List.swap\<close>
  by (auto simp: WB_More_Refinement_List.swap_def IICF_List.swap_def intro!: ext)

sepref_register choose_pivot3

text \<open>Example instantiation code for pivot\<close>
sepref_definition choose_pivot3_impl_code
  is \<open>uncurry2 (choose_pivot3_impl)\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>k  *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k\<rightarrow>\<^sub>a nat_assn\<close>
  unfolding choose_pivot3_impl_def choose_pivot3_def id_def
  by sepref

declare choose_pivot3_impl_code.refine[sepref_fr_rules]



text \<open>Example instantiation for \<^term>\<open>partition_main\<close>\<close>
definition partition_main_impl where
  \<open>partition_main_impl = partition_main (\<le>) id\<close>

sepref_register partition_main_impl

text \<open>Example instantiation code for \<^term>\<open>partition_main\<close>\<close>
sepref_definition partition_main_code
  is \<open>uncurry2 (partition_main_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_main_impl_def partition_main_def
    id_def isasat_codegen
  by sepref

declare partition_main_code.refine[sepref_fr_rules]


text \<open>Example instantiation for partition\<close>
definition partition_between_impl where
  \<open>partition_between_impl = partition_between_ref (\<le>) id\<close>

sepref_register partition_between_ref

text \<open>Example instantiation code for partition\<close>
sepref_definition partition_between_code
  is \<open>uncurry2 (partition_between_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_between_ref_def partition_between_impl_def
    choose_pivot3_impl_def[symmetric] partition_main_impl_def[symmetric]
  unfolding  id_def isasat_codegen
  by sepref

declare partition_between_code.refine[sepref_fr_rules]


\<comment> \<open>Example implementation\<close>
definition quicksort_impl where
  \<open>quicksort_impl a b c \<equiv> quicksort_ref (\<le>) id (a,b,c)\<close>

sepref_register quicksort_impl

\<comment> \<open>Example implementation code\<close>
sepref_definition
  quicksort_code
  is \<open>uncurry2 quicksort_impl\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding partition_between_impl_def[symmetric]
    quicksort_impl_def quicksort_ref_def
  by sepref

declare quicksort_code.refine[sepref_fr_rules]

text \<open>Executable code for the example instance\<close>
sepref_definition full_quicksort_code
  is \<open>full_quicksort_impl\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding full_quicksort_impl_def full_quicksort_ref_def quicksort_impl_def[symmetric] List.null_def
  by sepref

text \<open>Export the code\<close>
export_code \<open>nat_of_integer\<close> \<open>integer_of_nat\<close> \<open>partition_between_code\<close> \<open>full_quicksort_code\<close> in SML_imp module_name IsaQuicksort file "code/quicksort.sml"

end