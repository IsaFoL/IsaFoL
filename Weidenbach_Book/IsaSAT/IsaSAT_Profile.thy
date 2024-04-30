theory IsaSAT_Profile
  imports IsaSAT_Literals
begin

chapter \<open>Profiling\<close>

text \<open>For profiling, we don't do anything except calling some C functions to measure time. As for
printing, the functions to nothing in the refinement and are only removed from the generated code.
The aim is to better understand the behaviour of the generated code and find performance bug.
\<close>
context
begin
  qualified definition start :: \<open>8 word \<Rightarrow> unit\<close> where \<open>start a = ()\<close>
  qualified definition stop :: \<open>8 word \<Rightarrow> unit\<close> where \<open>stop a = ()\<close>
  qualified definition PROPAGATE :: \<open>8 word\<close> where \<open>PROPAGATE = 0\<close>
  qualified definition ANALYZE :: \<open>8 word\<close> where \<open>ANALYZE = 1\<close>
  qualified definition GC :: \<open>8 word\<close> where \<open>GC = 2\<close>
  qualified definition REDUCE :: \<open>8 word\<close> where \<open>REDUCE = 3\<close>
  qualified definition INITIALISATION :: \<open>8 word\<close> where \<open>INITIALISATION = 4\<close>
  qualified definition MINIMIZATION :: \<open>8 word\<close> where \<open>MINIMIZATION = 5\<close>
  qualified definition SUBSUMPTION :: \<open>8 word\<close> where \<open>SUBSUMPTION = 6\<close>
  qualified definition PURE_LITERAL :: \<open>8 word\<close> where \<open>PURE_LITERAL = 7\<close>
  qualified definition BINARY_SIMP :: \<open>8 word\<close> where \<open>BINARY_SIMP = 8\<close>
  qualified definition FOCUSED_MODE :: \<open>8 word\<close> where \<open>FOCUSED_MODE = 9\<close>
  qualified definition STABLE_MODE :: \<open>8 word\<close> where \<open>STABLE_MODE = 10\<close>

qualified abbreviation start_propagate :: \<open>unit\<close> where
  \<open>start_propagate \<equiv> IsaSAT_Profile.start IsaSAT_Profile.PROPAGATE\<close>
qualified abbreviation stop_propagate :: \<open>unit\<close> where
  \<open>stop_propagate \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.PROPAGATE\<close>

qualified abbreviation start_analyze :: \<open>unit\<close> where
  \<open>start_analyze \<equiv> IsaSAT_Profile.start IsaSAT_Profile.ANALYZE\<close>
qualified abbreviation stop_analyze :: \<open>unit\<close> where
  \<open>stop_analyze \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.ANALYZE\<close>

qualified abbreviation start_GC :: \<open>unit\<close> where
  \<open>start_GC \<equiv> IsaSAT_Profile.start IsaSAT_Profile.GC\<close>
qualified abbreviation stop_GC :: \<open>unit\<close> where
  \<open>stop_GC \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.GC\<close>

qualified abbreviation start_reduce :: \<open>unit\<close> where
  \<open>start_reduce \<equiv> IsaSAT_Profile.start IsaSAT_Profile.REDUCE\<close>
qualified abbreviation stop_reduce :: \<open>unit\<close> where
  \<open>stop_reduce \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.REDUCE\<close>

qualified abbreviation start_initialisation :: \<open>unit\<close> where
  \<open>start_initialisation \<equiv> IsaSAT_Profile.start IsaSAT_Profile.INITIALISATION\<close>
qualified abbreviation stop_initialisation :: \<open>unit\<close> where
  \<open>stop_initialisation \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.INITIALISATION\<close>

qualified abbreviation start_minimization :: \<open>unit\<close> where
  \<open>start_minimization \<equiv> IsaSAT_Profile.start IsaSAT_Profile.MINIMIZATION\<close>
qualified abbreviation stop_minimization :: \<open>unit\<close> where
  \<open>stop_minimization \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.MINIMIZATION\<close>

qualified abbreviation start_subsumption :: \<open>unit\<close> where
  \<open>start_subsumption \<equiv> IsaSAT_Profile.start IsaSAT_Profile.SUBSUMPTION\<close>
qualified abbreviation stop_subsumption :: \<open>unit\<close> where
  \<open>stop_subsumption \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.SUBSUMPTION\<close>

qualified abbreviation start_binary_simp :: \<open>unit\<close> where
  \<open>start_binary_simp \<equiv> IsaSAT_Profile.start IsaSAT_Profile.BINARY_SIMP\<close>
qualified abbreviation stop_binary_simp :: \<open>unit\<close> where
  \<open>stop_binary_simp \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.BINARY_SIMP\<close>

qualified abbreviation start_pure_literal :: \<open>unit\<close> where
  \<open>start_pure_literal \<equiv> IsaSAT_Profile.start IsaSAT_Profile.PURE_LITERAL\<close>
qualified abbreviation stop_pure_literal :: \<open>unit\<close> where
  \<open>stop_pure_literal \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.PURE_LITERAL\<close>

qualified abbreviation start_focused_mode :: \<open>unit\<close> where
  \<open>start_focused_mode \<equiv> IsaSAT_Profile.start IsaSAT_Profile.FOCUSED_MODE\<close>
qualified abbreviation stop_focused_mode :: \<open>unit\<close> where
  \<open>stop_focused_mode \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.FOCUSED_MODE\<close>

qualified abbreviation start_stable_mode :: \<open>unit\<close> where
  \<open>start_stable_mode \<equiv> IsaSAT_Profile.start IsaSAT_Profile.STABLE_MODE\<close>
qualified abbreviation stop_stable_mode :: \<open>unit\<close> where
  \<open>stop_stable_mode \<equiv> IsaSAT_Profile.stop IsaSAT_Profile.STABLE_MODE\<close>

end

end