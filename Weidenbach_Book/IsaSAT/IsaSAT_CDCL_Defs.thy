theory IsaSAT_CDCL_Defs
  imports IsaSAT_Propagate_Conflict_Defs IsaSAT_Other_Defs IsaSAT_Show
begin


paragraph \<open>Combining Together: Full Strategy\<close>

definition  cdcl_twl_stgy_prog_wl_D_heur
   :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
  \<open>cdcl_twl_stgy_prog_wl_D_heur S\<^sub>0 =
  do {
    do {
        (brk, T) \<leftarrow> WHILE\<^sub>T
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          cdcl_twl_o_prog_wl_D_heur T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>
definition cdcl_twl_stgy_prog_break_wl_D_heur :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
  \<open>cdcl_twl_stgy_prog_break_wl_D_heur S\<^sub>0 =
  do {
    b \<leftarrow> RETURN (isasat_fast S\<^sub>0);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). True\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(isasat_fast S);
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          ASSERT(isasat_fast T);
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
          b \<leftarrow> RETURN (isasat_fast T);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    if brk then RETURN T
    else cdcl_twl_stgy_prog_wl_D_heur T
  }\<close>


definition cdcl_twl_stgy_prog_bounded_wl_heur :: \<open>isasat \<Rightarrow> (bool \<times> isasat) nres\<close>
where
  \<open>cdcl_twl_stgy_prog_bounded_wl_heur S\<^sub>0 =
  do {
    b \<leftarrow> RETURN (isasat_fast S\<^sub>0);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). True\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(isasat_fast S);
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          ASSERT(isasat_fast T);
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
          b \<leftarrow> RETURN (isasat_fast T);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    RETURN (brk, T)
  }\<close>

end