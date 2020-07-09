theory IsaSAT_Reluctant
    imports More_Sepref.WB_More_Refinement "HOL-Word.More_Word"
begin

datatype reluctant =
  Reluctant
    (reluctant_limited: bool)
    (reluctant_trigger: bool)
    (reluctant_u: \<open>64 word\<close>)
    (reluctant_v: \<open>64 word\<close>)
    (reluctant_period: \<open>64 word\<close>)
    (reluctant_wait: \<open>64 word\<close>)
    (reluctant_limit: \<open>64 word\<close>)

definition reluctant_set_trigger :: \<open>bool \<Rightarrow> reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_set_trigger limited r =
     (let
    trigger = reluctant_trigger r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
    limit = reluctant_limit r in Reluctant limited trigger u v period wait limit)\<close>

definition reluctant_disable :: \<open>reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_disable r =
  (let
    limited = reluctant_limited r;
    trigger = reluctant_trigger r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
  limit = reluctant_limit r in
  (Reluctant limited trigger u v 0 wait limit))\<close>

definition reluctant_triggered :: \<open>reluctant \<Rightarrow> reluctant \<times> bool\<close> where
  \<open>reluctant_triggered r = (reluctant_set_trigger False r, reluctant_trigger r)\<close>

definition reluctant_tick :: \<open>reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_tick  r =
  (let
    limited = reluctant_limited r;
    trigger = reluctant_trigger r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
    limit = reluctant_limit r in
  (if period = 0 \<or> trigger then Reluctant limited trigger u v period (wait) limit
   else if wait > 1 then Reluctant limited trigger u v period (wait - 1) limit
   else let (u, v) = (if u AND (0-u) = v then (u+1, 1) else (u, 2 * v));
                 w = v * wait;
             (u, v, wait) = (if limited \<and> wait > limit then (1,2, period) else (u, v, wait)) in
    Reluctant limited True u v period wait limit))\<close>

definition reluctant_enable :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> reluctant\<close> where
  \<open>reluctant_enable period limit =
  (let limited = limit \<noteq> 0;
       period = (if limited \<and> period > limit then limit else period)
     in
    Reluctant limited False 1 1 period period limit)\<close>

definition reluctant_init :: \<open>reluctant\<close> where
  \<open>reluctant_init = reluctant_enable (1<< 10) (1<<20)\<close>

end