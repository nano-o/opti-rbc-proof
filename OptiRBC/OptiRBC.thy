theory OptiRBC
  imports Main "HOL-Statespace.StateSpaceSyntax"
begin

section "Specification of the algorithm"

statespace ('p, 'v) vars =
  proposal :: "'v \<Rightarrow> bool"
  echo :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  vote :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ack :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ready :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  committed :: "'p \<Rightarrow> 'v \<Rightarrow> bool"

locale protocol =
  vars _ _ _ _ _ _  project_HOL_bool_'v_fun_'p_fun _ _ _
  for project_HOL_bool_'v_fun_'p_fun :: "'state \<Rightarrow> ('p::finite) \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes faulty :: "'p set"
    and n :: nat and f :: nat
    and broadcaster :: 'p
  defines "n \<equiv> card (UNIV::('p::finite) set)"
    and "f \<equiv> card faulty"
  assumes fault_bound: "3*f < n"
begin


definition propose_step where
  \<comment> \<open>The broadcaster proposes a value.\<close>
  "propose_step c c' v \<equiv>
     (\<forall>v'. \<not> (c\<cdot>proposal) v')
     \<and> c' = c<proposal := (c\<cdot>proposal)(v := True)>"

definition echo_step where
  "echo_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>echo) p v')
     \<and> (c\<cdot>proposal) v
     \<and> c' = c<echo := (c\<cdot>echo)(p := ((c\<cdot>echo) p)(v := True))>"

definition vote_step where
  "vote_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>vote) p v')
     \<and> card {q. (c\<cdot>echo) q v} \<ge> (n + 1) div 2
     \<and> c' = c<vote := (c\<cdot>vote)(p := ((c\<cdot>vote) p)(v := True))>"

definition ack_step where
  "ack_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ack) p v')
     \<and> (card {q. (c\<cdot>vote) q v} \<ge> ((n + f + 1) div 2) - 1
        \<or> card {q. (c\<cdot>echo) q v} \<ge> ((n + f + 1) div 2) - 1)
     \<and> c' = c<ack := (c\<cdot>ack)(p := ((c\<cdot>ack) p)(v := True))>"

definition ready_step where
  "ready_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ready) p v')
     \<and> (card {q. (c\<cdot>ack) q v} \<ge> ((n + f + 1) div 2) - 1
        \<or> card {q. (c\<cdot>ready) q v} \<ge> f + 1)
     \<and> c' = c<ready := (c\<cdot>ready)(p := ((c\<cdot>ready) p)(v := True))>"

definition opt_commit_step where
  "opt_commit_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>committed) p v')
     \<and> card {q. (c\<cdot>echo) q v} \<ge> (n + 2 * f + 1) div 2
     \<and> c' = c<committed := (c\<cdot>committed)(p := ((c\<cdot>committed) p)(v := True))>"

definition commit_step where
  "commit_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>committed) p v')
     \<and> card {q. (c\<cdot>ready) q v} \<ge> 2 * f + 1
     \<and> c' = c<committed := (c\<cdot>committed)(p := ((c\<cdot>committed) p)(v := True))>"

definition byzantine_step where
  "byzantine_step c c' \<equiv> \<exists> x .
    (broadcaster \<in> faulty \<and> c' = c<proposal := x>)
    \<or> (\<exists> p . p \<in> faulty \<and> (
      c' = c<echo := (c\<cdot>echo)(p := x)>
      \<or> c' = c<vote := (c\<cdot>vote)(p := x)>
      \<or> c' = c<ack := (c\<cdot>ack)(p := x)>
      \<or> c' = c<ready := (c\<cdot>ready)(p := x)>))"
 
definition step where
  "step c c' \<equiv> byzantine_step c c'
     \<or> (\<exists>v. (propose_step c c' v)
      \<or> (\<exists> p .
        echo_step c c' p v
        \<or> vote_step c c' p v
        \<or> ack_step c c' p v
        \<or> ready_step c c' p v
        \<or> opt_commit_step c c' p v
        \<or> commit_step c c' p v))"

definition init where
  "init c \<equiv>
     (\<forall>v. \<not> (c\<cdot>proposal) v)
     \<and> (\<forall>p v. \<not> (c\<cdot>echo) p v
          \<and> \<not> (c\<cdot>vote) p v
          \<and> \<not> (c\<cdot>ack) p v
          \<and> \<not> (c\<cdot>ready) p v
          \<and> \<not> (c\<cdot>committed) p v)"

end

end


