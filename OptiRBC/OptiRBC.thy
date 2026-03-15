theory OptiRBC
  imports Complex_Main "HOL-Statespace.StateSpaceSyntax"
begin

section "Specification of the algorithm"

statespace ('p, 'v) vars =
  proposal :: "'v \<Rightarrow> bool"
  echo :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  vote :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ack :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ready :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  committed :: "'p \<Rightarrow> 'v \<Rightarrow> bool"

named_theorems protocol_defs

locale protocol =
  vars _ _ _ _ _ _  project_HOL_bool_'v_fun_'p_fun _ _ _
  for project_HOL_bool_'v_fun_'p_fun :: "'state \<Rightarrow> ('p::finite) \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes faulty :: "'p set"
    and n :: nat and f :: nat
    and broadcaster :: 'p
  defines n_def:"n \<equiv> card (UNIV::('p::finite) set)"
    and f_def:"f \<equiv> card faulty"
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
     \<and> card {q. q \<noteq> broadcaster \<and> (c\<cdot>echo) q v} \<ge> \<lceil>real n div 2\<rceil>
     \<and> c' = c<vote := (c\<cdot>vote)(p := ((c\<cdot>vote) p)(v := True))>"

definition ack_step where
  "ack_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ack) p v')
     \<and> (card {q. q \<noteq> broadcaster \<and> (c\<cdot>vote) q v} \<ge> \<lceil>real (n + f - 1) div 2\<rceil>
        \<or> card {q. q \<noteq> broadcaster \<and> (c\<cdot>echo) q v} \<ge> \<lceil>real (n + f - 1) div 2\<rceil>)
     \<and> c' = c<ack := (c\<cdot>ack)(p := ((c\<cdot>ack) p)(v := True))>"

definition ready_step where
  "ready_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ready) p v')
     \<and> (card {q. q \<noteq> broadcaster \<and> (c\<cdot>ack) q v} \<ge> \<lceil>real (n + f - 1) div 2\<rceil>
        \<or> card {q. (c\<cdot>ready) q v} \<ge> f + 1)
     \<and> c' = c<ready := (c\<cdot>ready)(p := ((c\<cdot>ready) p)(v := True))>"

definition opt_commit_step where
  "opt_commit_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>committed) p v')
     \<and> card {q. q \<noteq> broadcaster \<and> (c\<cdot>echo) q v} \<ge> \<lceil>real (n + 2*f - 2) div 2\<rceil>
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

definition inductive_invariant where
  "inductive_invariant I \<equiv>
     (\<forall>c. init c \<longrightarrow> I c)
     \<and> (\<forall>c c'. I c \<longrightarrow> step c c' \<longrightarrow> I c')"

definition inv1 where
  \<comment> \<open>if the broadcaster is faulty and a non-faulty party commits v, then either there are f+1 non-faulty parties ready for v or there are ceil((n+2f-2)/2)-(f-1) non-faulty non-
  broadcaster parties that echoed v.\<close>
  "inv1 c \<equiv> \<forall> p v . broadcaster \<in> faulty \<and> p \<notin> faulty \<and> (c\<cdot>committed) p v \<longrightarrow>
    card {p . p \<notin> faulty \<and> (c\<cdot>ready) p v} \<ge> f+1
    \<or> card {p . p \<notin> faulty \<and> (c\<cdot>echo) p v} \<ge> \<lceil>real (n + 2*f - 2) div 2\<rceil>-f+1"

lemmas protocol_defs = step_def propose_step_def vote_step_def ack_step_def
  byzantine_step_def ready_step_def init_def

lemma inv1_inductive:
  "inductive_invariant inv1"
proof -
  have "inv1 c" if "init c" for c
    using that unfolding inv1_def protocol_defs by blast
  moreover
  have "inv1 c'" if "inv1 c" and "step c c'" for c c'
    using that
    unfolding inv1_def protocol_defs apply simp
    sorry
  ultimately
  show ?thesis unfolding inductive_invariant_def by simp
qed

end

end


