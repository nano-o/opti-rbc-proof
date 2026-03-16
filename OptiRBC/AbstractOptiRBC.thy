theory AbstractOptiRBC
  imports Complex_Main Timed_Methods "HOL-Statespace.StateSpaceSyntax" "HOL-Eisbach.Eisbach"
    AbstractDomainModel
begin

section \<open>Abstract protocol specification\<close>

text \<open>This theory mirrors the protocol transitions of @{text "OptiRBC"} but works
  over the abstract domain model, replacing cardinality thresholds with quorum witnesses.\<close>

statespace ('p,'v) abs_vars =
  proposal :: "'v \<Rightarrow> bool"
  echo :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  vote :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ack :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ready :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  committed :: "'p \<Rightarrow> 'v \<Rightarrow> bool"

locale abs_protocol =
  abs_vars proposal echo vote ack ready committed
    project_HOL_bool_'v_fun_'p_fun inject_HOL_bool_'v_fun_'p_fun
    project_HOL_bool_'v_fun inject_HOL_bool_'v_fun +
  abstract_domain_model broadcaster faulty
    opt_quorum_member vote_quorum_member quorum_member
    amplification_quorum_member commit_quorum_member
  for proposal :: "'a"
    and echo :: "'a"
    and vote :: "'a"
    and ack :: "'a"
    and ready :: "'a"
    and committed :: "'a"
    and project_HOL_bool_'v_fun_'p_fun :: "'b \<Rightarrow> 'p::finite \<Rightarrow> 'v \<Rightarrow> bool"
    and inject_HOL_bool_'v_fun_'p_fun :: "('p \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'b"
    and project_HOL_bool_'v_fun :: "'b \<Rightarrow> 'v \<Rightarrow> bool"
    and inject_HOL_bool_'v_fun :: "('v \<Rightarrow> bool) \<Rightarrow> 'b"
    and broadcaster :: "'p"
    and faulty :: "'p set"
    and opt_quorum_member :: "'opQ \<Rightarrow> 'p \<Rightarrow> bool"
    and vote_quorum_member :: "'vtQ \<Rightarrow> 'p \<Rightarrow> bool"
    and quorum_member :: "'quQ \<Rightarrow> 'p \<Rightarrow> bool"
    and amplification_quorum_member :: "'amQ \<Rightarrow> 'p \<Rightarrow> bool"
    and commit_quorum_member :: "'coQ \<Rightarrow> 'p \<Rightarrow> bool"
begin

section \<open>Protocol transitions\<close>

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
     \<and> (\<exists>Q::'vtQ. \<forall>q. vote_quorum_member Q q \<longrightarrow> q \<noteq> broadcaster \<and> (c\<cdot>echo) q v)
     \<and> c' = c<vote := (c\<cdot>vote)(p := ((c\<cdot>vote) p)(v := True))>"

definition ack_step where
  "ack_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ack) p v')
     \<and> ((\<exists>Q::'quQ. \<forall>q. quorum_member Q q \<longrightarrow> q \<noteq> broadcaster \<and> (c\<cdot>vote) q v)
        \<or> (\<exists>Q::'quQ. \<forall>q. quorum_member Q q \<longrightarrow> q \<noteq> broadcaster \<and> (c\<cdot>echo) q v))
     \<and> c' = c<ack := (c\<cdot>ack)(p := ((c\<cdot>ack) p)(v := True))>"

definition ready_step where
  "ready_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ready) p v')
     \<and> ((\<exists>Q::'quQ. \<forall>q. quorum_member Q q \<longrightarrow> q \<noteq> broadcaster \<and> (c\<cdot>ack) q v)
        \<or> (\<exists>Q::'amQ. \<forall>q. amplification_quorum_member Q q \<longrightarrow> (c\<cdot>ready) q v))
     \<and> c' = c<ready := (c\<cdot>ready)(p := ((c\<cdot>ready) p)(v := True))>"

definition opt_commit_step where
  "opt_commit_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>committed) p v')
     \<and> (\<exists>Q::'opQ. \<forall>q. opt_quorum_member Q q \<longrightarrow> q \<noteq> broadcaster \<and> (c\<cdot>echo) q v)
     \<and> c' = c<committed := (c\<cdot>committed)(p := ((c\<cdot>committed) p)(v := True))>"

definition commit_step where
  "commit_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>committed) p v')
     \<and> (\<exists>Q::'coQ. \<forall>q. commit_quorum_member Q q \<longrightarrow> (c\<cdot>ready) q v)
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

section \<open>Initial state\<close>

definition init where
  "init c \<equiv>
     (\<forall>v. \<not> (c\<cdot>proposal) v)
     \<and> (\<forall>p v. \<not> (c\<cdot>echo) p v
          \<and> \<not> (c\<cdot>vote) p v
          \<and> \<not> (c\<cdot>ack) p v
          \<and> \<not> (c\<cdot>ready) p v
          \<and> \<not> (c\<cdot>committed) p v)"

section \<open>Inductive invariants\<close>

definition inductive_invariant where
  "inductive_invariant I \<equiv>
     (\<forall>c. init c \<longrightarrow> I c)
     \<and> (\<forall>c c'. I c \<longrightarrow> step c c' \<longrightarrow> I c')"

section \<open>Proof methods\<close>

lemma step_cases [consumes 1, case_names byzantine propose echo vote ack ready opt_commit commit]:
  assumes "step c c'"
  obtains
    (byzantine) "byzantine_step c c'"
  | (propose) v where "propose_step c c' v"
  | (echo) p v where "echo_step c c' p v"
  | (vote) p v where "vote_step c c' p v"
  | (ack) p v where "ack_step c c' p v"
  | (ready) p v where "ready_step c c' p v"
  | (opt_commit) p v where "opt_commit_step c c' p v"
  | (commit) p v where "commit_step c c' p v"
  using assms unfolding step_def by blast

lemma inductive_invariant_stepsI:
  assumes init_case: "\<And>c. init c \<Longrightarrow> I c"
    and byzantine_case: "\<And>c c'. I c \<Longrightarrow> byzantine_step c c' \<Longrightarrow> I c'"
    and propose_case: "\<And>c c' v. I c \<Longrightarrow> propose_step c c' v \<Longrightarrow> I c'"
    and echo_case: "\<And>c c' p v. I c \<Longrightarrow> echo_step c c' p v \<Longrightarrow> I c'"
    and vote_case: "\<And>c c' p v. I c \<Longrightarrow> vote_step c c' p v \<Longrightarrow> I c'"
    and ack_case: "\<And>c c' p v. I c \<Longrightarrow> ack_step c c' p v \<Longrightarrow> I c'"
    and ready_case: "\<And>c c' p v. I c \<Longrightarrow> ready_step c c' p v \<Longrightarrow> I c'"
    and opt_commit_case: "\<And>c c' p v. I c \<Longrightarrow> opt_commit_step c c' p v \<Longrightarrow> I c'"
    and commit_case: "\<And>c c' p v. I c \<Longrightarrow> commit_step c c' p v \<Longrightarrow> I c'"
  shows "inductive_invariant I"
proof (unfold inductive_invariant_def, intro conjI allI impI)
  fix c
  assume "init c"
  then show "I c"
    by (rule init_case)
next
  fix c c'
  assume inv: "I c" and st: "step c c'"
  from st show "I c'"
    by (metis ack_case byzantine_case commit_case echo_case inv opt_commit_case propose_case step_cases
        ready_case vote_case)
qed

method inductive_invariant_cases = (rule inductive_invariant_stepsI)

section \<open>Safety invariants\<close>

definition inv1 where
  \<comment> \<open>If @{term broadcaster} is faulty and a non-faulty party commits @{term v}, then either
  there is an amplification quorum of non-faulty parties ready for @{term v}, or there is
  a vote quorum of non-faulty parties that echoed @{term v}.\<close>
  "inv1 c \<equiv> \<forall> p v . broadcaster \<in> faulty \<and> p \<notin> faulty \<and> (c\<cdot>committed) p v \<longrightarrow>
    (\<exists>Q. \<forall>q. amplification_quorum_member Q q \<longrightarrow> q \<notin> faulty \<and> (c\<cdot>ready) q v)
    \<or> (\<exists>Q. \<forall>q. vote_quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>echo) q v)"

lemma inv1_inductive:
  "inductive_invariant inv1"
  text \<open>Proof sketch: We use @{thm [source] inductive_invariant_stepsI} to case-split on transitions.
    The init case is vacuous because no party has committed. Most honest steps do not change
    @{term committed}, so the antecedent is unchanged; for echo and ready steps the consequent
    can only become easier to satisfy because they add True entries.
    For @{term opt_commit_step}: the committing party saw an optimistic quorum of echoes, and
    @{thm [source] opt_quorum_contains_vote_quorum} extracts a vote quorum of non-faulty
    members who all echoed the committed value (second disjunct).
    For @{term commit_step}: the committing party saw a commit quorum of ready parties, and
    @{thm [source] commit_quorum_contains_amplification_quorum} extracts an amplification
    quorum of non-faulty members who are all ready (first disjunct).
    For @{term byzantine_step}: only faulty parties' fields change, and the invariant's
    consequent refers only to non-faulty parties' @{term ready} and @{term echo}, so it is
    preserved.\<close>
proof (inductive_invariant_cases)
  fix c
  assume "init c"
  then show "inv1 c"
    unfolding inv1_def init_def by simp
next
  fix c c'
  assume inv: "inv1 c" and step: "byzantine_step c c'"
  then show "inv1 c'"
    unfolding inv1_def byzantine_step_def
    apply auto
    apply meson
    apply (smt (verit))
    apply meson
    apply meson
    by metis
next
  fix c c' v
  assume inv: "inv1 c" and step: "propose_step c c' v"
  then show "inv1 c'"
    unfolding inv1_def propose_step_def by auto
next
  fix c c' p v
  assume inv: "inv1 c" and step: "echo_step c c' p v"
  then show "inv1 c'"
    unfolding inv1_def echo_step_def
    apply auto
    apply blast
    by blast
next
  fix c c' p v
  assume inv: "inv1 c" and step: "vote_step c c' p v"
  then show "inv1 c'"
    unfolding inv1_def vote_step_def by auto
next
  fix c c' p v
  assume inv: "inv1 c" and step: "ack_step c c' p v"
  then show "inv1 c'"
    unfolding inv1_def ack_step_def by auto
next
  fix c c' p v
  assume inv: "inv1 c" and step: "ready_step c c' p v"
  then show "inv1 c'"
    unfolding inv1_def ready_step_def
    apply auto
    apply blast
    apply blast
    apply blast
    by blast
next
  fix c c' p v
  assume inv: "inv1 c" and step: "opt_commit_step c c' p v"
  then show "inv1 c'"
    unfolding inv1_def opt_commit_step_def
    apply auto
    by (metis opt_quorum_contains_vote_quorum)
next
  fix c c' p v
  assume inv: "inv1 c" and step: "commit_step c c' p v"
  then show "inv1 c'"
    unfolding inv1_def commit_step_def
    apply auto
    by (metis commit_quorum_contains_amplification_quorum)
qed

definition inv2 where
  "inv2 c \<equiv> \<forall> p v . broadcaster \<in> faulty \<and> p \<notin> faulty \<and> (c\<cdot>committed) p v \<longrightarrow>
    (\<exists>Q. \<forall>q. quorum_member Q q \<longrightarrow> q \<notin> faulty \<and> (c\<cdot>ack) q v)
    \<or> (\<exists>Q. \<forall>q. vote_quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>echo) q v)"

end

end