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
  abs_vars _ _ _ _ _ _
    project_HOL_bool_'v_fun_'p_fun inject_HOL_bool_'v_fun_'p_fun
    project_HOL_bool_'v_fun inject_HOL_bool_'v_fun +
  abstract_domain_model broadcaster faulty
    opt_quorum_member vote_quorum_member quorum_member
    amplification_quorum_member commit_quorum_member
  for project_HOL_bool_'v_fun_'p_fun :: "'b \<Rightarrow> 'p::finite \<Rightarrow> 'v \<Rightarrow> bool"
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

lemma step_cases [consumes 1]:
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

lemmas protocol_defs = init_def byzantine_step_def propose_step_def
echo_step_def vote_step_def ack_step_def ready_step_def opt_commit_step_def commit_step_def

method try1 =
   (metis | force | (smt (verit)))

definition inv1 where
  "inv1 c \<equiv> \<forall> p v . p \<notin> faulty \<and> (c\<cdot>committed) p v \<longrightarrow>
    (\<exists>Q. \<forall>q. amplification_quorum_member Q q \<longrightarrow> q \<notin> faulty \<and> (c\<cdot>ready) q v)
    \<or> (\<exists>Q. \<forall>q. opt_quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>echo) q v)"


lemma inv1_inductive:
  "inductive_invariant inv1"
  apply (unfold inductive_invariant_def; rule conjI; (unfold step_def)?) \<comment> \<open>First obtain one goal per step case (and init)\<close>
   apply (simp add:inv1_def init_def) \<comment> \<open>Discharge init\<close>
  apply (auto elim: step_cases; auto simp add:protocol_defs inv1_def; insert abstract_domain_model_axioms; unfold abstract_domain_model_def) \<comment> \<open>Do cases analysis on the step\<close>
              apply try1+
  done

definition inv2 where
  "inv2 c \<equiv> \<forall> p v . p \<notin> faulty \<and> (c\<cdot>ready) p v \<longrightarrow> (\<exists>Q. \<forall>q. quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>ack) q v)"

lemma inv2_inductive:
  "inductive_invariant inv2"
  apply (unfold inductive_invariant_def; rule conjI; (unfold step_def)?) \<comment> \<open>First obtain one goal per step case (and init)\<close>
   apply (simp add:inv2_def init_def) \<comment> \<open>Discharge init\<close>
  apply (auto elim: step_cases; auto simp add:protocol_defs inv2_def; insert abstract_domain_model_axioms; unfold abstract_domain_model_def) \<comment> \<open>Do cases analysis on the step\<close>
              apply try1+
  done

definition inv3 where
  "inv3 c \<equiv> \<forall> v . (\<exists>Q. \<forall>q. quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>ack) q v) \<longrightarrow> (
    (\<exists>Q. \<forall>q. quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>echo) q v)
    \<or> (\<exists>Q. \<forall>q. quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>vote) q v))"

lemma inv3_inductive:
  "inductive_invariant inv3"
  apply (unfold inductive_invariant_def; rule conjI; (unfold step_def)?) \<comment> \<open>First obtain one goal per step case (and init)\<close>
   apply (simp add:inv3_def init_def) \<comment> \<open>Discharge init\<close>
  apply (auto elim: step_cases; auto simp add:protocol_defs inv3_def; insert abstract_domain_model_axioms; unfold abstract_domain_model_def) \<comment> \<open>Do cases analysis on the step\<close>
        apply try1+
  done

definition inv4 where
  "inv4 c \<equiv> \<forall> v . (\<exists>Q. \<forall>q. quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>vote) q v) \<longrightarrow> 
    (\<exists>Q. \<forall>q. vote_quorum_member Q q \<and> q \<notin> faulty \<longrightarrow> (c\<cdot>vote) q v)"

lemma inv4_inductive:
  "inductive_invariant inv4"
  apply (unfold inductive_invariant_def; rule conjI; (unfold step_def)?) \<comment> \<open>First obtain one goal per step case (and init)\<close>
   apply (simp add:init_def inv4_def) \<comment> \<open>Discharge init\<close>
  apply (auto elim: step_cases; auto simp add:protocol_defs inv4_def; insert abstract_domain_model_axioms; unfold abstract_domain_model_def) \<comment> \<open>Do cases analysis on the step\<close>
        apply try1+
  done
end

end