theory OptiRBC
  imports Complex_Main Timed_Methods "HOL-Statespace.StateSpaceSyntax" "HOL-Eisbach.Eisbach"
    DomainModel
begin

section "domain model"

statespace ('p, 'v) vars =
  proposal :: "'v \<Rightarrow> bool"
  echo :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  vote :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ack :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  ready :: "'p \<Rightarrow> 'v \<Rightarrow> bool"
  committed :: "'p \<Rightarrow> 'v \<Rightarrow> bool"

named_theorems protocol_defs

locale protocol = domain_model faulty _ _ + vars _ _ _ _ _ _  project_HOL_bool_'v_fun_'p_fun _ _ _
  for faulty :: "'p::finite set" and project_HOL_bool_'v_fun_'p_fun :: "'state \<Rightarrow> 'p \<Rightarrow> 'v \<Rightarrow> bool"
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
     \<and> card {q. q \<noteq> broadcaster \<and> (c\<cdot>echo) q v} \<ge> \<lceil>real n / 2\<rceil>
     \<and> c' = c<vote := (c\<cdot>vote)(p := ((c\<cdot>vote) p)(v := True))>"

definition ack_step where
  "ack_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ack) p v')
     \<and> (card {q. q \<noteq> broadcaster \<and> (c\<cdot>vote) q v} \<ge> \<lceil>real (n + f - 1) / 2\<rceil>
        \<or> card {q. q \<noteq> broadcaster \<and> (c\<cdot>echo) q v} \<ge> \<lceil>real (n + f - 1) / 2\<rceil>)
     \<and> c' = c<ack := (c\<cdot>ack)(p := ((c\<cdot>ack) p)(v := True))>"

definition ready_step where
  "ready_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>ready) p v')
     \<and> (card {q. q \<noteq> broadcaster \<and> (c\<cdot>ack) q v} \<ge> \<lceil>real (n + f - 1) / 2\<rceil>
        \<or> card {q. (c\<cdot>ready) q v} \<ge> f + 1)
     \<and> c' = c<ready := (c\<cdot>ready)(p := ((c\<cdot>ready) p)(v := True))>"

definition opt_commit_step where
  "opt_commit_step c c' p v \<equiv>
     p \<noteq> broadcaster
     \<and> (\<forall>v'. \<not> (c\<cdot>committed) p v')
     \<and> card {q. q \<noteq> broadcaster \<and> (c\<cdot>echo) q v} \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>
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
  \<comment> \<open>If @{term broadcaster} is faulty and a non-faulty party commits @{term v}, then either there
  are @{term "f+1"} non-faulty parties ready for @{term v} or there are
  @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> - (f - 1)"} non-faulty non-broadcaster parties that echoed @{term v}.\<close>
  "inv1 c \<equiv> \<forall> p v . broadcaster \<in> faulty \<and> p \<notin> faulty \<and> (c\<cdot>committed) p v \<longrightarrow>
    card {p . p \<notin> faulty \<and> (c\<cdot>ready) p v} \<ge> f+1
    \<or> card {p . p \<notin> faulty \<and> (c\<cdot>echo) p v} \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>-(f-1)"

lemmas protocol_defs = step_def propose_step_def vote_step_def ack_step_def
  byzantine_step_def ready_step_def init_def

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
    by (metis ack_case byzantine_case commit_case echo_case inv opt_commit_case propose_case protocol.step_cases protocol_axioms
        ready_case vote_case)
qed

method inductive_invariant_cases = (rule inductive_invariant_stepsI)

section "Safety proof"

lemma inv1_inductive:
  "inductive_invariant inv1"
  oops

definition no_disagreement where
  "no_disagreement c \<equiv> \<forall> p p' v v' . p \<notin> faulty \<and> p' \<notin> faulty \<longrightarrow>
    (c\<cdot>committed) p v \<and> (c\<cdot>committed) p' v' \<longrightarrow> v = v'"


lemma no_disagreement_inductive:
  "inductive_invariant no_disagreement"
  oops

end

end


