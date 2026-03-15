theory OptiRBC
  imports Complex_Main Timed_Methods "HOL-Statespace.StateSpaceSyntax" "HOL-Eisbach.Eisbach"
begin

section "domain model"

locale domain_model =
  fixes faulty :: "('p::finite) set"
    and n :: nat and f :: nat
    and broadcaster :: 'p
  defines n_def:"n \<equiv> card (UNIV::'p set)"
    and f_def:"f \<equiv> card faulty"
  assumes fault_bound: "3*f < n"
begin

lemma card_lemma_1:
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1"
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>"
  shows "(S\<^sub>1 \<inter> S\<^sub>2) - faulty \<noteq> {}"
  text \<open>Proof sketch: Since broadcaster is not in @{term S\<^sub>1} or @{term S\<^sub>2}, both are subsets of
    @{term "UNIV - {broadcaster}"} which has cardinality @{term "n - 1::nat"}. By inclusion-exclusion,
    @{term "card (S\<^sub>1 \<inter> S\<^sub>2)"} is at least @{term "f::nat"}.
    Since broadcaster is in faulty but not in @{term "S\<^sub>1 \<inter> S\<^sub>2"}, at most @{term "f - 1::nat"} faulty
    elements can be in the intersection. So @{term "(S\<^sub>1 \<inter> S\<^sub>2) - faulty"} has at least 1 element.\<close>
proof -
  have n_pos: "n \<ge> 1" using fault_bound by (simp add: n_def)
  have f_pos: "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  have card_U: "card (UNIV - {broadcaster} :: 'p set) = n - 1"
    using n_pos by (simp add: n_def)
  text \<open>By inclusion-exclusion, the intersection is large enough.\<close>
  have ie: "card (S\<^sub>1 \<inter> S\<^sub>2) + (n - 1) \<ge> card S\<^sub>1 + card S\<^sub>2"
    by (metis Diff_empty Un_iff add.commute add_le_cancel_right \<open>broadcaster \<notin> S\<^sub>1\<close> \<open>broadcaster \<notin> S\<^sub>2\<close> card_U card_Un_Int card_mono finite subset_Diff_insert subset_UNIV)
  text \<open>The sum of cardinalities is at least @{term "n + f - 1::nat"} in int.\<close>
  have sum_bound: "int (card S\<^sub>1) + int (card S\<^sub>2) \<ge> int n + int f - 1"
  proof -
    have "n + 2*f \<ge> 2" using n_pos f_pos by linarith
    hence "real (n + 2*f - 2) / 2 + real n / 2 = real n + real f - 1"
      by (simp add: of_nat_diff field_simps)
    thus ?thesis
      using \<open>card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> \<open>card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>\<close>
        le_of_int_ceiling[of "real (n + 2*f - 2) / 2"]
        le_of_int_ceiling[of "real n / 2"]
      by linarith
  qed
  text \<open>So the intersection has at least @{term "f::nat"} elements.\<close>
  have inter_card: "int (card (S\<^sub>1 \<inter> S\<^sub>2)) \<ge> int f"
    using ie sum_bound n_pos by linarith
  text \<open>Broadcaster is in faulty but not in the intersection, so at most @{term "f - 1::nat"}
    faulty elements are in the intersection.\<close>
  have faulty_inter: "card (faulty \<inter> (S\<^sub>1 \<inter> S\<^sub>2)) \<le> f - 1"
    by (metis Int_iff Int_lower1 One_nat_def \<open>broadcaster \<in> faulty\<close> \<open>broadcaster \<notin> S\<^sub>1\<close> bot_nat_0.extremum_unique card.infinite card.remove card_Diff_singleton_if card_seteq f_def f_pos not_less_eq_eq)
  text \<open>Conclude that the intersection minus faulty is nonempty.\<close>
  have "card ((S\<^sub>1 \<inter> S\<^sub>2) - faulty) \<ge> 1"
    by (metis Diff_Diff_Int Diff_empty Int_lower2 One_nat_def card.empty card_seteq dec_greater_eq_self_imp_bot empty_subsetI f_def f_pos faulty_inter finite inter_card not_less_eq_eq of_nat_le_iff)
  thus ?thesis by (metis card.empty not_one_le_zero)
qed

lemma card_lemma_2:
  \<comment> \<open>This follows from @{thm [source] card_lemma_1} because @{term "\<lceil>real (n + f - 1) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"} when @{term "f>0"}.\<close>
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1"
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>"
  shows "(S\<^sub>1 \<inter> S\<^sub>2) - faulty \<noteq> {}"
  text \<open>Since @{term "f \<ge> 1"}, we have @{term "\<lceil>real (n + f - 1) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"},
    so the assumption on @{term S\<^sub>2} is at least as strong as what @{thm [source] card_lemma_1} requires.
    We apply @{thm [source] card_lemma_1} directly.\<close>
proof -
  have "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  hence "\<lceil>real (n + f - 1) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"
    by (intro ceiling_mono divide_right_mono) linarith+
  hence "card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>"
    using \<open>card S\<^sub>2 \<ge> \<lceil>real (n + f - 1) / 2\<rceil>\<close> by linarith
  thus ?thesis
    using card_lemma_1[OF \<open>broadcaster \<in> faulty\<close> \<open>broadcaster \<notin> S\<^sub>1\<close> \<open>card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> \<open>broadcaster \<notin> S\<^sub>2\<close>]
    by blast
qed

lemma card_lemma_3:
  \<comment> \<open>This should follows immediately from @{thm [source] card_lemma_1} because @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"} when @{term "f>0"}\<close>
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1" 
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
    and "broadcaster \<notin> S\<^sub>2"
    and "card S\<^sub>2 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
  shows "((S\<^sub>1 \<inter> S\<^sub>2) - faulty) \<noteq> {}"
  text \<open>Since @{term "f \<ge> 1"}, we have @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"},
    so the assumption on @{term S\<^sub>2} implies the weaker bound needed by @{thm [source] card_lemma_1}.
    We apply @{thm [source] card_lemma_1} directly.\<close>
proof -
  have "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  hence "\<lceil>real (n + 2*f - 2) / 2\<rceil> \<ge> \<lceil>real n / 2\<rceil>"
    by (intro ceiling_mono divide_right_mono) linarith+
  hence "card S\<^sub>2 \<ge> \<lceil>real n / 2\<rceil>"
    using \<open>card S\<^sub>2 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> by linarith
  thus ?thesis
    using card_lemma_1[OF \<open>broadcaster \<in> faulty\<close> \<open>broadcaster \<notin> S\<^sub>1\<close> \<open>card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>\<close> \<open>broadcaster \<notin> S\<^sub>2\<close>]
    by blast
qed

lemma card_lemma_4:
  assumes "card S\<^sub>1 \<ge> 2*f +1"
  shows "card (S\<^sub>1 - faulty) \<ge> f +1"
  text \<open>At most @{term f} elements of @{term S\<^sub>1} can be faulty, so removing faulty elements
    leaves at least @{term "2*f + 1 - f"} = @{term "f + (1::nat)"} elements.\<close>
proof -
  have "card (S\<^sub>1 \<inter> faulty) \<le> f"
    by (metis Int_lower2 card_mono f_def finite)
  moreover have "card (S\<^sub>1 - faulty) = card S\<^sub>1 - card (S\<^sub>1 \<inter> faulty)"
    by (metis card_Diff_subset_Int finite)
  ultimately show ?thesis using assms by linarith
qed

lemma card_lemma_5:
  assumes "broadcaster \<in> faulty"
    and "broadcaster \<notin> S\<^sub>1" 
    and "card S\<^sub>1 \<ge> \<lceil>real (n + 2*f - 2) / 2\<rceil>"
  shows "card (S\<^sub>1 - faulty) \<ge> \<lceil>real n / 2\<rceil>"
  text \<open>Since @{term "broadcaster \<in> faulty"} but @{term "broadcaster \<notin> S\<^sub>1"}, at most @{term "f - 1::nat"}
    faulty elements are in @{term S\<^sub>1}. So @{term "card (S\<^sub>1 - faulty)"} is at least
    @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> - int (f - 1)"}. Since
    @{term "\<lceil>real (n + 2*f - 2) / 2\<rceil> = \<lceil>real n / 2\<rceil> + int f - 1"}, the result follows.\<close>
proof -
  have f_pos: "f \<ge> 1"
    by (metis One_nat_def \<open>broadcaster \<in> faulty\<close> bot_nat_0.extremum_unique card.remove f_def finite nat.simps(3) not_less_eq_eq)
  have "card (S\<^sub>1 \<inter> faulty) \<le> f - 1"
    by (metis Int_iff Int_lower2 assms(1,2) card.remove card_Diff_singleton_if card_seteq f_def finite not_less_eq_eq)
  moreover have "card (S\<^sub>1 - faulty) = card S\<^sub>1 - card (S\<^sub>1 \<inter> faulty)"
    by (metis card_Diff_subset_Int finite)
  moreover have "\<lceil>real (n + 2*f - 2) / 2\<rceil> = \<lceil>real n / 2\<rceil> + int f - 1"
  proof -
    have "n + 2*f \<ge> 2" using f_pos by linarith
    hence "real (n + 2*f - 2) / 2 = real n / 2 + real f - 1"
      by (simp add: of_nat_diff field_simps)
    thus ?thesis by linarith
  qed
  moreover have "card (S\<^sub>1 \<inter> faulty) \<le> card S\<^sub>1"
    by (simp add: card_mono)
  ultimately have "int (card (S\<^sub>1 - faulty)) \<ge> int (card S\<^sub>1) - int (f - 1)"
    by (simp add: card_Diff_subset_Int card_mono of_nat_diff)
  moreover have "int (card S\<^sub>1) \<ge> \<lceil>real n / 2\<rceil> + int f - 1"
    using assms(3) by linarith
  ultimately show ?thesis using f_pos by linarith
qed

end

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


