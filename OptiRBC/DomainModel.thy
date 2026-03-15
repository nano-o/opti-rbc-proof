theory DomainModel
  imports Complex_Main Timed_Methods
begin

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

lemma card_lemma_6:
  assumes "card S\<^sub>1 \<ge> \<lceil>real n / 2\<rceil>"
  shows "\<exists> p \<in> S\<^sub>1 . p \<notin> faulty"
  text \<open>Proof sketch: From @{term "3*f < n"} we get @{term "f < \<lceil>real n / 2\<rceil>"}, so
    @{term "card faulty < card S\<^sub>1"}. Hence @{term S\<^sub>1} cannot be a subset of faulty,
    meaning there exists a member of @{term S\<^sub>1} not in faulty.\<close>
proof -
  have "int f < \<lceil>real n / 2\<rceil>"
  proof -
    have "2 * f < n" using fault_bound by linarith
    hence "real (2*f) < real n" by simp
    hence "real f < real n / 2" by simp
    thus ?thesis by linarith
  qed
  hence "int f < int (card S\<^sub>1)" using assms by linarith
  hence "card faulty < card S\<^sub>1" by (simp add: f_def)
  hence "\<not> S\<^sub>1 \<subseteq> faulty"
    by (metis card_mono finite leD)
  thus ?thesis by blast
qed

end

text \<open>The assumptions below are the abstract counterparts of
  @{thm [source] "domain_model.card_lemma_1"}, @{thm [source] "domain_model.card_lemma_2"},
  @{thm [source] "domain_model.card_lemma_3"}, @{thm [source] "domain_model.card_lemma_4"}, and
  @{thm [source] "domain_model.card_lemma_5"}, together with the analogous quorum-against-quorum
  intersection used in Claim 3 of the paper. Optimistic quorums correspond to the
  optimistic-commit threshold, vote quorums to the vote threshold, quorums to the
  threshold used by ack and the first ready rule, amplification quorums to the
  @{term "f + (1::nat)"} threshold from the second ready rule, and commit quorums to the
  @{term "2 * f + (1::nat)"} threshold from the final commit rule.\<close>

locale abstract_domain_model =
  fixes faulty :: "('p::finite) set"
    and opt_quorum_member :: "'opQ \<Rightarrow> 'p \<Rightarrow> bool"
    and vote_quorum_member :: "'vtQ \<Rightarrow> 'p \<Rightarrow> bool"
    and quorum_member :: "'quQ \<Rightarrow> 'p \<Rightarrow> bool"
    and amplification_quorum_member :: "'amQ \<Rightarrow> 'p \<Rightarrow> bool"
    and commit_quorum_member :: "'coQ \<Rightarrow> 'p \<Rightarrow> bool"
  assumes opt_quorum_intersection:
      "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ\<^sub>1 p \<and> opt_quorum_member opQ\<^sub>2 p"
    and opt_vote_quorum_intersection:
      "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> vote_quorum_member vtQ p"
    and opt_quorum_intersects_quorum:
      "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> quorum_member quQ p"
    and quorum_intersection:
      "\<exists>p. p \<notin> faulty \<and> quorum_member quQ\<^sub>1 p \<and> quorum_member quQ\<^sub>2 p"
    and vote_quorum_has_nonfaulty_member:
      "\<exists>p. p \<notin> faulty \<and> vote_quorum_member vtQ p"
    and amplification_quorum_has_nonfaulty_member:
      "\<exists>p. p \<notin> faulty \<and> amplification_quorum_member amQ p"
    and opt_quorum_contains_vote_quorum:
      "\<exists>vtQ. \<forall>p. vote_quorum_member vtQ p \<longrightarrow> p \<notin> faulty \<and> opt_quorum_member opQ p"
    and commit_quorum_contains_amplification_quorum:
      "\<exists>amQ. \<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty \<and> commit_quorum_member coQ p"
begin

lemma opt_quorum_has_nonfaulty_member:
  "\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p"
  text \<open>Proof sketch: instantiate the optimistic-quorum intersection property with
    @{term opQ} on both sides.\<close>
  using opt_quorum_intersection[of opQ opQ] by blast

lemma vote_quorum_nonempty:
  "\<exists>p. vote_quorum_member vtQ p"
  text \<open>Proof sketch: every vote quorum has a non-faulty member, hence in particular a member.\<close>
  using vote_quorum_has_nonfaulty_member[of vtQ] by blast

lemma quorum_nonempty:
  "\<exists>p. quorum_member quQ p"
  using quorum_intersection by blast

lemma amplification_quorum_nonempty:
  "\<exists>p. amplification_quorum_member amQ p"
  text \<open>Proof sketch: every amplification quorum has a non-faulty member, hence in particular a member.\<close>
  using amplification_quorum_has_nonfaulty_member[of amQ] by blast

lemma obtain_vote_quorum_from_opt_quorum:
  obtains vtQ where "\<forall>p. vote_quorum_member vtQ p \<longrightarrow> p \<notin> faulty \<and> opt_quorum_member opQ p"
  text \<open>Proof sketch: use the abstraction of @{thm [source] "domain_model.card_lemma_5"} to extract
    a vote quorum whose members are all non-faulty members of the optimistic quorum.\<close>
  using opt_quorum_contains_vote_quorum[of opQ] by blast

lemma obtain_amplification_quorum_from_commit_quorum:
  obtains amQ where "\<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty \<and> commit_quorum_member coQ p"
  text \<open>Proof sketch: use the abstraction of @{thm [source] "domain_model.card_lemma_4"} to extract
    a non-faulty amplification quorum contained in the commit quorum.\<close>
  using commit_quorum_contains_amplification_quorum[of coQ] by blast

lemma commit_quorum_has_nonfaulty_member:
  "\<exists>p. p \<notin> faulty \<and> commit_quorum_member coQ p"
  text \<open>Proof sketch: first extract a non-faulty amplification quorum contained in the commit quorum,
    then use that every amplification quorum has a non-faulty member. Since both facts are available as
    existential assumptions, the conclusion follows directly.\<close>
  using amplification_quorum_has_nonfaulty_member commit_quorum_contains_amplification_quorum by blast


lemma commit_quorum_nonempty:
  "\<exists>p. commit_quorum_member coQ p"
  text \<open>Proof sketch: every commit quorum contains a non-faulty member, hence in particular a member.\<close>
  using commit_quorum_has_nonfaulty_member[of coQ] by blast

end

end

