theory AxiomaticDomainModel
  imports AbstractDomainModel
begin

text \<open>In this theory we define types of quorums corresponding to the various thresholds
used by the optimistic RBC algorithm. This will then allow us to do proof abstractly, just relying
on intersection properties and not on cardinalitites.\<close>

section \<open>The domain model, axiomatically\<close>

typedecl party

axiomatization faulty :: "party set" and broadcaster :: party
  where party_finite: "finite (UNIV :: party set)"

instantiation party :: finite
begin

instance
  by intro_classes (simp add: party_finite)

end

definition n :: nat where
  "n \<equiv> card (UNIV :: party set)"

definition f :: nat where
  "f \<equiv> card faulty"

axiomatization where
  fault_bound: "3*f < n"
  and two_parties: "2 \<le> n"

typedef opt_quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>}"
proof -
  text \<open>Proof sketch: @{term "UNIV - {broadcaster}"} excludes @{term broadcaster} and has
    cardinality @{term "n - 1"}. The global inequality @{term fault_bound} makes this large
    enough for the optimistic threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
  proof -
    have "real (n - 1) >= real (n + 2 * f - 2) / 2"
      using fault_bound by linarith
    then have "\<lceil>real (n - 1)\<rceil> >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      by (intro ceiling_mono)
    then have "n - 1 >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
      by simp
    then show ?thesis
      by (simp add: card_S)
  qed
  show "\<exists>S :: party set.
      S \<in> {S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>}"
    using thresh by (intro exI[of _ ?S]) simp
qed

typedef vote_quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real n / 2\<rceil>}"
proof -
  text \<open>Proof sketch: @{term "UNIV - {broadcaster}"} again provides all non-broadcaster parties.
    The global inequality @{term "2 \<le> n"} ensures that this set reaches the vote threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real n / 2\<rceil>"
  proof -
    have "real (n - 1) >= real n / 2"
      using two_parties by linarith
    then have "\<lceil>real (n - 1)\<rceil> >= \<lceil>real n / 2\<rceil>"
      by (intro ceiling_mono)
    then have "n - 1 >= \<lceil>real n / 2\<rceil>"
      by simp
    then show ?thesis
      by (simp add: card_S)
  qed
  show "\<exists>S :: party set.
      S \<in> {S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real n / 2\<rceil>}"
    using thresh by (intro exI[of _ ?S]) simp
qed

typedef quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + f - 1) / 2\<rceil>}"
proof -
  text \<open>Proof sketch: use @{term "UNIV - {broadcaster}"} once more. The global inequalities
    @{term fault_bound} and @{term "2 \<le> n"} imply that @{term "n - 1"} dominates the quorum
    threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real (n + f - 1) / 2\<rceil>"
  proof -
    have "real (n - 1) >= real (n + f - 1) / 2"
      using fault_bound two_parties by linarith
    then have "\<lceil>real (n - 1)\<rceil> >= \<lceil>real (n + f - 1) / 2\<rceil>"
      by (intro ceiling_mono)
    then have "n - 1 >= \<lceil>real (n + f - 1) / 2\<rceil>"
      by simp
    then show ?thesis
      by (simp add: card_S)
  qed
  show "\<exists>S :: party set.
      S \<in> {S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + f - 1) / 2\<rceil>}"
    using thresh by (intro exI[of _ ?S]) simp
qed

typedef amplification_quorum =
  "{S :: party set. card S >= f + 1}"
proof -
  text \<open>Proof sketch: the full universe has cardinality @{term n}, and the global inequality
    @{thm [source] fault_bound} implies @{prop "n >= f + 1"}.\<close>
  have thresh: "card (UNIV :: party set) >= f + 1"
  proof -
    have "n >= f + 1"
      using fault_bound by linarith
    then show ?thesis
      by (simp add: n_def)
  qed
  show "\<exists>S :: party set. S \<in> {S :: party set. card S >= f + 1}"
    using thresh by (intro exI[of _ "UNIV :: party set"]) simp
qed

typedef commit_quorum =
  "{S :: party set. card S >= 2 * f + 1}"
proof -
  text \<open>Proof sketch: the full universe again witnesses nonemptiness because the global inequality
    @{thm [source] fault_bound} implies @{term "n >= 2 * f + 1"}.\<close>
  have thresh: "card (UNIV :: party set) >= 2 * f + 1"
  proof -
    have "n >= 2 * f + 1"
      using fault_bound by linarith
    then show ?thesis
      by (simp add: n_def)
  qed
  show "\<exists>S :: party set. S \<in> {S :: party set. card S >= 2 * f + 1}"
    using thresh by (intro exI[of _ "UNIV :: party set"]) simp
qed

section \<open>Intersection properties\<close>

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
  have card_U: "card (UNIV - {broadcaster} :: party set) = n - 1"
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

section "Mapping to the abstract domain model"

definition opt_quorum_member :: "opt_quorum => party => bool" where
  "opt_quorum_member Q p \<equiv> p \<in> Rep_opt_quorum Q"

definition vote_quorum_member :: "vote_quorum => party => bool" where
  "vote_quorum_member Q p \<equiv> p \<in> Rep_vote_quorum Q"

definition quorum_member :: "quorum => party => bool" where
  "quorum_member Q p \<equiv> p \<in> Rep_quorum Q"

definition amplification_quorum_member :: "amplification_quorum => party => bool" where
  "amplification_quorum_member Q p \<equiv> p \<in> Rep_amplification_quorum Q"

definition commit_quorum_member :: "commit_quorum => party => bool" where
  "commit_quorum_member Q p \<equiv> p \<in> Rep_commit_quorum Q"

interpretation axiomatic_abstract_domain_model:
  abstract_domain_model faulty opt_quorum_member vote_quorum_member
    quorum_member amplification_quorum_member commit_quorum_member
  text \<open>Proof sketch: unfold the five membership definitions and use the representation theorems of
    the typedefs to recover the concrete threshold facts for each quorum object. The global
    domain-model interpretation above should then supply the cardinality lemmas behind the
    abstract obligations. The existential quorum-object obligations should be witnessed via
    @{term "Abs_vote_quorum (Rep_opt_quorum opQ - faulty)"} and
    @{term "Abs_amplification_quorum (Rep_commit_quorum coQ - faulty)"}. This interpretation is
    left unproved for now.\<close>
  sorry

end