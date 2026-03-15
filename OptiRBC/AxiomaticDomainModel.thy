theory AxiomaticDomainModel
  imports DomainModel
begin

text \<open>This theory fixes one global domain model. Unlike the locale-based development,
  the quorum carriers below are genuine HOL types obtained from global constants.\<close>

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
  fault_bound: "3 * f < n"
  and two_parties: "2 \<le> n"

interpretation axiomatic_domain_model: domain_model faulty n f broadcaster
proof (intro domain_model.intro)
  text \<open>Proof sketch: unfold the global definitions of @{term n} and @{term f}. The remaining
    arithmetic obligation is the global inequality @{term "3 * f < n"}.\<close>
  have "3 * f < n"
    by (rule fault_bound)
  then show "3 * card faulty < card (UNIV :: party set)"
    by (simp add: n_def f_def)
  show "n \<equiv> card (UNIV :: party set)"
    by (simp add: n_def)
  show "f \<equiv> card faulty"
    by (simp add: f_def)
qed


typedef opt_quorum =
  "{S :: party set. broadcaster \<notin> S \<and> card S >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>}"
proof -
  text \<open>Proof sketch: @{term "UNIV - {broadcaster}"} excludes @{term broadcaster} and has
    cardinality @{term "n - 1"}. The global inequality @{term "3 * f < n"} makes this large
    enough for the optimistic threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have "3 * f < n"
    by (rule fault_bound)
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real (n + 2 * f - 2) / 2\<rceil>"
  proof -
    have "real (n - 1) >= real (n + 2 * f - 2) / 2"
      using \<open>3 * f < n\<close> by linarith
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
  have "2 \<le> n"
    by (rule two_parties)
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real n / 2\<rceil>"
  proof -
    have "real (n - 1) >= real n / 2"
      using \<open>2 \<le> n\<close> by linarith
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
    @{term "3 * f < n"} and @{term "2 \<le> n"} imply that @{term "n - 1"} dominates the quorum
    threshold.\<close>
  let ?S = "UNIV - {broadcaster} :: party set"
  have "3 * f < n"
    by (rule fault_bound)
  have "2 \<le> n"
    by (rule two_parties)
  have card_S: "card ?S = n - 1"
    by (simp add: n_def)
  have thresh: "card ?S >= \<lceil>real (n + f - 1) / 2\<rceil>"
  proof -
    have "real (n - 1) >= real (n + f - 1) / 2"
      using \<open>3 * f < n\<close> \<open>2 \<le> n\<close> by linarith
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
    @{term "3 * f < n"} implies @{term "n >= f + 1"}.\<close>
  have "3 * f < n"
    by (rule fault_bound)
  have thresh: "card (UNIV :: party set) >= f + 1"
  proof -
    have "n >= f + 1"
      using \<open>3 * f < n\<close> by linarith
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
    @{term "3 * f < n"} implies @{term "n >= 2 * f + 1"}.\<close>
  have "3 * f < n"
    by (rule fault_bound)
  have thresh: "card (UNIV :: party set) >= 2 * f + 1"
  proof -
    have "n >= 2 * f + 1"
      using \<open>3 * f < n\<close> by linarith
    then show ?thesis
      by (simp add: n_def)
  qed
  show "\<exists>S :: party set. S \<in> {S :: party set. card S >= 2 * f + 1}"
    using thresh by (intro exI[of _ "UNIV :: party set"]) simp
qed


definition axiomatic_opt_quorum_member :: "opt_quorum => party => bool" where
  "axiomatic_opt_quorum_member Q p \<equiv> p \<in> Rep_opt_quorum Q"

definition axiomatic_vote_quorum_member :: "vote_quorum => party => bool" where
  "axiomatic_vote_quorum_member Q p \<equiv> p \<in> Rep_vote_quorum Q"

definition axiomatic_quorum_member :: "quorum => party => bool" where
  "axiomatic_quorum_member Q p \<equiv> p \<in> Rep_quorum Q"

definition axiomatic_amplification_quorum_member :: "amplification_quorum => party => bool" where
  "axiomatic_amplification_quorum_member Q p \<equiv> p \<in> Rep_amplification_quorum Q"

definition axiomatic_commit_quorum_member :: "commit_quorum => party => bool" where
  "axiomatic_commit_quorum_member Q p \<equiv> p \<in> Rep_commit_quorum Q"

interpretation axiomatic_abstract_domain_model:
  abstract_domain_model faulty axiomatic_opt_quorum_member axiomatic_vote_quorum_member
    axiomatic_quorum_member axiomatic_amplification_quorum_member axiomatic_commit_quorum_member
  text \<open>Proof sketch: unfold the five membership definitions and use the representation theorems of
    the typedefs to recover the concrete threshold facts for each quorum object. The global
    domain-model interpretation above should then supply the cardinality lemmas behind the
    abstract obligations. The existential quorum-object obligations should be witnessed via
    @{term "Abs_vote_quorum (Rep_opt_quorum opQ - faulty)"} and
    @{term "Abs_amplification_quorum (Rep_commit_quorum coQ - faulty)"}. This interpretation is
    left unproved for now.\<close>
  sorry

end


