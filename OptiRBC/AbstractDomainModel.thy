theory AbstractDomainModel
  imports Complex_Main Timed_Methods
begin

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

