theory AbstractDomainModel
  imports Complex_Main Timed_Methods
begin

locale abstract_domain_model =
  fixes broadcaster :: "'p::finite"
    and faulty :: "'p set"
    and opt_quorum_member :: "'opQ \<Rightarrow> 'p \<Rightarrow> bool"
    and vote_quorum_member :: "'vtQ \<Rightarrow> 'p \<Rightarrow> bool"
    and quorum_member :: "'quQ \<Rightarrow> 'p \<Rightarrow> bool"
    and amplification_quorum_member :: "'amQ \<Rightarrow> 'p \<Rightarrow> bool"
    and commit_quorum_member :: "'coQ \<Rightarrow> 'p \<Rightarrow> bool"
  assumes opt_quorum_intersection:
      "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ\<^sub>1 p \<and> opt_quorum_member opQ\<^sub>2 p)"
    and opt_vote_quorum_intersection:
      "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> vote_quorum_member vtQ p)"
    and opt_quorum_intersects_quorum:
      "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> opt_quorum_member opQ p \<and> quorum_member quQ p)"
    and quorum_intersection:
      "broadcaster \<in> faulty \<longrightarrow> (\<exists>p. p \<notin> faulty \<and> quorum_member quQ\<^sub>1 p \<and> quorum_member quQ\<^sub>2 p)"
    and vote_quorum_has_nonfaulty_member:
      "\<exists>p. p \<notin> faulty \<and> vote_quorum_member vtQ p"
    and amplification_quorum_has_nonfaulty_member:
      "\<exists>p. p \<notin> faulty \<and> amplification_quorum_member amQ p"
    and opt_quorum_contains_vote_quorum:
      "broadcaster \<in> faulty \<longrightarrow> (\<exists>vtQ. \<forall>p. vote_quorum_member vtQ p \<longrightarrow> p \<notin> faulty \<and> opt_quorum_member opQ p)"
    and commit_quorum_contains_amplification_quorum:
      "\<exists>amQ. \<forall>p. amplification_quorum_member amQ p \<longrightarrow> p \<notin> faulty \<and> commit_quorum_member coQ p"

end

