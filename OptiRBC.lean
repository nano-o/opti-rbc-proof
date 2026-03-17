import Veil

veil module OptiRBC

/-
Liveness Strategy: the state-space is finite and non-faulty actions are monotonic, so eventually no more non-faulty actions are enabled. At this point we show the liveness conditions must hold.
-/

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

type party      -- protocol participants
type val        -- values that can be proposed

-- Quorum types (abstract witnesses for threshold sets of parties)
type opt_quorum
type maj_quorum
type classic_quorum
type amplification_quorum
type commit_quorum

--------------------------------------------------------------------------------
-- Immutable state (theory parameters)
--------------------------------------------------------------------------------

immutable individual broadcaster : party
immutable relation faulty : party → Bool

immutable relation opt_quorum_member : opt_quorum → party → Bool
immutable relation maj_quorum_member : maj_quorum → party → Bool
immutable relation classic_quorum_member : classic_quorum → party → Bool
immutable relation amplification_quorum_member : amplification_quorum → party → Bool
immutable relation commit_quorum_member : commit_quorum → party → Bool

--------------------------------------------------------------------------------
-- Mutable state
--------------------------------------------------------------------------------

relation proposal : val → Bool
relation echo : party → val → Bool
relation vote : party → val → Bool
relation ack : party → val → Bool
relation ready : party → val → Bool
relation committed : party → val → Bool

immutable individual pv : val -- proposal of the non-faulty broadcaster (if any)

#gen_state

--------------------------------------------------------------------------------
-- Abstract domain model assumptions (quorum intersection properties)
--------------------------------------------------------------------------------

-- assumption [faulty_broadcaster]
--   faulty broadcaster -- temporary

-- classic, vote, and optimistic quorums do not contain the broadcaster
assumption [broadcaster_not_in_classic_quorum]
  ∀ (q : classic_quorum), ¬ classic_quorum_member q broadcaster

assumption [broadcaster_not_in_maj_quorum]
  ∀ (q : maj_quorum), ¬ maj_quorum_member q broadcaster

assumption [broadcaster_not_in_opt_quorum]
  ∀ (q : opt_quorum), ¬ opt_quorum_member q broadcaster

-- assumption [test]
--   ∀ q, ¬ commit_quorum_member q broadcaster

-- the set of non-faulty parties satisfies all the quorum thresholds except the optimistic quorum threshold

assumption [non_faulty_commit_quorum]
  (∃ (q : commit_quorum), ∀ p, commit_quorum_member q p → ¬ faulty p)

assumption [non_faulty_amplification_quorum]
  (∃ (q : amplification_quorum), ∀ p, amplification_quorum_member q p → ¬ faulty p)

assumption [non_faulty_maj_quorum]
  (∃ (q : maj_quorum), ∀ p, maj_quorum_member q p → ¬ faulty p)

assumption [non_faulty_classic_quorum]
  (∃ (q : classic_quorum), ∀ p, classic_quorum_member q p → ¬ faulty p)

-- An optimistic quorum contains a non-faulty member.
assumption [opt_quorum_has_nonfaulty_member]
  ∀ (q : opt_quorum), ∃ p, ¬ faulty p ∧ opt_quorum_member q p

-- When the broadcaster is faulty, any two optimistic quorums share a
-- non-faulty member.
assumption [opt_quorum_intersection]
  ∀ (q₁ q₂ : opt_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ opt_quorum_member q₁ p ∧ opt_quorum_member q₂ p)

-- When the broadcaster is faulty, an optimistic quorum and a majority
-- quorum share a non-faulty member.
assumption [opt_maj_quorum_intersection]
  ∀ (q₁ : opt_quorum) (q₂ : maj_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ opt_quorum_member q₁ p ∧ maj_quorum_member q₂ p)

-- When the broadcaster is faulty, an optimistic quorum and a classic quorum
-- share a non-faulty member.
assumption [opt_quorum_intersects_classic_quorum]
  ∀ (q₁ : opt_quorum) (q₂ : classic_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ opt_quorum_member q₁ p ∧ classic_quorum_member q₂ p)

-- When the broadcaster is faulty, any two classic quorums share a non-faulty member.
assumption [classic_quorum_intersection]
  ∀ (q₁ q₂ : classic_quorum),
    faulty broadcaster →
      (∃ p, ¬ faulty p ∧ classic_quorum_member q₁ p ∧ classic_quorum_member q₂ p)

-- Every classic quorum contains a non-faulty member.
assumption [quorum_not_faulty]
  ∀ (q : classic_quorum), ∃ p, ¬ faulty p ∧ classic_quorum_member q p

-- Every majority quorum contains a non-faulty member.
assumption [maj_quorum_has_nonfaulty_member]
  ∀ (q : maj_quorum), ∃ p, ¬ faulty p ∧ maj_quorum_member q p

-- Every amplification quorum contains a non-faulty member.
assumption [amplification_quorum_has_nonfaulty_member]
  ∀ (q : amplification_quorum), ∃ p, ¬ faulty p ∧ amplification_quorum_member q p

-- When the broadcaster is faulty, for any optimistic quorum there exists a
-- majority quorum whose members are all non-faulty and in the optimistic quorum.
assumption [opt_quorum_contains_maj_quorum]
  ∀ (q : opt_quorum),
    faulty broadcaster →
      (∃ (q' : maj_quorum), ∀ p, maj_quorum_member q' p → ¬ faulty p ∧ opt_quorum_member q p)

-- For any commit quorum there exists an amplification quorum whose members
-- are all non-faulty and in the commit quorum.
assumption [commit_quorum_contains_non_faulty_amplification_quorum]
  ∀ (q : commit_quorum),
    ∃ (q' : amplification_quorum), ∀ p, amplification_quorum_member q' p → ¬ faulty p ∧ commit_quorum_member q p

--------------------------------------------------------------------------------
-- Initialization
--------------------------------------------------------------------------------

after_init {
  proposal V := false
  echo P V := false
  vote P V := false
  ack P V := false
  ready P V := false
  committed P V := false
}

--------------------------------------------------------------------------------
-- Protocol actions
--------------------------------------------------------------------------------

-- The broadcaster proposes.
action propose {
  require ∀ v, ¬ proposal v
  proposal pv := true
}
-- Enabledness condition:
ghost relation propose_enabled :=
  ¬ faulty broadcaster ∧ ∀  v, ¬ proposal v

-- A non-broadcaster party echoes a proposed value (at most one echo per party).
action echoStep (p : party) (v : val) {
  require p ≠ broadcaster
  require ∀ v', ¬ echo p v'
  require proposal v
  echo p v := true
}
-- Enabledness condition:
ghost relation echo_enabled (p : party) (v : val):=
   ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ echo p v') ∧ proposal v

-- A non-broadcaster party votes for a value after seeing a majority-quorum
-- of echoes (unless it has already voted for some other value).
action voteStep (p : party) (v : val) {
  require p ≠ broadcaster
  require ∀ v', ¬ vote p v'
  require ∃ (q : maj_quorum), ∀ p', maj_quorum_member q p' → echo p' v
  vote p v := true
}
ghost relation vote_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ vote p v') ∧ (∃ (q : maj_quorum), ∀ p', maj_quorum_member q p' → echo p' v)

-- A non-broadcaster party sends an ack after seeing either a quorum of votes
-- or a quorum of echoes (unless it has already acked some other value).
action ackStep (p : party) (v : val) {
  require p ≠ broadcaster
  require ∀ v', ¬ ack p v'
  require (∃ (q : classic_quorum), ∀ q', classic_quorum_member q q' → vote q' v)
       ∨ (∃ (q : classic_quorum), ∀ q', classic_quorum_member q q' → echo q' v)
  ack p v := true
}
ghost relation ack_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ ack p v') ∧
    ((∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' → vote p' v)
      ∨ (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' → echo p' v))

-- A non-broadcaster party becomes ready after seeing either a quorum of acks
-- or an amplification-quorum of readys (unless it has already become ready for some other value).
action readyStep (p : party) (v : val) {
  require ∀ v', ¬ ready p v'
  require (∃ (q : classic_quorum), ∀ q', classic_quorum_member q q' → ack q' v)
       ∨ (∃ (q : amplification_quorum), ∀ q', amplification_quorum_member q q' → ready q' v)
  ready p v := true
}
ghost relation ready_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ (∀ v', ¬ ready p v') ∧
    ((∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' → ack p' v)
      ∨ (∃ (q : amplification_quorum), ∀ p', amplification_quorum_member q p' → ready p' v))

-- Optimistic commit: a non-broadcaster party commits after seeing an
-- optimistic-quorum of echoes (unless it has already committed some other value).
action optCommitStep (p : party) (v : val) {
  require p ≠ broadcaster
  require ∀ v', ¬ committed p v'
  require ∃ (q : opt_quorum), ∀ q', opt_quorum_member q q' → echo q' v
  committed p v := true
}
ghost relation optCommit_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ p ≠ broadcaster ∧ (∀ v', ¬ committed p v') ∧
    (∃ (q : opt_quorum), ∀ p', opt_quorum_member q p' → echo p' v)

-- Normal commit: a non-broadcaster party commits after seeing a
-- commit-quorum of readys (unless it has already committed some other value).
action commitStep (p : party) (v : val) {
  require ∀ v', ¬ committed p v'
  require ∃ (q : commit_quorum), ∀ q', commit_quorum_member q q' → ready q' v
  committed p v := true
}
ghost relation commit_enabled (p : party) (v : val) :=
  ¬ faulty p ∧ (∀ v', ¬ committed p v')
  ∧ (∃ (q : commit_quorum), ∀ p', commit_quorum_member q p' → ready p' v)

-- Byzantine step: a faulty broadcaster can set proposal arbitrarily.
action byzProposal {
  require faulty broadcaster
  proposal V := *
}

-- Byzantine step: a faulty party can set its echo/vote/ack/ready arbitrarily.
action byzParty (p : party) {
  require faulty p
  echo p V := *
  vote p V := *
  ack p V := *
  ready p V := *
}

-- Check the liveness properties

action check_validity (p : party) {
  require ¬ faulty broadcaster
  require ¬ faulty p
  require ¬ propose_enabled
  require ∀ p v, ¬ echo_enabled p v
  require ∀ p v, ¬ vote_enabled p v
  require ∀ p v, ¬ ack_enabled p v
  require ∀ p v, ¬ ready_enabled p v
  require ∀ p v, ¬ commit_enabled p v
  assert committed p pv
}

action check_totality (p1 : party) (p2 : party) (v : val) {
  require ¬ faulty p1 ∧ ¬ faulty p2
  require committed p1 v
  require ¬ propose_enabled
  require ∀ p v, ¬ echo_enabled p v
  require ∀ p v, ¬ vote_enabled p v
  require ∀ p v, ¬ ack_enabled p v
  require ∀ p v, ¬ ready_enabled p v
  require ∀ p v, ¬ commit_enabled p v
  assert committed p2 v
}

-- Invariants

-- inv0: non-faulty parties never echo, vote, ack, ready, or commit two different values
invariant [inv0]
  ∀ p v1 v2, ¬ faulty p ∧ v1 ≠ v2 →
    ¬ (echo p v1 ∧ echo p v2)
    ∧ ¬ (vote p v1 ∧ vote p v2)
    ∧ ¬ (ack p v1 ∧ ack p v2)
    ∧ ¬ (ready p v1 ∧ ready p v2)
    ∧ ¬ (committed p v1 ∧ committed p v2)

-- inv1: If a non-faulty party commits value v, then either
--   (a) an amplification quorum of non-faulty parties are ready for v, or
--   (b) the non-faulty members of some optimistic quorum have echoed v.
invariant [inv1]
  ∀ p v, ¬ faulty p ∧ committed p v →
    (∃ (q : amplification_quorum), ∀ p', amplification_quorum_member q p' → ¬ faulty p' ∧ ready p' v)
    ∨ (∃ (q : opt_quorum), ∀ p', opt_quorum_member q p' ∧ ¬ faulty p' → echo p' v)

-- inv2: If a non-faulty party is ready for v, then the non-faulty members of
-- some classic quorum have acked v.
invariant [inv2]
  ∀ p v, ¬ faulty p ∧ ready p v →
    (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' ∧ ¬ faulty p' → ack p' v)

-- inv3: If a non-faulty party has acked v, then either
--   (a) the non-faulty members of some classic quorum have all voted for v, or
--   (b) the non-faulty members of some classic quorum have all echoed v.
invariant [inv3]
  ∀ p v, ¬ faulty p ∧ ack p v →
    (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' ∧ ¬ faulty p' → vote p' v)
    ∨ (∃ (q : classic_quorum), ∀ p', classic_quorum_member q p' ∧ ¬ faulty p' → echo p' v)

-- inv5: if a non-faulty party votes for v, then the non-faulty members of some majority quorum have echoed v.
invariant [inv5]
  ∀ p v, ¬ faulty p ∧ vote p v →
    (∃ (q : maj_quorum), ∀ p', maj_quorum_member q p' ∧ ¬ faulty p' → echo p' v)

-- Agreement: no two non-faulty parties commit different values.
safety [agreement]
  ∀ p1 p2 v1 v2, ¬ faulty p1 ∧ ¬ faulty p2 ∧ committed p1 v1 ∧ committed p2 v2 → v1 = v2

-- inv7: if the broadcaster is not faulty, then it makes at most one proposal and non-faulty parties only echo, vote, ack, ready, or commit the value proposed by the broadcaster.
invariant [inv7] ¬ faulty broadcaster →
  (∀ v , proposal v → v = pv)
  ∧ ∀ p v, ¬ faulty p →
    (echo p v → proposal v) ∧
    (vote p v → proposal v) ∧
    (ack p v → proposal v) ∧
    (ready p v → proposal v) ∧
    (committed p v → proposal v)

-- The next two are not strictly necessary but it seems they speed things up.

-- inv4: no two non-faulty parties are ready for different values.
invariant [inv4]
  ∀ p1 p2 v1 v2, ¬ faulty p1 ∧ ¬ faulty p2 ∧ ready p1 v1 ∧ ready p2 v2 → v1 = v2

-- inv6: if an optimistic quorum has echoed v, then no non-faulty party votes for a different value.
invariant [inv6] ∀ v,
  (∃ (q : opt_quorum), ∀ p', opt_quorum_member q p' ∧ ¬ faulty p' → echo p' v) →
    (∀ p v', ¬ faulty p ∧ vote p v' → v' = v)

-- inv8: if an optimistic quorum echoes some value, then no non-faulty party
-- acks a different value.
invariant [inv8] ∀ (q : opt_quorum) (v2 : val),
  (∀ p2, opt_quorum_member q p2 ∧ ¬ faulty p2 → echo p2 v2) →
    (∀ p1 v1, ¬ faulty p1 ∧ v1 ≠ v2 → ¬ ack p1 v1)

-- inv9: if the broadcaster is not faulty and a non-faulty party commits, then
-- the broadcaster has proposed.
invariant [inv9] ∀ p v,
  ¬ faulty broadcaster ∧ ¬ faulty p ∧ committed p v → proposal pv

set_option veil.smt.timeout 30 
set_option veil.smt.finiteModelFind false

#gen_spec

-- Did not terminate in any reasonable time:
-- #check_invariants

end OptiRBC
