/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Golf.Game
import RandomSystems.SpoC.Distinguishing

/-!
# SpoC-128: the worked instance, and the adequacy check for `Golf.Game`

This file exists to prove that `Golf.Game` is an *abstraction* of the game the
repository already has, not a second modelling stack beside it.  It adds no
mathematics: it packages `RandomSystems.SpoC`'s existing real and ideal systems
as a `Game`, its existing environment and verdict as an `Attack` at budget `3`,
and then discharges the win condition by `attack_distinguishing_advantage`
*verbatim* — no restatement, no re-proof.

`golfed_attack_is_spoc_attack` is the receipt: the generic denotation is the
SpoC distinguisher on the nose.
-/

namespace Golf.Instances.SpoC128

open RandomSystems.CR18
open RandomSystems.SpoC

/-! ## The trusted game -/

/-- SpoC-128 as a board game: real SpoC against the replay-only ideal, over the
public permutation. -/
@[reducible] noncomputable def game : Golf.Game where
  Param := Equiv.Perm RandomSystems.SpoC.State
  Query := RandomSystems.SpoC.Query
  Response := RandomSystems.SpoC.Response
  real := RandomSystems.SpoC.spocPDS
  ideal := RandomSystems.SpoC.idealSystem

/-! ## Par: the reference submission -/

/-- The existing key-recovery attack, in submission normal form.  Note it carries
no query count: the same strategy is scored at whatever budget it can carry, and
`3` appears below only as the point this submission claims. -/
def parAttack : Golf.Attack game where
  strategy := RandomSystems.SpoC.attackEnvironment
  verdict := RandomSystems.SpoC.verificationVerdict

/-- **Adequacy receipt.**  At three queries the generic denotation of `parAttack`
*is* the SpoC distinguisher — definitionally, not up to an equivalence. -/
theorem golfed_attack_is_spoc_attack (p : game.Param) :
    parAttack.distinguisher 3 p = RandomSystems.SpoC.attackDistinguisher p :=
  rfl

/-- **Adequacy receipt.**  The generic advantage is the SpoC advantage. -/
theorem golfed_advantage_is_spoc_advantage (p : game.Param) :
    parAttack.advantage 3 p =
      RandomSystems.SpoC.distinguishingAdvantage p
        (RandomSystems.SpoC.attackDistinguisherDistribution p) :=
  rfl

/-! ## The attack stops, so its row extends -/

/-- `attackEnvironment` issues nothing once it has seen three answers — a finite
pattern match, which is all `stalls_of_silent_above` asks for. -/
theorem attackEnvironment_silent_above (p : Equiv.Perm RandomSystems.SpoC.State)
    (ys : List (Option RandomSystems.SpoC.Response)) (h : 3 ≤ ys.length) :
    RandomSystems.SpoC.attackEnvironment p ys = none := by
  rcases ys with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · cases a <;> cases b <;> simp [RandomSystems.SpoC.attackEnvironment]

theorem parAttack_stopsAt : parAttack.StopsAt 3 := fun p =>
  Golf.stalls_of_silent_above (attackEnvironment_silent_above p)

/-- The reference attack holds advantage `1` at **every** budget of three or
more — the upper half of its curve, for free, from the single proved point. -/
theorem parAttack_wins_above (q : ℕ) (hq : 3 ≤ q) : parAttack.Wins q 1 :=
  Golf.Attack.wins_mono_of_stops parAttack_stopsAt hq
    (fun p => le_of_eq (RandomSystems.SpoC.attack_distinguishing_advantage p).symm)

/-- Par for this challenge: three queries, advantage one. -/
def parScore : Golf.Score where
  budget := 3
  advNum := 1
  advDen := 1

/-- The reference submission, discharged by the existing SpoC endpoint with no
restatement of the mathematics.

`parAttack_wins_above` shows the same attack holds this score at every larger
budget too.  The remaining half of the step curve — that the advantage is not
*negative* below three queries — is a separate obligation and is not claimed
here; see `Golf.Attack.achieves_step_of_stops`. -/
noncomputable def parSubmission : Golf.Submission game where
  attack := parAttack
  score := parScore
  wins := by
    intro p
    have hscore : parScore.advantage = 1 := by
      simp [Golf.Score.advantage, parScore]
    rw [hscore]
    exact le_of_eq (RandomSystems.SpoC.attack_distinguishing_advantage p).symm

end Golf.Instances.SpoC128
