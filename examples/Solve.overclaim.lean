/-
The same null adversary, submitted with advantage 1/1 instead of 0/1.

Nothing about the adversary changed. Only the number on the form did — and that
number is substituted into `Challenge.SpoC128DS.score`, which appears inside the
type of `wins`. So the proposition became "this adversary achieves advantage 1",
and the proof stops discharging it:

    error: unsolved goals
    ⊢ False

Two independent rejections, which is the point:

  1. the build fails, because the claim is now a stronger theorem; and
  2. even if a build were coaxed through, `#print axioms` reports `sorryAx`,
     which is not in the challenge's permitted list.

Use this to test the over-claim path.
-/
import Golf.Challenges.SpoC128DS.Challenge

namespace Solution.SpoC128DS

open RandomSystems.CR18
open RandomSystems.Golf.Instances.SpoC128DS

def solution : Challenge.SpoC128DS.Solution where
  strategy := fun _ _ => none
  verdict := fun _ => false
  wins := by
    have h : Challenge.SpoC128DS.score.advantage = 0 := by
      simp [Golf.Score.advantage, Challenge.SpoC128DS.score]
    rw [h]
    exact Golf.Attack.wins_zero_of_reject _ _ (fun _ _ _ => rfl)

end Solution.SpoC128DS
