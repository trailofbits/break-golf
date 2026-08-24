/-
A submission that verifies and wins nothing.

The null adversary: ask no questions, always answer "ideal". Its signed advantage
is exactly 0, so `Wins budget 0` is *true* and provable, the file elaborates
cleanly, and `#print axioms` reports only propext, Classical.choice, Quot.sound.

It is still worth nothing. score = log2(budget / advantage^e) is infinite at
advantage 0: an attack that refutes 0 bits of security refutes nothing. The board
rejects the submission form for it (`non_positive`) rather than the Lean.

Use this to test the honest-but-worthless path: a real proof of a real statement
that is not a break.
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
