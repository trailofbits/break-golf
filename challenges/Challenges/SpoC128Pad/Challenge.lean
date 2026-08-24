/-
TRUSTED. The submission's entire type lives here, and the verifier builds its own
copy.

The score is **not** a form field the platform injects. A submission declares its
own `budget`, `advNum` and `advDen` as ordinary Lean definitions, and the type
below is *indexed by them*:

    def solution : Challenge.SpoC128Pad.Solution budget advNum advDen

So the numbers are inside the proposition by construction, and the verifier reads
them back out of Lean with `#eval` rather than parsing them out of an issue.
There is no way for a claimed score and a proved score to differ, because they
are the same three definitions.
-/
import Golf.Instances.SpoC128Pad.Interface

namespace Challenge.SpoC128Pad

open RandomSystems
open RandomSystems.CR18
open Golf.Instances.SpoC128Pad

/-- **What a submission is**, indexed by the score it claims.

`budget` is the query count and `advNum / advDen` the advantage. Both appear in
the type of `wins`, so claiming a smaller budget or a larger advantage changes
the theorem rather than the label on it. -/
structure Solution (budget advNum advDen : Nat) where
  /-- The adaptive query strategy: given the answers so far, the next query. -/
  strategy : game.Param → PFunDDS.DDE game.Query game.Response
  /-- The verdict, read off the observed transcript. -/
  verdict : List (game.Query × Option game.Response) → Bool
  /-- The advantage must be a positive rational to be scoreable. -/
  advNum_pos : 0 < advNum
  advDen_pos : 0 < advDen
  /-- **The win condition.** Allowed `budget` queries, at every public parameter,
  the signed advantage between the ideal and real worlds is at least
  `advNum / advDen`. -/
  wins : Golf.Attack.Wins (G := game) ⟨strategy, verdict⟩ budget
    ((advNum : Real) / (advDen : Real))

end Challenge.SpoC128Pad
