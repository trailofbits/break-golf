/-
`Solve.lean` — the file you submit.

Provide exactly one declaration, `solution`, at the type the challenge pins.
The statement is not yours to change; `budget` and the claimed advantage come
from the submission form and sit inside that type.

Before submitting: build locally, and check the axiom footprint against
`permitted_axioms` in the challenge config. `native_decide` is not part of the
accepted proof surface, and a proof that only closes with a raised
`maxHeartbeats` is likely to exceed the verifier timeout.
-/
import Challenges.SpoC128.Challenge

namespace Solution.SpoC128

open RandomSystems.CR18
open Golf.Instances.SpoC128

def solution : Challenge.SpoC128.Solution where
  strategy := fun _ _ => none
  verdict := fun _ => false
  wins := by
    sorry

end Solution.SpoC128
