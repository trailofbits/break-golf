/-
The reference submission for `spoc128`: the published three-query key recovery.

The score lives here, in Lean, as three ordinary definitions. The type of
`solution` is indexed by them, so they are part of what is proved — not a claim
attached to it. The verifier reads them back with `#eval`.
-/
import Challenges.SpoC128.Challenge

namespace Solution.SpoC128

open RandomSystems
open RandomSystems.CR18
open Golf.Instances.SpoC128

/-- Queries spent. -/
def budget : Nat := 3
/-- Advantage numerator. -/
def advNum : Nat := 1
/-- Advantage denominator. -/
def advDen : Nat := 1

def solution : Challenge.SpoC128.Solution budget advNum advDen where
  strategy := RandomSystems.SpoC.attackEnvironment
  verdict := RandomSystems.SpoC.verificationVerdict
  advNum_pos := by decide
  advDen_pos := by decide
  wins := by
    intro p
    have h : ((advNum : Real) / (advDen : Real)) = 1 := by
      norm_num [advNum, advDen]
    rw [h]
    exact le_of_eq (RandomSystems.SpoC.attack_distinguishing_advantage p).symm

end Solution.SpoC128
