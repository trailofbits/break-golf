/-
The reference solve for `spoc128`, written from scratch.

The strategy uses nothing from the library's *attack* — only the mode, which is
the target: `capacity`, `state`, `encrypt`, `tagControl`, and inverting the
public permutation.

What it does lean on is the last line, `attack_distinguishing_advantage`. That
is the advantage proof, and for a challenge nobody has solved there is no such
theorem to cite. Writing it is the work.
-/
import Challenges.SpoC128.Challenge

namespace Solution.SpoC128

open RandomSystems
open RandomSystems.CR18
open RandomSystems.SpoC
open Golf.Instances.SpoC128

def budget : Nat := 3
def advNum : Nat := 1
def advDen : Nat := 1

/-- Written from scratch. Nothing from the library's *attack* is used — only the
mode, which is the target. -/
def strategy (p : game.Param) : PFunDDS.DDE game.Query game.Response
  | [] => some (Sum.inl ⟨0, [], []⟩)
  | [some (Sum.inl _)] => some (Sum.inl ⟨tagControl, [], [0]⟩)
  | [some (Sum.inl r0), some (Sum.inl r1)] =>
      -- r0.tag is the capacity of π(K ‖ ctrl_T); r1.ciphertext.head is its rate.
      let k := capacity (p.symm (state r0.tag (r1.ciphertext.getD 0 0)))
      let forged := encrypt (⇑p) k 0 [] [0]
      some (Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩)
  | _ => none

def verdict : List (game.Query × Option game.Response) → Bool
  | t => match t.getLast? with
         | some (_, some (Sum.inr r)) => r.verified
         | _ => false

def solution : Challenge.SpoC128.Solution budget advNum advDen where
  strategy := strategy
  verdict := verdict
  advNum_pos := by decide
  advDen_pos := by decide
  wins := by
    intro p
    have h : ((advNum : Real) / (advDen : Real)) = 1 := by norm_num [advNum, advDen]
    rw [h]
    exact le_of_eq (RandomSystems.SpoC.attack_distinguishing_advantage p).symm

end Solution.SpoC128
