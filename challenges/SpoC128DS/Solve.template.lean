/-
Skeleton for `spoc128-ds`. It compiles and wins nothing — the strategy asks no
questions. Replace `strategy`, `verdict`, and the three numbers, then prove
`wins`.

One trap worth knowing before you start: an exact replay of an earlier
encryption is accepted by the *ideal* world too, so replaying wins nothing. You
have to make the real decryption oracle accept something that is not a replay.
-/
import Challenges.SpoC128DS.Challenge

namespace Solution.SpoC128DS

open RandomSystems
open RandomSystems.CR18
open RandomSystems.SpoC
open Golf.Instances.SpoC128DS

/-- Your score. These three appear in the type of `wins` below, so they are part
of what you prove — not a claim about it. -/
def budget : Nat := 1
def advNum : Nat := 1
def advDen : Nat := 1

/-- A query carries a proof that its nonce is legal: `n &&& 0xF0 = 0`. Build one
with `by decide`; an illegal nonce will not typecheck, which is the whole point
of this variant. -/
def encQuery (nonce : Block) (ad pt : List Block) (h : ValidNonce nonce) : game.Query :=
  ⟨Sum.inl ⟨nonce, ad, pt⟩, h⟩

def decQuery (nonce : Block) (ad ct : List Block) (tag : Block)
    (h : ValidNonce nonce) : game.Query :=
  ⟨Sum.inr ⟨nonce, ad, ct, tag⟩, h⟩

/-- Given the answers so far, the next query. `none` stops.
`p` is the public permutation; `p.symm` inverts it. -/
def strategy (_p : game.Param) : PFunDDS.DDE game.Query game.Response :=
  fun _ => none

/-- Read the transcript and guess: `true` means "real". -/
def verdict : List (game.Query × Option game.Response) → Bool :=
  fun _ => false

/-- `Attack.Wins` unfolds to

    ∀ p, (advNum : Real) / advDen ≤ advantage budget p

the signed gap between the ideal and real worlds. There is no library theorem
for this challenge — proving this *is* the challenge. -/
def solution : Challenge.SpoC128DS.Solution budget advNum advDen where
  strategy := strategy
  verdict := verdict
  advNum_pos := by decide
  advDen_pos := by decide
  wins := by
    intro p
    sorry

end Solution.SpoC128DS
