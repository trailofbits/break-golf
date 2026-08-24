import Challenges.SpoC128DS.Challenge

namespace Solution.SpoC128DS

open RandomSystems
open RandomSystems.CR18
open RandomSystems.SpoC
open Golf.Instances.SpoC128DS

def budget : Nat := 2
def advNum : Nat := 1
def advDen : Nat := 1

/-- A query carries a proof its nonce is legal: `n &&& 0xF0 = 0`. Build one with
`⟨q, by decide⟩`; an illegal nonce simply will not typecheck. -/
def encQuery (nonce : Block) (ad pt : List Block) (h : ValidNonce nonce) : game.Query :=
  ⟨Sum.inl ⟨nonce, ad, pt⟩, h⟩

def decQuery (nonce : Block) (ad ct : List Block) (tag : Block)
    (h : ValidNonce nonce) : game.Query :=
  ⟨Sum.inr ⟨nonce, ad, ct, tag⟩, h⟩

def strategy (p : game.Param) : PFunDDS.DDE game.Query game.Response
  | [] => some (encQuery 0 [] [] (by decide))
  | [some (Sum.inl r0)] =>
      -- r0.tag is the capacity of π(K ‖ ctrl_T). The rate half is what the
      -- spoc128 attack read from a ciphertext under nonce ctrl_T — and ctrl_T
      -- is not a legal nonce here, so that route is closed.
      some (decQuery 0 [] r0.ciphertext r0.tag (by decide))
  | _ => none

def verdict : List (game.Query × Option game.Response) → Bool
  | t => match t.getLast? with
         | some (_, some (Sum.inr r)) => r.verified
         | _ => false

/-- The open part. `Attack.Wins` unfolds to

    ∀ p, (advNum : Real) / advDen ≤ advantage budget p

where `advantage` is the signed gap between the ideal and real worlds. There is
no library theorem for this challenge — proving it *is* the challenge. -/
def solution : Challenge.SpoC128DS.Solution budget advNum advDen where
  strategy := strategy
  verdict := verdict
  advNum_pos := by decide
  advDen_pos := by decide
  wins := by
    intro p
    sorry

end Solution.SpoC128DS
