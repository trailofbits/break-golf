/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Golf.Instances.SpoC128.Interface

/-!
# SpoC-128-DS: the same mode with the nonce domain-separated from the controls

## What the existing break eats

`load key n` puts the nonce in the **rate**, and `tagInput` XORs `tagControl`
into that **same rate**.  So

```
tagInput (load key n) = load key (n ^^^ tagControl)
```

and one permutation input is reachable by two different queries: as the
tag-generation call on the empty message under nonce `n`, and as the first
squeeze under nonce `n ^^^ tagControl`.  Since the permutation is public and
invertible, an adversary reads one half of `π (key ‖ tagControl)` out of a tag
and the other half out of a ciphertext block, joins them, inverts, and takes the
capacity — which is the key.  That is
`RandomSystems.SpoC.attack_distinguishing_advantage`, in one sentence.

## What this variant changes

Nothing in the mode.  The four control bits are **reserved in the nonce**, which
is how a specification actually states domain separation: *the nonce is 124 bits
and the low nibble-pair is reserved*.  `n ^^^ tagControl` is then not a nonce an
adversary may send, and the collision above is unreachable.

This is deliberately not a rewrite of `DDC.lean`.  A second copy of the mode
would be a parallel model to keep in sync; a restriction of the query domain is
one predicate, and it leaves every existing theorem about the mode applicable.

## The receipt

The restriction is carried in the **type** of a query, so the existing attack is
not merely unsuccessful here — `SpoC128.parAttack` is a
`DDE SpoC.Query SpoC.Response` and this game's queries are a different type, so
it cannot be presented as an adversary at all.  `attack_second_query_illegal`
records why: the nonce it needs is exactly the one the variant reserves.

## What is NOT claimed

That this variant is secure.  Nobody has looked.  Closing the one published
route into a mode is not an argument that no other route exists, and the point
of putting it on a board is to find out.
-/

namespace Golf.Instances.SpoC128DS

open RandomSystems
open RandomSystems.CR18
open RandomSystems.SpoC

/-! ## The reserved bits -/

/-- The four mode-control bits: tag `0x80`, plaintext `0x40`, associated data
`0x20`, partial block `0x10`. -/
def controlMask : Block := 0xF0

/-- A nonce is legal when it touches none of the control bits. -/
def ValidNonce (n : Block) : Prop := n &&& controlMask = 0

instance : DecidablePred ValidNonce := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The nonce of either kind of query. -/
def queryNonce : RandomSystems.SpoC.Query → Block
  | Sum.inl q => q.nonce
  | Sum.inr q => q.nonce

/-- A query is legal when its nonce is. -/
def ValidQuery (q : RandomSystems.SpoC.Query) : Prop := ValidNonce (queryNonce q)

instance : DecidablePred ValidQuery := fun _ => inferInstanceAs (Decidable (ValidNonce _))

/-- The variant's query type.  Domain separation lives here, in the type, so an
adversary for the unrestricted game is not an adversary for this one. -/
abbrev Query := {q : RandomSystems.SpoC.Query // ValidQuery q}

/-- Responses are unchanged. -/
abbrev Response := RandomSystems.SpoC.Response

/-! ## Receipts on the restriction -/

/-- The variant is not vacuous: the all-zero nonce is legal. -/
theorem zero_valid : ValidNonce 0 := by decide

/-- Every control word is illegal as a nonce. -/
theorem tagControl_not_valid : ¬ ValidNonce tagControl := by decide

theorem fullPTControl_not_valid : ¬ ValidNonce fullPTControl := by decide

theorem fullADControl_not_valid : ¬ ValidNonce fullADControl := by decide

/-- **Why the published attack does not reach this game.**  Its second query is
`oneBlockEncryptionQuery`, whose nonce is exactly `tagControl` — the value the
variant reserves.  The collision `tagInput (load key n) = load key (n ^^^ tagControl)`
is therefore not addressable from the legal nonce space. -/
theorem attack_second_query_illegal :
    ¬ ValidQuery (Sum.inl RandomSystems.SpoC.oneBlockEncryptionQuery) :=
  tagControl_not_valid

/-! ## The game -/

noncomputable def realRepresentative (permutation : Equiv.Perm State) (key : Block) :
    PFunDDS.DDS Query Response :=
  PFunDDS.functionEvaluator (fun q : Query => spocOracle permutation key q.val)

noncomputable def realSystem (permutation : Equiv.Perm State) :
    PFunPDS.Prob Query Response :=
  ⟨Dist.fTransform (realRepresentative permutation) (Dist.uniform Block),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

noncomputable def idealRepresentative (permutation : Equiv.Perm State) (key : Block) :
    PFunDDS.DDS Query Response :=
  PFunDDS.historyEvaluator (fun (h : List Query) (ne : h ≠ []) =>
    RandomSystems.SpoC.idealOracle permutation key (h.map Subtype.val)
      (by simpa using ne))

noncomputable def idealSystem (permutation : Equiv.Perm State) :
    PFunPDS.Prob Query Response :=
  ⟨Dist.fTransform (idealRepresentative permutation) (Dist.uniform Block),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- SpoC-128 with the nonce domain-separated from the mode controls. -/
@[reducible] noncomputable def game : Golf.Game where
  Param := Equiv.Perm State
  Query := Query
  Response := Response
  real := realSystem
  ideal := idealSystem

end Golf.Instances.SpoC128DS
