/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Golf.Game
import RandomSystems.SpoC.Distinguishing

/-!
# SpoC-128-Pad: the empty message, padded

## The hole this is trying to fix

In SpoC-128 the empty query is the whole bug. With no associated data and no
message, nothing is absorbed and nothing is squeezed, so `tagInput` is applied to
the **raw** loaded state `(K, N)` and the tag hands out
`capacity (π (K ‖ N ⊕ tagControl))` with no permutation in between.

## The mitigation

Pad the empty message to a single zero block. Every message then passes through
at least one permutation call before finalisation, so `tagInput` is never applied
to `(K, N)` again — and the published three-query key recovery is dead.

Decryption mirrors it by substituting a zero **plaintext** block, not a zero
ciphertext block. That asymmetry is forced: padding the ciphertext would decrypt
to `rate (π s)` rather than `0` and break round-tripping.
-/

namespace Golf.Instances.SpoC128Pad

open RandomSystems
open RandomSystems.CR18
open RandomSystems.SpoC
open scoped RandomSystems.CR18.PFunDDS

/-- The mitigation: an empty message is processed as one zero block. -/
def padded (message : List Block) : List Block :=
  if message = [] then [0] else message

/-- Encryption with the padding. The ciphertext returned is the one for the
*original* message, so an empty message still returns an empty ciphertext. -/
def encryptPad (permutation : State → State) (key nonce : Block)
    (ad plaintext : List Block) : EncryptResponse :=
  let s := absorbBlocks permutation (load key nonce) ad
  let result := cryptBlocks permutation false s (padded plaintext)
  ⟨if plaintext = [] then [] else result.2,
    capacity (permutation (tagInput result.1))⟩

/-- Decryption with the padding. An empty ciphertext advances the state as if the
plaintext were a zero block — the encryption-side update at `0`. -/
def decryptPad (permutation : State → State) (key nonce : Block)
    (ad ciphertext : List Block) (tag : Block) : DecryptResponse :=
  let s := absorbBlocks permutation (load key nonce) ad
  let result :=
    if ciphertext = [] then ((cryptBlocks permutation false s [0]).1, [])
    else cryptBlocks permutation true s ciphertext
  if capacity (permutation (tagInput result.1)) = tag then ⟨true, result.2⟩
  else ⟨false, []⟩

/-! ## The game -/

def oraclePad (permutation : State → State) (key : Block) : Query → Response
  | Sum.inl q => Sum.inl (encryptPad permutation key q.nonce q.associatedData q.plaintext)
  | Sum.inr q => Sum.inr (decryptPad permutation key q.nonce q.associatedData q.ciphertext q.tag)

noncomputable def realRepresentative (permutation : Equiv.Perm State) (key : Block) :
    PFunDDS.DDS Query Response :=
  PFunDDS.functionEvaluator (oraclePad permutation key)

noncomputable def realSystem (permutation : Equiv.Perm State) :
    PFunPDS.Prob Query Response :=
  ⟨Dist.fTransform (realRepresentative permutation) (Dist.uniform Block),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- The ideal decryption oracle accepts only an exact replay of an earlier
encryption query. -/
def idealDecryptPad (permutation : Equiv.Perm State) (key : Block) :
    List Query → DecryptQuery → DecryptResponse
  | [], _ => ⟨false, []⟩
  | Sum.inl encryption :: history, decryption =>
      let response := encryptPad permutation key encryption.nonce
        encryption.associatedData encryption.plaintext
      if encryption.nonce = decryption.nonce ∧
          encryption.associatedData = decryption.associatedData ∧
          response.ciphertext = decryption.ciphertext ∧
          response.tag = decryption.tag then
        ⟨true, encryption.plaintext⟩
      else
        idealDecryptPad permutation key history decryption
  | Sum.inr _ :: history, decryption =>
      idealDecryptPad permutation key history decryption

def idealOraclePad (permutation : Equiv.Perm State) (key : Block)
    (history : List Query) (nonempty : history ≠ []) : Response :=
  match history.getLast nonempty with
  | Sum.inl q =>
      Sum.inl (encryptPad permutation key q.nonce q.associatedData q.plaintext)
  | Sum.inr q =>
      Sum.inr (idealDecryptPad permutation key history.dropLast q)

noncomputable def idealRepresentative (permutation : Equiv.Perm State) (key : Block) :
    PFunDDS.DDS Query Response :=
  PFunDDS.historyEvaluator (idealOraclePad permutation key)

noncomputable def idealSystem (permutation : Equiv.Perm State) :
    PFunPDS.Prob Query Response :=
  ⟨Dist.fTransform (idealRepresentative permutation) (Dist.uniform Block),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- SpoC-128 with the empty message padded to a single zero block. -/
@[reducible] noncomputable def game : Golf.Game where
  Param := Equiv.Perm State
  Query := RandomSystems.SpoC.Query
  Response := RandomSystems.SpoC.Response
  real := realSystem
  ideal := idealSystem



end Golf.Instances.SpoC128Pad
