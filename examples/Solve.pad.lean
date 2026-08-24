/-
The reference solve for `spoc128-pad`, written from scratch.

The mitigation pads an empty message to a single zero block, which does close the
published three-query key recovery — `tagInput` is never applied to the raw
`(K, N)` again. But the padding is not injective: `[]` and `[0]` are processed
identically, so they carry the same tag and only the ciphertext differs.

Two queries, advantage one. Nothing from any library attack is used.
-/
import Challenges.SpoC128Pad.Challenge

namespace Solution.SpoC128Pad

open RandomSystems
open RandomSystems.CR18
open RandomSystems.SpoC
open scoped RandomSystems.CR18.PFunDDS
open Golf.Instances.SpoC128Pad

def budget : Nat := 2
def advNum : Nat := 1
def advDen : Nat := 1


/-- Query one: a single zero block. Its ciphertext is one block long. -/
def probe : Query := Sum.inl ⟨0, [], [0]⟩

/-- Query two: the same tag, but an *empty* ciphertext. The padding makes the
real oracle recompute exactly the same state, so it verifies; the ideal has no
matching replay because the ciphertexts differ. -/
def forge (r : EncryptResponse) : Query := Sum.inr ⟨0, [], [], r.tag⟩

def env : PFunDDS.DDE Query Response
  | [] => some probe
  | [some (Sum.inl r)] => some (forge r)
  | _ => none

def verdict (t : List (Query × Option Response)) : Bool :=
  match t.getLast? with
  | some (_, some (Sum.inr r)) => r.verified
  | _ => false

/-- The real oracle accepts the forgery: padding makes the empty ciphertext
recompute the probe's state. -/
theorem real_accepts (p : Equiv.Perm State) (k : Block) :
    decryptPad (⇑p) k 0 [] [] (encryptPad (⇑p) k 0 [] [0]).tag = ⟨true, []⟩ := by
  simp [decryptPad, encryptPad, padded]

/-- The probe's ciphertext is one block long, so it is not the empty ciphertext
the forgery submits — which is why the ideal has no replay to match. -/
theorem probe_ciphertext_ne (p : Equiv.Perm State) (k : Block) :
    (encryptPad (⇑p) k 0 [] [0]).ciphertext ≠ [] := by
  simp [encryptPad, padded, cryptBlocks]

/-- The ideal oracle rejects it: the only earlier encryption carries a one-block
ciphertext, so the empty-ciphertext forgery matches no replay. -/
theorem ideal_rejects (p : Equiv.Perm State) (k : Block) :
    idealDecryptPad p k [probe] ⟨0, [], [], (encryptPad (⇑p) k 0 [] [0]).tag⟩
      = ⟨false, []⟩ := by
  simp only [idealDecryptPad, probe]
  rw [if_neg]
  rintro ⟨-, -, hc, -⟩
  exact probe_ciphertext_ne p k hc

noncomputable def distinguisher (p : Equiv.Perm State) : PFunDDS.DDD Query Response :=
  PFunDDS.DDD.ofDDE env 2 verdict

noncomputable def law (p : Equiv.Perm State) :
    RandomSystems.Dist (PFunDDS.DDD Query Response) :=
  Finsupp.single (distinguisher p) 1

theorem real_transcript (p : Equiv.Perm State) (k : Block) :
    PFunDDS.transcript (Golf.Instances.SpoC128Pad.realRepresentative p k) env 2 =
      [(probe, some (Sum.inl (encryptPad (⇑p) k 0 [] [0]))),
       (forge (encryptPad (⇑p) k 0 [] [0]), some (Sum.inr ⟨true, []⟩))] := by
  have answer (history : List Query) (query : Query) :
      PFunDDS.output (Golf.Instances.SpoC128Pad.realRepresentative p k)⊥ (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
        some (oraclePad (⇑p) k query) := by
    have hh : history ∈ PFunDDS.dom (Golf.Instances.SpoC128Pad.realRepresentative p k) ∨ history = [] := by
      by_cases he : history = []
      · exact Or.inr he
      · left
        change history ∈ PFunDDS.dom (PFunDDS.functionEvaluator (oraclePad (⇑p) k))
        rw [PFunDDS.dom_functionEvaluator]; exact he
    have hn : history ++ [query] ∈ PFunDDS.dom (Golf.Instances.SpoC128Pad.realRepresentative p k) := by
      change history ++ [query] ∈ PFunDDS.dom (PFunDDS.functionEvaluator (oraclePad (⇑p) k))
      rw [PFunDDS.dom_functionEvaluator]; simp
    rw [PFunDDS.output_fullyDefined_append_of_mem (Golf.Instances.SpoC128Pad.realRepresentative p k) history query hh hn]
    change some (PFunDDS.output (PFunDDS.functionEvaluator (oraclePad (⇑p) k)) (history ++ [query]) _) = _
    rw [PFunDDS.functionEvaluator_output]
  have hfire0 : env (PFunDDS.transcriptOutputs
      (PFunDDS.transcript (Golf.Instances.SpoC128Pad.realRepresentative p k) env 0)) = some probe := rfl
  have htr1 : PFunDDS.transcript (Golf.Instances.SpoC128Pad.realRepresentative p k) env 1
      = [(probe, some (Sum.inl (encryptPad (⇑p) k 0 [] [0])))] := by
    rw [show 1 = 0 + 1 by omega, transcript_succ_fire hfire0]
    simp only [PFunDDS.transcript, PFunDDS.transcriptInputs, List.map_nil, List.nil_append]
    have h := answer [] probe
    simp only [List.nil_append] at h
    rw [h]
    rfl
  have hfire1 : env (PFunDDS.transcriptOutputs
      (PFunDDS.transcript (Golf.Instances.SpoC128Pad.realRepresentative p k) env 1))
      = some (forge (encryptPad (⇑p) k 0 [] [0])) := by
    rw [htr1]; rfl
  rw [show 2 = 1 + 1 by omega, transcript_succ_fire hfire1, htr1]
  simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
  rw [answer [probe] (forge (encryptPad (⇑p) k 0 [] [0]))]
  simp only [oraclePad, forge]
  rw [real_accepts p k]
  rfl

theorem ideal_transcript (p : Equiv.Perm State) (k : Block) :
    PFunDDS.transcript (Golf.Instances.SpoC128Pad.idealRepresentative p k) env 2 =
      [(probe, some (Sum.inl (encryptPad (⇑p) k 0 [] [0]))),
       (forge (encryptPad (⇑p) k 0 [] [0]), some (Sum.inr ⟨false, []⟩))] := by
  have answer (history : List Query) (query : Query) :
      PFunDDS.output (Golf.Instances.SpoC128Pad.idealRepresentative p k)⊥ (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
        some (idealOraclePad p k (history ++ [query]) (by simp)) := by
    have hh : history ∈ PFunDDS.dom (Golf.Instances.SpoC128Pad.idealRepresentative p k) ∨ history = [] := by
      by_cases he : history = []
      · exact Or.inr he
      · left
        change history ∈ PFunDDS.dom (PFunDDS.historyEvaluator (idealOraclePad p k))
        rw [PFunDDS.dom_historyEvaluator]; exact he
    have hn : history ++ [query] ∈ PFunDDS.dom (Golf.Instances.SpoC128Pad.idealRepresentative p k) := by
      change history ++ [query] ∈ PFunDDS.dom (PFunDDS.historyEvaluator (idealOraclePad p k))
      rw [PFunDDS.dom_historyEvaluator]; simp
    rw [PFunDDS.output_fullyDefined_append_of_mem (Golf.Instances.SpoC128Pad.idealRepresentative p k) history query hh hn]
    change some (PFunDDS.output (PFunDDS.historyEvaluator (idealOraclePad p k)) (history ++ [query]) _) = _
    rw [PFunDDS.historyEvaluator_output]
  have hfire0 : env (PFunDDS.transcriptOutputs
      (PFunDDS.transcript (Golf.Instances.SpoC128Pad.idealRepresentative p k) env 0)) = some probe := rfl
  have htr1 : PFunDDS.transcript (Golf.Instances.SpoC128Pad.idealRepresentative p k) env 1
      = [(probe, some (Sum.inl (encryptPad (⇑p) k 0 [] [0])))] := by
    rw [show 1 = 0 + 1 by omega, transcript_succ_fire hfire0]
    simp only [PFunDDS.transcript, PFunDDS.transcriptInputs, List.map_nil, List.nil_append]
    have h := answer [] probe
    simp only [List.nil_append] at h
    rw [h]
    rfl
  have hfire1 : env (PFunDDS.transcriptOutputs
      (PFunDDS.transcript (Golf.Instances.SpoC128Pad.idealRepresentative p k) env 1))
      = some (forge (encryptPad (⇑p) k 0 [] [0])) := by
    rw [htr1]; rfl
  rw [show 2 = 1 + 1 by omega, transcript_succ_fire hfire1, htr1]
  simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
  rw [answer [probe] (forge (encryptPad (⇑p) k 0 [] [0]))]
  simp [idealOraclePad, forge]
  exact ideal_rejects p k

/-- **The break.** Two queries, advantage exactly one, for every key and every
permutation. The padding that closed SpoC-128's empty-message hole made the
empty message and a single zero block indistinguishable to the tag. -/
theorem advantage_eq_one (p : Equiv.Perm State) :
    _root_.RandomSystems.CR18.advantage (law p) (Golf.Instances.SpoC128Pad.idealSystem p).val (Golf.Instances.SpoC128Pad.realSystem p).val = 1 := by
  have realVerdict (k : Block) :
      PFunDDS.verdict (distinguisher p) (Golf.Instances.SpoC128Pad.realRepresentative p k) := by
    change PFunDDS.verdict (PFunDDS.DDD.ofDDE env 2 verdict) (Golf.Instances.SpoC128Pad.realRepresentative p k)
    rw [verdict_ofDDE_iff, real_transcript p k]
    simp [verdict]
  have idealNoVerdict (k : Block) :
      ¬ PFunDDS.verdict (distinguisher p) (Golf.Instances.SpoC128Pad.idealRepresentative p k) := by
    change ¬ PFunDDS.verdict (PFunDDS.DDD.ofDDE env 2 verdict) (Golf.Instances.SpoC128Pad.idealRepresentative p k)
    rw [verdict_ofDDE_iff, ideal_transcript p k]
    simp [verdict]
  unfold _root_.RandomSystems.CR18.advantage law
  rw [verdictProb_single, verdictProb_single]
  unfold Golf.Instances.SpoC128Pad.idealSystem Golf.Instances.SpoC128Pad.realSystem
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  have hreal : (Dist.uniform Block).mass
      (fun k => PFunDDS.verdict (distinguisher p) (Golf.Instances.SpoC128Pad.realRepresentative p k)) = 1 := by
    calc
      _ = (Dist.uniform Block).mass (fun _ => True) :=
        Dist.mass_congr _ fun k => iff_of_true (realVerdict k) trivial
      _ = (Dist.uniform Block).weight := Dist.mass_true _
      _ = 1 := Dist.uniform_isProbDist.weight_eq
  have hideal : (Dist.uniform Block).mass
      (fun k => PFunDDS.verdict (distinguisher p) (Golf.Instances.SpoC128Pad.idealRepresentative p k)) = 0 :=
    Dist.mass_eq_zero_of_forall_not _ idealNoVerdict
  rw [hreal, hideal]
  norm_num


def strategy : game.Param → PFunDDS.DDE game.Query game.Response := fun _ => env

def solution : Challenge.SpoC128Pad.Solution budget advNum advDen where
  strategy := strategy
  verdict := verdict
  advNum_pos := by decide
  advDen_pos := by decide
  wins := by
    intro p
    have h : ((advNum : Real) / (advDen : Real)) = 1 := by norm_num [advNum, advDen]
    rw [h]
    exact le_of_eq (advantage_eq_one p).symm

end Solution.SpoC128Pad
