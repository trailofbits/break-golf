/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Distinguishing
import RandomSystems.RandomSystem

/-!
# The golf board: the outer interfaces

This file is the *trusted boundary* between the repository and an agent that
submits an attack.  It owns three things and nothing else:

* `Game` — what a challenge author must supply to put a new target on the board;
* `Attack` — the normal form every submission is required to take;
* `Submission` — the win condition, tied to the number that appears on the
  leaderboard.

Everything here is an abstraction of the one game the repository actually has,
`RandomSystems/SpoC/`.  Read that directory as the worked instance: `spocPDS`
and `idealSystem` are a `Game`, `attackEnvironment`/`verificationVerdict` are an
`Attack` at budget `3`, and `attack_distinguishing_advantage` is `Wins` at
bound `1`.  Nothing in this file is a new modelling primitive: `DDE`, `DDD`,
`DDD.ofDDE` and `advantage` are all CR18 carriers that already exist.

## The query count is not part of the attack

An `Attack` is a strategy and a verdict, with no budget of its own.  The budget
is a parameter of *evaluation*: `a.advantage q p` is what the attack achieves
when it is allowed `q` queries.  Three things follow, and they are the reason
the interface is shaped this way.

* An agent never has to guess a budget in advance.  Guessing low used to be a
  hard failure with no partial credit; now the same strategy is simply scored at
  whichever `q` it can carry.
* Improvement is expressible on one object.  A brute-force adversary at `q = 2^n`
  and a sharp one at `q = 3` are the *same kind* of submission at different
  points, so a board can watch one become the other.
* The natural object of cryptanalysis is a curve, not a point.  `Attack.Achieves`
  states a whole advantage function `bound : ℕ → ℝ`; `Attack.Wins` is its value
  at one `q`, which is what a leaderboard row displays.

## Why the score cannot be overclaimed

The query count is a *constructor argument* of `DDD.ofDDE`, not a claim about a
finished object.  `Attack.silent_past` discharges the consequence: past `q`
observations the denoted distinguisher is silent, no matter what `strategy`
does.  So there is no separate cost theorem to fake — the number on the board is
the number the adversary was built from.
-/

namespace RandomSystems.CR18
namespace Golf

open RandomSystems (Dist)
open PFunDDS

universe u v w

/-! ## What a challenge author supplies -/

/-- A distinguishing game: the two worlds an adversary must tell apart.

`Param` is the *public* data the adversary is also given — SpoC's public
permutation is the motivating case.  Quantifying the win over `Param` is what
stops a submission from choosing a convenient instance for itself. -/
structure Game where
  /-- Public parameters, known to the adversary. -/
  Param : Type u
  /-- The queries the adversary may issue. -/
  Query : Type v
  /-- The answers the game returns. -/
  Response : Type w
  /-- The real world. -/
  real : Param → PFunPDS.Prob Query Response
  /-- The idealized world the real one is supposed to be indistinguishable from. -/
  ideal : Param → PFunPDS.Prob Query Response

variable {G : Game.{u, v, w}}

/-! ## What an agent submits -/

/-- A submitted attack, in normal form.

This is the entire shape of `Solve.lean`: a strategy and a verdict, and nothing
else.  There is deliberately no budget field — see the header.  A single attack
is scored at whatever query counts it can carry. -/
structure Attack (G : Game.{u, v, w}) where
  /-- The adaptive query strategy: what to ask next, given the answers so far. -/
  strategy : G.Param → PFunDDS.DDE G.Query G.Response
  /-- The verdict: accept or reject, read off the observed transcript. -/
  verdict : List (G.Query × Option G.Response) → Bool

/-- The distinguisher an attack denotes when allowed `q` queries: replay
`strategy` for at most `q` queries, then rule by `verdict`.  This is CR18's
§4.10.1 accept-set normal form, unchanged. -/
noncomputable def Attack.distinguisher (a : Attack G) (q : ℕ) (p : G.Param) :
    PFunDDS.DDD G.Query G.Response :=
  PFunDDS.DDD.ofDDE (a.strategy p) q a.verdict

/-- The point-mass law of a deterministic attack.  Submissions are deterministic
by construction: randomness belongs in the game, not in the adversary. -/
noncomputable def Attack.law (a : Attack G) (q : ℕ) (p : G.Param) :
    Dist (PFunDDS.DDD G.Query G.Response) :=
  Finsupp.single (a.distinguisher q p) 1

/-- The attack's signed advantage on `q` queries at a public parameter,
`Pr[real] - Pr[ideal]`.

Argument order matches `RandomSystems.SpoC.distinguishingAdvantage`: `advantage`
is `verdictProb D T - verdictProb D S`, so the ideal world goes in the `S` slot.

Nothing here forces this to be monotone in `q`.  A strategy that stops early is
unaffected by raising the budget, and a badly chosen `verdict` can genuinely do
worse with more data; the curve reports whatever is true. -/
noncomputable def Attack.advantage (a : Attack G) (q : ℕ) (p : G.Param) : ℝ :=
  _root_.RandomSystems.CR18.advantage (a.law q p) (G.ideal p).val (G.real p).val

/-- **The win condition at one query count** — a leaderboard row.  The bound must
hold at *every* public parameter, which is what stops a submission from choosing
a convenient instance for itself. -/
def Attack.Wins (a : Attack G) (q : ℕ) (bound : ℝ) : Prop :=
  ∀ p : G.Param, bound ≤ a.advantage q p

/-- **The win condition as a curve.**  The honest statement of a cryptanalytic
result: an advantage function of the query count, holding at every parameter.
`fun _ => 0` is the floor, not a free pass — the signed advantage of a useless
adversary is exactly `0`, so a curve only scores where it is positive. -/
def Attack.Achieves (a : Attack G) (bound : ℕ → ℝ) : Prop :=
  ∀ (q : ℕ) (p : G.Param), bound q ≤ a.advantage q p

/-- A curve is exactly its rows: every point of an achieved curve is a win. -/
theorem Attack.Achieves.wins {a : Attack G} {bound : ℕ → ℝ}
    (h : a.Achieves bound) (q : ℕ) : a.Wins q (bound q) :=
  fun p => h q p

/-- Conversely, winning at every `q` is achieving the curve. -/
theorem Attack.achieves_of_wins {a : Attack G} {bound : ℕ → ℝ}
    (h : ∀ q, a.Wins q (bound q)) : a.Achieves bound :=
  fun q p => h q p

/-- `q` is *the* query complexity of reaching advantage `α`: the attack gets
there on `q` queries and on nothing smaller.  Stated as a predicate rather than
a `sInf` so an unreachable `α` has no junk value. -/
def Attack.IsQueryComplexity (a : Attack G) (α : ℝ) (q : ℕ) : Prop :=
  a.Wins q α ∧ ∀ q' < q, ¬ a.Wins q' α

/-- **Structural budget enforcement.**  Past `q` observations the denoted
distinguisher issues no further query, whatever `strategy` does.  Immediate from
`ddToDDE_ofDDE`; this is the reason a submission cannot spend more queries than
it is scored for. -/
theorem Attack.silent_past (a : Attack G) (q : ℕ) (p : G.Param)
    (ys : List (Option G.Response)) (h : q ≤ ys.length) :
    PFunDDS.ddToDDE (a.distinguisher q p) ys = none := by
  rw [Attack.distinguisher, ddToDDE_ofDDE]
  exact if_neg (Nat.not_lt.mpr h)

/-! ## Stopping attacks state their curve for free

Most attacks stop: after `k` queries the strategy has what it needs and issues no
more.  For those, the advantage is *constant* above `k`, so a single won row
extends to the whole upper half of the curve with no further work.  This is what
makes curve-scored challenges practical — an agent proves one point and gets the
tail. -/

/-- An environment **stalls at `k`** when, on every observation history of length
at least `k`, its replayed transcript issues no further query. -/
def Stalls {X : Type u} {Y : Type v} (e : PFunDDS.DDE X Y) (k : ℕ) : Prop :=
  ∀ ys : List (Option Y), k ≤ ys.length →
    e (PFunDDS.transcriptOutputs (replay e ys)) = none

/-- A stalled environment's replay is determined by the first `k` answers. -/
theorem replay_take_of_stalls {X : Type u} {Y : Type v}
    {e : PFunDDS.DDE X Y} {k : ℕ} (hs : Stalls e k)
    {ys : List (Option Y)} (h : k ≤ ys.length) :
    replay e ys = replay e (ys.take k) := by
  have hlen : k ≤ (ys.take k).length := by
    rw [List.length_take]; omega
  exact replay_eq_of_stall (hs _ hlen) (List.take_prefix k ys)

/-- One more answer extends the replay by the environment's next move, or by
nothing at all once it has gone quiet. -/
theorem replay_append_one {X : Type u} {Y : Type v}
    (e : PFunDDS.DDE X Y) (ys : List (Option Y)) (y : Option Y) :
    replay e (ys ++ [y]) =
      match e (PFunDDS.transcriptOutputs (replay e ys)) with
      | some x => replay e ys ++ [(x, y)]
      | none => replay e ys := by
  unfold replay
  rw [List.foldl_append]
  rfl

/-- A replay either consumed every answer it was given, or it is already
stalled.  There is no third case, which is what makes the syntactic stopping
criterion below sufficient. -/
theorem replay_full_or_stalled {X : Type u} {Y : Type v}
    (e : PFunDDS.DDE X Y) (ys : List (Option Y)) :
    (replay e ys).length = ys.length ∨
      e (PFunDDS.transcriptOutputs (replay e ys)) = none := by
  induction ys using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton ys y ih =>
      rcases ih with hlen | hnone
      · rcases hm : e (PFunDDS.transcriptOutputs (replay e ys)) with _ | x
        · right
          rw [replay_append_one, hm, hm]
        · left
          rw [replay_append_one, hm]
          simp [hlen]
      · right
        rw [replay_append_one, hnone, hnone]

/-- **The criterion an agent actually discharges.**  It is enough that the
strategy is silent on every *raw* history of length at least `k` — no reasoning
about replays required.  This is a finite pattern-match for any strategy written
by cases on the answers so far. -/
theorem stalls_of_silent_above {X : Type u} {Y : Type v}
    {e : PFunDDS.DDE X Y} {k : ℕ}
    (h : ∀ ys : List (Option Y), k ≤ ys.length → e ys = none) : Stalls e k := by
  intro ys hys
  rcases replay_full_or_stalled e ys with hlen | hnone
  · exact h _ (by
      rw [PFunDDS.transcriptOutputs, List.length_map, hlen]; exact hys)
  · exact hnone

/-- **Raising the budget of a stalled environment changes nothing.**  The two
accept-set distinguishers are equal, not merely equal in verdict probability. -/
theorem ofDDE_eq_of_stalls {X : Type u} {Y : Type v}
    {e : PFunDDS.DDE X Y} {k q : ℕ} (hs : Stalls e k) (hkq : k ≤ q)
    (A : List (X × Option Y) → Bool) :
    PFunDDS.DDD.ofDDE e q A = PFunDDS.DDD.ofDDE e k A := by
  apply Subtype.ext
  funext ys
  show (if ys.length < q then _ else _) = (if ys.length < k then _ else _)
  by_cases hk : ys.length < k
  · rw [if_pos hk, if_pos (lt_of_lt_of_le hk hkq)]
  · have hkle : k ≤ ys.length := Nat.not_lt.mp hk
    rw [if_neg hk]
    by_cases hq : ys.length < q
    · rw [if_pos hq, hs ys hkle, replay_take_of_stalls hs hkle]
    · rw [if_neg hq]
      have hqle : q ≤ ys.length := Nat.not_lt.mp hq
      have hre : replay e (ys.take q) = replay e (ys.take k) := by
        have h1 : k ≤ (ys.take q).length := by
          rw [List.length_take]; omega
        rw [replay_take_of_stalls hs h1, List.take_take, Nat.min_eq_left hkq]
      rw [hre]

/-- An attack **stops at `k`** when its strategy stalls there at every public
parameter. -/
def Attack.StopsAt (a : Attack G) (k : ℕ) : Prop :=
  ∀ p : G.Param, Stalls (a.strategy p) k

theorem Attack.distinguisher_eq_of_stops {a : Attack G} {k q : ℕ}
    (hs : a.StopsAt k) (hkq : k ≤ q) (p : G.Param) :
    a.distinguisher q p = a.distinguisher k p :=
  ofDDE_eq_of_stalls (hs p) hkq a.verdict

/-- A stopping attack's advantage is constant above its stopping point. -/
theorem Attack.advantage_eq_of_stops {a : Attack G} {k q : ℕ}
    (hs : a.StopsAt k) (hkq : k ≤ q) (p : G.Param) :
    a.advantage q p = a.advantage k p := by
  unfold Attack.advantage Attack.law
  rw [Attack.distinguisher_eq_of_stops hs hkq]

/-- **The row extends.**  Winning at a stopping attack's own budget wins at every
larger one, so an agent never has to re-prove a result to report it at a coarser
query count. -/
theorem Attack.wins_mono_of_stops {a : Attack G} {k q : ℕ} {β : ℝ}
    (hs : a.StopsAt k) (hkq : k ≤ q) (hw : a.Wins k β) : a.Wins q β := by
  intro p
  rw [Attack.advantage_eq_of_stops hs hkq]
  exact hw p

/-- A point-mass winner that never wins has winning probability zero. -/
theorem winProb_single_eq_zero_of_never {W : Type u} {Gm : Type v}
    {win : W → Gm → Prop} (d : W) (Gd : Dist Gm) (h : ∀ g, ¬ win d g) :
    GamePerf.winProb win (Finsupp.single d 1) Gd = 0 := by
  unfold GamePerf.winProb
  rw [Finsupp.sum_single_index (by simp)]
  simp [h]

/-- An attack that never returns the verdict `true` has advantage exactly zero.
This is the honest floor of the board: not a win, but not a loss either. -/
theorem Attack.advantage_eq_zero_of_never_accepts (a : Attack G) (q : ℕ) (p : G.Param)
    (h : ∀ ys, (a.distinguisher q p).val ys ≠ Sum.inr true) :
    a.advantage q p = 0 := by
  have hnever : ∀ s : PFunDDS.DDS G.Query G.Response,
      ¬ PFunDDS.verdict (a.distinguisher q p) s := by
    intro s hs
    obtain ⟨n, hn⟩ := hs
    exact h _ hn
  unfold Attack.advantage _root_.RandomSystems.CR18.advantage
    _root_.RandomSystems.CR18.verdictProb Attack.law
  rw [winProb_single_eq_zero_of_never _ _ hnever,
      winProb_single_eq_zero_of_never _ _ hnever]
  ring

/-- **The criterion for the floor.**  Every verdict the `q`-truncated
distinguisher can ever read is `a.verdict` applied to a replay of at most `q`
answers.  Rejecting all of those is enough. -/
theorem Attack.never_accepts_of_reject (a : Attack G) (q : ℕ) (p : G.Param)
    (h : ∀ zs : List (Option G.Response), zs.length ≤ q →
      a.verdict (replay (a.strategy p) zs) = false) :
    ∀ ys, (a.distinguisher q p).val ys ≠ Sum.inr true := by
  intro ys
  show (if ys.length < q then _ else _) ≠ _
  by_cases hq : ys.length < q
  · rw [if_pos hq]
    rcases hm : a.strategy p (PFunDDS.transcriptOutputs (replay (a.strategy p) ys)) with _ | x
    · simp [h ys (le_of_lt hq)]
    · simp
  · rw [if_neg hq]
    have hlen : (ys.take q).length ≤ q := by rw [List.length_take]; omega
    simp [h _ hlen]

/-- The floor, from a syntactic check on the verdict alone. -/
theorem Attack.wins_zero_of_reject (a : Attack G) (q : ℕ)
    (h : ∀ (p : G.Param) (zs : List (Option G.Response)), zs.length ≤ q →
      a.verdict (replay (a.strategy p) zs) = false) :
    a.Wins q 0 := fun p =>
  le_of_eq (a.advantage_eq_zero_of_never_accepts q p
    (a.never_accepts_of_reject q p (h p))).symm

/-- **The curve, from one point.**  A stopping attack that wins at `k`, and does
no harm below it, achieves the step curve.  `hfloor` is the honest residue: the
signed advantage of a truncated attack is not automatically non-negative, so the
floor has to be shown rather than assumed. -/
theorem Attack.achieves_step_of_stops {a : Attack G} {k : ℕ} {β : ℝ}
    (hs : a.StopsAt k) (hw : a.Wins k β) (hfloor : ∀ q, q < k → a.Wins q 0) :
    a.Achieves (fun q => if k ≤ q then β else 0) := by
  intro q p
  by_cases h : k ≤ q
  · simpa only [if_pos h] using Attack.wins_mono_of_stops hs h hw p
  · simpa only [if_neg h] using hfloor q (Nat.not_le.mp h) p

/-! ## What the leaderboard records -/

/-- A leaderboard entry's two numbers.  The advantage is kept as a rational so
the score is a literal the platform can carry through the submission form. -/
structure Score where
  /-- Queries spent. Lower is better. -/
  budget : ℕ
  /-- Numerator of the claimed advantage. -/
  advNum : ℕ
  /-- Denominator of the claimed advantage. -/
  advDen : ℕ

/-- The claimed advantage as a real number. -/
noncomputable def Score.advantage (s : Score) : ℝ :=
  (s.advNum : ℝ) / (s.advDen : ℝ)

/-- The **work factor**: queries per unit advantage, `q / α^e`.

This is the figure of merit that lets a board rank results on a target *nobody
has studied yet*.  A fixed target advantage cannot be set for a new design —
that is the very thing under research, and a threshold set too high scores a
genuine `2⁻³⁰` distinguisher as zero.  The work factor instead **measures** what
was achieved: `Real.logb 2` of it is the security level, in bits, that the attack
refutes.

`e` is the advantage exponent and there is deliberately **no default**, because
the right value depends on what the game asks.

* `e = 2` for a **decision** game — the shape of `Golf.Game`.  An advantage `α`
  needs about `α⁻²` independent repetitions to amplify to constant confidence,
  not `α⁻¹`, so `q/α²` is the cost of actually deciding.
* `e = 1` for a **search**-flavoured game — key recovery, forgery — where
  success probability `α` needs about `α⁻¹` repetitions.

The two conventions coexist in the literature and their inconsistency is a known
problem (Micciancio–Walter, *On the Bit Security of Cryptographic Primitives*).
Making `e` a visible challenge parameter is the honest response: the board states
which convention it is using rather than picking one silently.

Scoring this way is incentive-compatible.  Understating the advantage *raises*
the work factor, so there is nothing to gain by claiming a weaker bound than one
can prove, and `Wins` refuses a stronger one. -/
noncomputable def Score.workFactor (e : ℕ) (s : Score) : ℝ :=
  (s.budget : ℝ) / s.advantage ^ e

/-- The ranked column: one score beats another when its work factor is smaller.
Unlike `Dominates` this compares *any* two results, which is what lets a board
keep a single ordered leaderboard and a single record progression over a target
whose achievable frontier is unknown. -/
def Score.Beats (e : ℕ) (a b : Score) : Prop :=
  a.workFactor e < b.workFactor e

/-- The two views agree: a result that dominates on both axes never ranks worse
on the work factor.  So the ranked column never contradicts the frontier. -/
theorem Score.workFactor_le_of_dominates {e : ℕ} {a b : Score}
    (hb : 0 < b.advantage) (hq : a.budget ≤ b.budget)
    (hadv : b.advantage ≤ a.advantage) :
    a.workFactor e ≤ b.workFactor e := by
  unfold Score.workFactor
  gcongr

/-- One score beats another when it is no worse on both axes and strictly better
on one.  The board is the Pareto frontier of this order, not a single column:
fewer queries and a larger advantage are both progress, and neither dominates. -/
def Score.Dominates (a b : Score) : Prop :=
  a.budget ≤ b.budget ∧ b.advantage ≤ a.advantage ∧
    (a.budget < b.budget ∨ b.advantage < a.advantage)

/-- Dominating is *strictly* better on the work factor, so the ranked column can
never quietly bury a result that wins on both axes. -/
theorem Score.workFactor_lt_of_dominates {e : ℕ} (he : e ≠ 0) {a b : Score}
    (hbadv : 0 < b.advantage) (hbbud : 0 < b.budget) (h : Score.Dominates a b) :
    a.workFactor e < b.workFactor e := by
  obtain ⟨hq, hadv, hstrict⟩ := h
  have haadv : 0 < a.advantage := lt_of_lt_of_le hbadv hadv
  have hbp : (0:ℝ) < b.advantage ^ e := pow_pos hbadv e
  have hap : (0:ℝ) < a.advantage ^ e := pow_pos haadv e
  have hle : b.advantage ^ e ≤ a.advantage ^ e := by gcongr
  unfold Score.workFactor
  rcases hstrict with hs | hs
  · have hs' : (a.budget : ℝ) < (b.budget : ℝ) := by exact_mod_cast hs
    have h1 : (a.budget : ℝ) / a.advantage ^ e ≤ (a.budget : ℝ) / b.advantage ^ e := by gcongr
    have h2 : (a.budget : ℝ) / b.advantage ^ e < (b.budget : ℝ) / b.advantage ^ e := by gcongr
    linarith
  · have hlt : b.advantage ^ e < a.advantage ^ e := by
      have := Nat.pos_of_ne_zero he
      gcongr
    have hq' : (a.budget : ℝ) ≤ (b.budget : ℝ) := by exact_mod_cast hq
    have hbb : (0:ℝ) < (b.budget : ℝ) := by exact_mod_cast hbbud
    have h1 : (a.budget : ℝ) / a.advantage ^ e ≤ (b.budget : ℝ) / a.advantage ^ e := by gcongr
    have h2 : (b.budget : ℝ) / a.advantage ^ e < (b.budget : ℝ) / b.advantage ^ e := by gcongr
    linarith

/-- **The frontier is the primary object.**  `s` is on the frontier of the
submitted set `S` when nothing in `S` beats it on both axes at once.  A board
should mark a submission a *record* by this test, not by a scalar: the partial
order is what we actually know, and every scalar is a chosen summary of it. -/
def Score.OnFrontier (S : Set Score) (s : Score) : Prop :=
  ∀ t ∈ S, ¬ Score.Dominates t s

/-- The headline never lies: a work-factor minimiser is on the frontier. -/
theorem Score.onFrontier_of_workFactor_min {e : ℕ} (he : e ≠ 0) {S : Set Score}
    {s : Score} (hpos : 0 < s.advantage) (hbud : 0 < s.budget)
    (hmin : ∀ t ∈ S, s.workFactor e ≤ t.workFactor e) : s.OnFrontier S := by
  intro t ht hdom
  exact absurd (hmin t ht)
    (not_le.mpr (Score.workFactor_lt_of_dominates he hpos hbud hdom))

/-- Domination between whole curves: pointwise better, strictly somewhere.  This
is the order a board should rank submissions by once they report curves; the
`Score` order above is its restriction to a single reported point. -/
def CurveDominates (f g : ℕ → ℝ) : Prop :=
  (∀ q, g q ≤ f q) ∧ ∃ q, g q < f q

/-- **A verified submission.**  This is what the checker certifies and what the
board displays.  `budget_eq` is what ties the two together: the number on the
leaderboard is the number the adversary was constructed with. -/
structure Submission (G : Game.{u, v, w}) where
  /-- The attack itself. -/
  attack : Attack G
  /-- The numbers carried by the submission form. -/
  score : Score
  /-- The proof obligation the agent discharges.  Both numbers on the board
  appear in this statement, so a verified submission cannot be displayed at a
  score it did not prove. -/
  wins : attack.Wins score.budget score.advantage

end Golf
end RandomSystems.CR18
