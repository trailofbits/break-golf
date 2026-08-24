# break-golf

A board for cryptanalysis results that are **proved**, not run.

A challenge fixes two worlds and the statement you must prove. You write an
adversary and a proof that it distinguishes them. The win is the proof: nothing
is executed, sampled, or replayed, and no human reads the submission to decide
whether it counts.

Status: **the verifier runs.** A `verify:` issue is elaborated in CI against the
challenge's pinned type and audited with `#print axioms`; the verdict comes back
as a comment. Records are still added to `scoring/ledger.json` by hand.

This is a standalone Lake project. It takes the mathematics as a git dependency
pinned to a revision, so a board verifies against a fixed statement of the mode:

```lean
require RandomSystems from git
  "https://github.com/MarcIlunga/random-systems.git" @ "08aec7a7"
```

Build time is a cache, not a problem: Mathlib's oleans come from its CDN via
`lake exe cache get`, and the ~400 MB of pinned-revision and challenge oleans sit
in the Actions cache keyed on the manifest and our own sources.

## Layout

| Path | What it is |
|---|---|
| `challenges/<name>/Challenge.lean` | **Trusted.** Pins the exact types a submission must inhabit. Not part of any upload. |
| `challenges/<name>/Cost.lean` | Platform-generated per submission from the form's numbers. |
| `challenges/<name>/config.json` | Scoring, par, permitted axioms, timeout. The only file you edit to add a challenge. |
| `challenges/<name>/Solve.template.lean` | The skeleton a submitter fills in. |
| `tools/manifest.py` | Derives `docs/data/manifest.json` from `challenges/`. |
| `tools/ledger.py` | Derives `docs/data/ledger.json` from `scoring/ledger.json`, scoring and sorting the records. |
| `tools/record.py` | Adds a verified submission to the ledger. Refuses anything not `proved`. |
| `tools/verify.py` | Verifies one submission: challenge id as `argv[1]`, body on stdin, JSON verdict on stdout. Same interface as lean-golf's. |
| `tools/lint_challenges.py` | Every challenge config carries what the board and the verifier need. |
| `tools/check_site.py` | The static site can load and render its own generated data. |
| `scoring/ledger.json` | The record set. |
| `docs/` | The GitHub Pages site. Static; reads only the two generated files. |
| `examples/` | Test fixtures: a submission that verifies and wins nothing, and its over-claiming twin. |

```sh
python3 tools/manifest.py          # rewrite the manifest
python3 tools/manifest.py --check  # fail if stale
python3 tools/ledger.py            # rescore and sort the records
python3 tools/lint_challenges.py   # configs are complete
python3 tools/check_site.py        # the site can render what the tools generate

printf '%s' "$BODY" | python3 tools/verify.py spoc128    # one submission
```

## CI

`verify.yml` runs on push and pull request: the `--check` gates, the config lint,
the site check, and a battery of submissions the verifier must accept and must
reject — a `sorry`, a `native_decide`, an unknown challenge, a zero advantage, a
body with no Lean block. `workflow_dispatch` verifies one submission on demand
without opening an issue.

`submission.yml` handles a `verify:` issue in two jobs. The first parses
untrusted input and holds **no write scopes**; the second downloads its verdict
and posts the comment. That split is lean-golf's and it is the reason an issue
body cannot reach a token.

## The submitter never writes the statement

A submission is **one declaration** inhabiting a type the challenge pins:

```lean
-- Challenge.lean, trusted. The verifier builds its own copy.
def score : Golf.Score := ⟨budget, advNum, advDen⟩   -- from the submission form

structure Solution where
  strategy : game.Param → PFunDDS.DDE game.Query game.Response
  verdict  : List (game.Query × Option game.Response) → Bool
  wins     : Golf.Attack.Wins (G := game) ⟨strategy, verdict⟩ score.budget score.advantage
```

```lean
-- Solve.lean, the upload.
def solution : Challenge.SpoC128.Solution where
  strategy := …
  verdict  := …
  wins     := …
```

One structure rather than three loose names, because the loose names collide:
a `Solve.lean` that imports a `Challenge.lean` already declaring
`strategy`/`verdict`/`attackWins` fails with *"has already been declared"*.
Making the submission a **value of a trusted type** removes the collision and
reduces the verifier's type check to a single `#check`.

### Why the submitter choosing the score is safe

Two things have to hold, and neither is taken on trust.

**The numbers are part of the proposition.** The platform writes them into
`Cost.lean`, `Challenge.lean` builds `score` from them, and `score` appears
inside the type of `Solution.wins`. Changing a number changes what must be
proved.

**The submission must inhabit *our* type.** The audit step imports the trusted
challenge alongside the submission and elaborates

```lean
example : Challenge.SpoC128.Solution := Solution.SpoC128.solution
```

so a submission that declares its own `Challenge.SpoC128.Solution` collides with
ours, and one that uses any other type fails to typecheck. Without this step a
submission that simply never imports the challenge can define a trivial
structure of the same name and be "proved" at 0 bits — that hole was real, and
both attacks are now CI cases.

**The query count needs no separate proof.** It is not a claim about a finished
adversary; it is a *constructor argument*. `Attack.distinguisher q` is
`DDD.ofDDE strategy q verdict`, truncated at `q` by construction, and
`Attack.silent_past` proves it issues nothing beyond it. There is no way to
overspend a budget, so there is nothing to check.



`budget`, `advNum` and `advDen` come from the submission form, and they are not
trusted. They do not need to be: the platform substitutes them into `Cost.lean`,
`Challenge.lean` builds `score` from them, and `score` appears **inside
`Solution.wins`**. The numbers are therefore part of the proposition, not a claim
about it.

Checked against the real SpoC-128 attack:

| Claim | Result |
|---|---|
| `budget = 3`, advantage `1` | compiles — the honest claim |
| `budget = 1`, advantage `1` | **fails** — `Wins 1 1` is a different, stronger theorem |
| `budget = 3`, advantage `2` | **fails** — nothing can exceed advantage 1 |

And there is no incentive to understate: `score = log₂(budget / advantage^e)`, so
a smaller claimed advantage or a larger claimed budget *raises* the score. Both
directions are worse. The only move is the tightest claim you can actually prove.

Four more rejections the verifier makes without reading anything:

| The cheat | The verdict |
|---|---|
| weaken the claim | type mismatch against the pinned `Solution` |
| add a convenient hypothesis | same |
| `sorry` the proof | `sorryAx` is not in `permitted_axioms` |
| `native_decide` / raised `maxHeartbeats` | rejected outright |

## Scoring

Nothing is fixed in advance. On a scheme nobody has studied, what advantage is
reachable at what cost is the research question, so any target is a guess — and a
target set too high scores a genuine `2⁻³⁰` distinguisher as zero. The board
measures the result instead:

```
score = log₂( budget / advantage^e )
```

Queries per unit advantage; its log base two is the security level in bits the
attack refutes. Lower is better. Understating your advantage *raises* the score,
so there is nothing to gain by claiming less than you can prove.

`e` is per challenge and has no default. `e = 2` for a decision game — an
advantage `α` needs about `α⁻²` repetitions to amplify — and `e = 1` for a
search-flavoured one. Both conventions are in the literature and the
inconsistency is known (Micciancio–Walter, *On the Bit Security of Cryptographic
Primitives*), so a challenge states which it uses.

**Par is the designer's own claim**, taken from the specification, so no guess
about attack difficulty appears anywhere. Under par is a break of the claim.

Records are listed best score first. That is the whole ranking.
