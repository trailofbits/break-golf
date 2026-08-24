# Test fixtures

Submissions used to exercise the pipeline. All three are checked against the real
Lean tree, not written by hand and hoped for.

| File | Cost.lean | Elaborates | Axioms | Board |
|---|---|---|---|---|
| `Solve.null.lean` | `budget 1`, `advNum 0` | yes | clean | rejected: `non_positive` |
| `Solve.overclaim.lean` | `budget 1`, `advNum 1` | **no** — `⊢ False` | `sorryAx` | rejected |
| the real attack | `budget 3`, `advNum 1` | yes | clean | 1.58 bits, under par |

`Solve.null.lean` is the interesting one: it is *honest*. The null adversary asks
nothing and always answers "ideal", so its signed advantage really is 0 and
`Wins budget 0` really is a theorem. The file is not a cheat — it is a correct
proof of a worthless statement, and the scoring function is what discards it:
`log2(budget / advantage^e)` is infinite at advantage 0.

`Solve.overclaim.lean` is byte-identical except for the number on the submission
form. That is the whole demonstration that the claim is not trusted: the number
is substituted into the type of `wins`, so changing it changes what must be
proved.
