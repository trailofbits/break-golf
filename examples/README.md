# Examples

| File | Challenge | Verdict |
|---|---|---|
| `Solve.reference.lean` | `spoc128` | verifies — 3 queries, advantage 1, 1.58 bits |
| `Solve.pad.lean` | `spoc128-pad` | verifies — 2 queries, advantage 1, 1.0 bits |

Both are written from scratch: they construct their own queries and prove their
own advantage. `Solve.pad.lean` cites no library attack at all — the mitigation
it breaks is new, so there was nothing to cite.
