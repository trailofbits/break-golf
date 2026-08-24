import Lake
open Lake DSL

package BreakGolf where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned to a SHA, not a branch name: a board must verify against a fixed
-- statement of the mode, and `spoc/full-aead-break` moves.
require RandomSystems from git
  "https://github.com/MarcIlunga/random-systems.git" @ "08aec7a7"

/-- The generic board layer plus one module per challenge instance. -/
@[default_target]
lean_lib Golf

/-- The trusted per-challenge statements. The verifier builds these itself; they
are never part of an upload. -/
lean_lib Challenges where
  srcDir := "challenges"
  globs := #[.submodules `Challenges]

/-- A submission under verification, and the verifier's own driver on top of it.

`Verify.lean` is written by the verifier, never by the submitter, and it is the
top of the build: it imports the trusted challenge *first*, then the submission,
then binds the submission to our type. So the challenge is ours by construction
rather than by a check run afterwards. -/
lean_lib Solutions where
  srcDir := "solutions"
  globs := #[.submodules `Solution, .one `Verify]
