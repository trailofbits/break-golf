/-
Aggregator root of `lean_lib Golf`: the generic board layer plus one module per
challenge instance. The verifier builds this, then the challenge's own
`Challenge.lean`, then the submission.
-/
import Golf.Game
import Golf.Instances.SpoC128.Interface
import Golf.Instances.SpoC128Pad.Interface
