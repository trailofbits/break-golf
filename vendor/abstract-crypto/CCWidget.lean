import Lean

/-!
# Stub for the `CCDiagram` proof-widget engine

The pinned random-systems revision imports this module to register semantic roles
for an editor panel: `cc_diagram_application`, `cc_diagram_attachment`, and the
rest populate a *rendering* registry and contribute nothing to any statement or
proof.

This stub re-declares those commands as no-ops so the chain elaborates without
the org-internal `abstract-crypto` package. It deliberately declares nothing
else. If anything downstream ever took a real definition from the engine, the
build would fail with an unknown identifier rather than proving something
weaker — which is exactly how the two earlier, emptier versions of this stub
failed.
-/
open Lean Elab Command

/-- Registry entries take an identifier followed by arity numerals. -/
syntax ccDiagramArg := (ident <|> num <|> str)

elab "cc_diagram_application" (ppSpace ccDiagramArg)* : command => pure ()
elab "cc_diagram_attachment" (ppSpace ccDiagramArg)* : command => pure ()
elab "cc_diagram_game" (ppSpace ccDiagramArg)* : command => pure ()
elab "cc_diagram_winning" (ppSpace ccDiagramArg)* : command => pure ()
elab "cc_diagram_distance" (ppSpace ccDiagramArg)* : command => pure ()
elab "cc_diagram_conditional" (ppSpace ccDiagramArg)* : command => pure ()
elab "cc_diagram_transparent" (ppSpace ccDiagramArg)* : command => pure ()

elab "#cc_diagram_rule_check" (ppSpace ccDiagramArg)* : command => pure ()

/-- `cc_diagram_labels` is a comma-separated list of `ident "label"` pairs. -/
syntax ccDiagramLabel := ident (ppSpace str)?
elab "cc_diagram_labels" ccDiagramLabel,+ : command => pure ()
