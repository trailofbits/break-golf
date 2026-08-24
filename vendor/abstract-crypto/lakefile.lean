import Lake
open Lake DSL

/-
Stub for the sibling `abstract-crypto` package that the pinned random-systems
revision requires by relative path.

break-golf's challenge chain reaches exactly two modules from it, `CCWidget` and
`graph`, and both are presentation layers — a proof-widget engine and a rendering
helper. Neither contributes a name to any statement or proof in the chain.

The stubs are empty ON PURPOSE, and that is what makes them safe: had anything in
the chain actually used a declaration from these modules, the build would fail
with an unknown identifier rather than quietly proving something weaker.
-/
package AbstractCrypto where
  buildDir := (get_config? verificationBuildDir).getD ".lake/build"

lean_lib AbstractCrypto
lean_lib CCWidget
lean_lib graph
