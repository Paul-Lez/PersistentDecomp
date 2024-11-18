import Lake
open Lake DSL

package "PersistentDecomp" where
  leanOptions := #[
    ⟨`autoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`relaxedAutoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib PersistentDecomp where
  -- add any library configuration options here
