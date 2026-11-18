import Lake
open Lake DSL

package «srnsgraph» where
  leanOptions := #[
    -- Enable well-founded recursion default (useful for dependent types)
    ⟨`autoImplicit, false⟩
  ]

lean_lib «Basic» where
  srcDir := "proofs"

@[default_target]
lean_exe «basic» where
  root := `Basic
  srcDir := "proofs"
