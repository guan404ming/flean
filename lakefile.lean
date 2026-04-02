import Lake
open Lake DSL

package flean where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Flean where
  srcDir := "."
