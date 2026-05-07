import Lake
open Lake DSL

package «climber» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Climber» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
