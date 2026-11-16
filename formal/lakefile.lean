import Lake
open Lake DSL

package «nanoimage-formal» where
  leanOptions := #[]

@[default_target]
lean_lib «NANO» where
  srcDir := "."

/-- Differential-testing driver (see formal/tools/cdiff.py). -/
lean_exe «cdiff» where
  root := `CDiff
