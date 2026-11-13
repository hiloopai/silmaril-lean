module

public import Silmaril.Machine.SystemV.Abi.DataLayout.Defs
public import Silmaril.Data.Layout.Cerberus.Thms

/-!
# Native layout agreement

`layoutOfCtype` and `declLayout sysvX86_64` agree on the glibc 2.39 malloc structures, the
`Cerb.testEnv` structs and union, and on `float` members (`Cerb.floatEnv`, where Cerberus'
concrete layout differs), checked by kernel evaluation.
-/

@[expose] public section

namespace Silmaril.Machine.SystemV.Abi.DataLayout

open Silmaril.Data.Layout Silmaril.Data.Layout.Cerb Silmaril.Data.Layout.Glibc.Malloc

theorem malloc_agree :
    (["malloc_chunk", "malloc_state", "malloc_par", "tcache_entry",
      "tcache_perthread_struct"].map fun tag =>
        nativeLayout (env sysvX86_64) .struct tag ==
          ourLayout sysvX86_64 (env sysvX86_64) .struct tag) = [true, true, true, true, true] := by
  decide +kernel

theorem test_agree :
    (([(.struct, "pad"), (.union, "u"), (.struct, "nest"), (.struct, "over")] : List (Kind × String)).map
      fun (k, tag) => nativeLayout testEnv k tag == ourLayout sysvX86_64 testEnv k tag) =
      [true, true, true, true] := by
  decide +kernel

theorem float_agree :
    nativeLayout floatEnv .struct "cf" = ourLayout sysvX86_64 floatEnv .struct "cf" := by
  decide +kernel

end Silmaril.Machine.SystemV.Abi.DataLayout
