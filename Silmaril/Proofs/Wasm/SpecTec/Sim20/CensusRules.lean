module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Census

/-!
# The reduction-rule census: `Step_read` and `Step`

The censuses of `Step_read` and `Step` (wasm-1.0 against wasm-2.0, wasm-2.0 against wasm-3.0),
computed by the kernel. Split from `Sim20/Census.lean` to keep each module fast.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Census

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec

set_option maxRecDepth 100000

/-- The census of `Step_read`, wasm-1.0 against wasm-2.0 (tally: 4 same, 0 up to
`admininstr`, 9 changed, 0 renamed, 0 absent). -/
theorem census_read_10_20 :
    census Scripts.Wasm10.fixed Scripts.Wasm20.fixed "Step_read" =
  [(0, "block", .changed 0),
  (1, "loop", .changed 1),
  (2, "call", .same 2),
  (3, "call_indirect-call", .changed 3),
  (4, "call_indirect-trap", .changed 4),
  (5, "call_addr", .changed 5),
  (6, "local.get", .same 7),
  (7, "global.get", .same 8),
  (8, "load-num-trap", .changed 22),
  (9, "load-num-val", .changed 23),
  (10, "load-pack-trap", .changed 24),
  (11, "load-pack-val", .changed 25),
  (12, "memory.size", .same 36)] := by
  decide +kernel

/-- The tally of `census_read_10_20`. -/
theorem tally_read_10_20 : tally (census Scripts.Wasm10.fixed Scripts.Wasm20.fixed "Step_read") = (4, 0, 9, 0, 0) := by
  rw [census_read_10_20]; rfl

/-- The census of `Step`, wasm-1.0 against wasm-2.0 (tally: 4 same, 0 up to
`admininstr`, 8 changed, 0 renamed, 1 absent). -/
theorem census_step_10_20 :
    census Scripts.Wasm10.fixed Scripts.Wasm20.fixed "Step" =
  [(0, "pure", .changed 0),
  (1, "read", .changed 1),
  (2, "ctxt-label", .changed 2),
  (3, "ctxt-frame", .changed 3),
  (4, "ctxt-instrs", .absent),
  (5, "local.set", .same 4),
  (6, "global.set", .same 5),
  (7, "store-num-trap", .changed 11),
  (8, "store-num-val", .changed 12),
  (9, "store-pack-trap", .changed 13),
  (10, "store-pack-val", .changed 14),
  (11, "memory.grow-succeed", .same 19),
  (12, "memory.grow-fail", .same 20)] := by
  decide +kernel

/-- The tally of `census_step_10_20`. -/
theorem tally_step_10_20 : tally (census Scripts.Wasm10.fixed Scripts.Wasm20.fixed "Step") = (4, 0, 8, 0, 1) := by
  rw [census_step_10_20]; rfl

/-- The census of `Step_read`, wasm-2.0 against wasm-3.0 (tally: 0 same, 0 up to
`admininstr`, 31 changed, 0 renamed, 16 absent). -/
theorem census_read_20_30 :
    census Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step_read" =
  [(0, "block", .changed 0),
  (1, "loop", .changed 1),
  (2, "call", .changed 6),
  (3, "call_indirect-call", .absent),
  (4, "call_indirect-trap", .absent),
  (5, "call_addr", .absent),
  (6, "ref.func", .changed 64),
  (7, "local.get", .changed 23),
  (8, "global.get", .changed 24),
  (9, "table.get-trap", .absent),
  (10, "table.get-val", .changed 26),
  (11, "table.size", .changed 27),
  (12, "table.fill-trap", .absent),
  (13, "table.fill-zero", .changed 29),
  (14, "table.fill-succ", .changed 30),
  (15, "table.copy-trap", .absent),
  (16, "table.copy-zero", .changed 32),
  (17, "table.copy-le", .changed 33),
  (18, "table.copy-gt", .changed 34),
  (19, "table.init-trap", .absent),
  (20, "table.init-zero", .changed 36),
  (21, "table.init-succ", .changed 37),
  (22, "load-num-trap", .absent),
  (23, "load-num-val", .changed 39),
  (24, "load-pack-trap", .absent),
  (25, "load-pack-val", .changed 41),
  (26, "vload-oob", .absent),
  (27, "vload-val", .absent),
  (28, "vload-shape-oob", .absent),
  (29, "vload-shape-val", .absent),
  (30, "vload-splat-oob", .changed 46),
  (31, "vload-splat-val", .changed 47),
  (32, "vload-zero-oob", .changed 48),
  (33, "vload-zero-val", .changed 49),
  (34, "vload_lane-oob", .changed 50),
  (35, "vload_lane-val", .changed 51),
  (36, "memory.size", .changed 52),
  (37, "memory.fill-trap", .absent),
  (38, "memory.fill-zero", .changed 54),
  (39, "memory.fill-succ", .changed 55),
  (40, "memory.copy-trap", .absent),
  (41, "memory.copy-zero", .changed 57),
  (42, "memory.copy-le", .changed 58),
  (43, "memory.copy-gt", .changed 59),
  (44, "memory.init-trap", .absent),
  (45, "memory.init-zero", .changed 61),
  (46, "memory.init-succ", .changed 62)] := by
  decide +kernel

/-- The tally of `census_read_20_30`. -/
theorem tally_read_20_30 : tally (census Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step_read") = (0, 0, 31, 0, 16) := by
  rw [census_read_20_30]; rfl

/-- The census of `Step`, wasm-2.0 against wasm-3.0 (tally: 2 same, 2 up to
`admininstr`, 15 changed, 0 renamed, 3 absent). -/
theorem census_step_20_30 :
    census Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step" =
  [(0, "pure", .changed 0),
  (1, "read", .changed 1),
  (2, "ctxt-label", .changed 3),
  (3, "ctxt-frame", .changed 5),
  (4, "local.set", .admOnly 11),
  (5, "global.set", .admOnly 12),
  (6, "table.set-trap", .absent),
  (7, "table.set-val", .changed 14),
  (8, "table.grow-succeed", .changed 15),
  (9, "table.grow-fail", .changed 16),
  (10, "elem.drop", .same 17),
  (11, "store-num-trap", .absent),
  (12, "store-num-val", .changed 19),
  (13, "store-pack-trap", .absent),
  (14, "store-pack-val", .changed 21),
  (15, "vstore-oob", .changed 22),
  (16, "vstore-val", .changed 23),
  (17, "vstore_lane-oob", .changed 24),
  (18, "vstore_lane-val", .changed 25),
  (19, "memory.grow-succeed", .changed 26),
  (20, "memory.grow-fail", .changed 27),
  (21, "data.drop", .same 28)] := by
  decide +kernel

/-- The tally of `census_step_20_30`. -/
theorem tally_step_20_30 : tally (census Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step") = (2, 2, 15, 0, 3) := by
  rw [census_step_20_30]; rfl

end Silmaril.Wasm.SpecTec.Sim20.Census
