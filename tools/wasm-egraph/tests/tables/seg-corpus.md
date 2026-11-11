| function | result | changed | every-run | e-nodes | steps | search ms | note |
|---|---|---|---|---|---|---|---|
| `tee_form` | proved | yes | yes | 0 | 0 | 0.8 |  |
| `set_get_dead` | proved | yes | yes | 14 | 2 | 0.8 |  |
| `swap_locals` | proved | yes | yes | 0 | 0 | 0.5 |  |
| `dead_store_total` | proved | yes | yes | 0 | 0 | 0.5 |  |
| `dropped_total` | proved | yes | yes | 0 | 0 | 0.5 |  |
| `dropped_div_kept` | proved | yes | yes | 0 | 0 | 0.5 |  |
| `dropped_div_removed` | unknown | yes |  | 3 | 0 | 0.8 | the trap of (i32.div_u (local.get 0) (local.get 1)) is not covered |
| `div_by_const_dropped` | proved | yes | yes | 0 | 0 | 0.5 |  |
| `div_recomputed` | proved | yes | yes | 0 | 0 | 0.5 |  |
| `trap_order` | proved | yes | yes | 6 | 1 | 0.8 |  |
| `sdiv_pow2` | proved | yes | yes | 11 | 1 | 0.9 |  |
| `sdiv_pow2_i64` | proved | yes | yes | 11 | 1 | 0.9 |  |
| `sdiv_not_shift` | unknown | yes |  | 26 | 0 | 2.0 | no proof of (i32.div_s (local.get 0) (i32.const 2)) = (i32.shr_s (local.get 0) (i32.const 1)) |
| `srem_eqz` | proved | yes | yes | 13 | 1 | 0.9 |  |
| `shift_shift` | proved | yes | yes | 7 | 1 | 0.7 |  |
| `shift_shift_too_far` | unknown | yes |  | 16 | 0 | 1.3 | no proof of (i32.shl (i32.shl (local.get 0) (i32.const 20)) (i32.const 20)) = (i32.shl (local.get 0) (i32.const 40)) |
| `ltu_one` | proved | yes | yes | 14 | 2 | 0.8 |  |
| `gtu_zero` | proved | yes | yes | 8 | 1 | 0.7 |  |
| `sign_test` | proved | yes | yes | 7 | 1 | 0.6 |  |
| `cse_tee` | proved | yes | yes | 0 | 0 | 3.5 |  |
| `wrong_local` | unknown | yes |  | 4 | 0 | 0.6 | no proof of (local.get 0) = (local.get 1) |
