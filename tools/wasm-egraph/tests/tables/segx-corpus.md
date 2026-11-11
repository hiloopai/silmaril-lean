| function | result | changed | every-run | e-nodes | steps | search ms | note |
|---|---|---|---|---|---|---|---|
| `sel_true` | proved | yes | yes | 87831 | 7 | 8118.1 |  |
| `sel_false` | proved | yes | yes | 61960 | 4 | 5015.4 |  |
| `sel_same` | proved | yes | yes | 1252 | 4 | 4.2 |  |
| `sel_both` | proved | yes | yes | 24 | 2 | 0.6 |  |
| `sel_trap` | proved | yes | yes | 82622 | 21 | 6861.2 |  |
| `sel_seg` | proved | yes | yes | 82618 | 7 | 10516.0 |  |
| `sel_wrong` | unknown | yes |  | 152541 | 0 | 11517.3 | no proof of (i32.xor (local.get 1) (i32.and (i32.xor (local.get 0) (local.get 1)) (i32.sub (i32.const 0) (i32.ne (i32.const 1) (i32.const 0))))) = (local.get 1) |
| `sel_trap_lost` | unknown | yes |  | 143229 | 0 | 3328.4 | no proof of (i32.xor (local.get 2) (i32.and (i32.xor (i32.div_u (local.get 0) (local.get 1)) (local.get 2)) (i32.sub (i32.const 0) (i32.ne (local.get 0) (i32.const 0))))) = (local.get 2) |
| `func_renumber` | proved | yes | yes | 0 | 0 | 0.3 |  |
| `func_merge` | proved | yes | yes | 0 | 0 | 0.3 |  |
| `func_zero_init` | proved | yes | yes | 5 | 2 | 0.5 |  |
| `func_trap` | proved | yes | yes | 0 | 0 | 0.3 |  |
| `func_select` | proved | yes | yes | 0 | 0 | 0.3 |  |
| `func_wrong` | unknown | yes |  | 6 | 0 | 0.5 | no proof of (i32.const 0) = (local.get 0) |
