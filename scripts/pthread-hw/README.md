# pthread programs on hardware

Eight small pthread programs (`src/p*.c`) and two experiments (`src/x*.c`), checked
against the simple pthread model (`Silmaril.Process.Mt.Pthread.Simple`) and the glibc
representations the implementation obligations assume (`Silmaril.Process.Mt.Pthread.Glibc`).

```sh
scripts/pthread-hw/build.sh OUT        # gcc -O2 against the host glibc; prints OUT/PINS (SHA-256)
python3 -I scripts/pthread-hw/run.py OUT 300 2000000
```

`build.sh` uses fixed flags, so the pins can be reproduced with the same gcc and glibc. Two
builds on the recording machine gave identical hashes.

| program | what it does | predicted outcome set |
|---|---|---|
| `p1_mutex_counter` | 2 threads × 100 000 increments under a normal mutex | `{200000}` |
| `p2_prodcons_cond` | producer/consumer, one slot, mutex + 2 condvars, waits in loops | `{200010000}` |
| `p3_once` | 4 threads, one `pthread_once` | `{"1 4"}` |
| `p4_tls_keys` | 4 threads, one key with a destructor | `{"4 4 0"}` |
| `p5_racy_counter` | **racy**: 2 threads × 100 000 unlocked `volatile` increments (`mov`/`add`/`mov`) | `[2, 200000]` |
| `p6_spin_counter` | `p1` with a spin lock | `{200000}` |
| `p7_sem_barrier` | semaphore ping-pong, then a 4-thread barrier | `{"abababababababababab 4 1"}` |
| `p8_mutex_errors` | POSIX error returns: errorcheck, recursive, trylock, spin trylock, `sem_trywait`, rwlock, self-join | one line of codes |

Experiments:

* `x1_unlock_fence`: store buffering with an unlock of the thread's own lock between the
  store and the load. glibc 2.39's `pthread_spin_unlock` is a plain `movl $1` (TSO allows the
  weak outcome); `pthread_mutex_unlock` in multi-threaded mode is `xchg` (TSO forbids it).
* `x2_lockword`: `__libc_single_threaded` flips from 1 to 0 at the first `pthread_create`
  (the single-threaded fast paths of `pthread_mutex_lock/unlock` use plain accesses while it
  is 1); a normal mutex word is 0 free, 1 held, 2 held with waiters, `__owner` is the
  holder's tid; a spin lock word is 1 free, at most 0 held, driven below 0 by failed
  `lock decl`s (never below `-n` with `n` spinning threads) and reset to 1 by unlock.

## Recorded run

Intel Core i7-8700 (6 cores, 12 threads), Ubuntu 24.04, Linux 6.8, gcc 13.3.0, glibc
2.39-0ubuntu8.9 (`libc.so.6` SHA-256 `3a15d668…f7498bf`), 2026-11-13, 300 runs per program,
2 000 000 iterations per `x1` variant:

```
p1_mutex_counter: 300 runs, predicted {200000}, observed {'200000': 300}
p2_prodcons_cond: 300 runs, predicted {200010000}, observed {'200010000': 300}
p3_once: 300 runs, predicted {'1 4'}, observed {'1 4': 300}
p4_tls_keys: 300 runs, predicted {'4 4 0'}, observed {'4 4 0': 300}
p5_racy_counter: 300 runs, predicted [2, 200000], observed 272 distinct outcomes, min 98422, max 145373, 0 runs at 2N
p6_spin_counter: 300 runs, predicted {200000}, observed {'200000': 300}
p7_sem_barrier: 300 runs, predicted {'abab...ab 4 1'}, observed {'abababababababababab 4 1': 300}
p8_mutex_errors: 300 runs, predicted {the POSIX/glibc codes}, observed {'ec 0 35 1 0 rec 0 0 0 0 1 try 16 spin 0 16 sem -1 11 rw 0 0 16 0 35 join 35': 300}
SB+none: 2000000 runs, r0r1 {00: 25328, 01: 973636, 10: 1001035, 11: 1}
SB+spin_unlock: 2000000 runs, r0r1 {00: 6747, 01: 950124, 10: 1043104, 11: 25}
SB+mutex_unlock: 2000000 runs, r0r1 {00: 0, 01: 899653, 10: 988330, 11: 112017}
SB+mfence: 2000000 runs, r0r1 {00: 0, 01: 674834, 10: 998207, 11: 326959}
spin_unlock is not observed to be a barrier (weak outcome 6747 times; x86-TSO allows it for a plain store)
single_threaded 1->0 mutex free 0 held(st) 1 owner(st) 1 held 1 owner 1 waiters 2 after 0 owner_after 0 spin free 1 held 0 contended -4 min -4 end 1
OK: every observed outcome is allowed
```

What this shows, and what it does not:

* Every observed output is in its predicted set. The race-free programs printed one output in
  every run, which is consistent with their predicted (singleton) sets but does not prove them
  deterministic. The racy counter lost updates in almost every run (an earlier run of 300 saw
  one run reach 2N); the theoretical minimum 2 was never seen, as expected for a schedule that
  needs near-perfect interleaving.
* `pthread_spin_unlock` is **not** a barrier on this machine (store buffering across it, 0.34 %
  of iterations), while `pthread_mutex_unlock` and `mfence` are. This is why the spin lock's
  model places the unlock's linearization point at the flush of its store
  (`Pthread/Glibc/Defs`), and why `pthread_spin_init` (the same plain store) is not treated as
  an atomic initialisation under TSO.
* The lock-word values match the representations the glibc models assume. A run never shows
  that a value is impossible.
