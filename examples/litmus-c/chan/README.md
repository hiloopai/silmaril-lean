# Channel C programs

Two single-producer single-consumer channels. The producer `P0` sends `1, 2, 3` and the
consumer `P1` receives three values into `r1, r2, r3`:

| dir | protocol | locations |
|---|---|---|
| `mailbox` | one slot, sequence numbers: `seq` (producer) counts messages in, `ack` (consumer) counts messages out | `data`, `seq`, `ack`, `r1`–`r3` |
| `ring` | two slots, `tail` (producer) and `head` (consumer) counters, message `k` in slot `(k - 1) % 2` | `s0`, `s1`, `tail`, `head`, `r1`–`r3` |

- Every location is an `unsigned` at a fixed address (`chan.h`), so all accesses are absolute
  `[disp32]` operands. Payloads are plain (`ST_NA`/`LD_NA`, volatile); control words use C11
  release stores and acquire loads. Every control word has a single writer.
- `-DSWAP` builds the mutant: the producer publishes the control word before it writes the
  payload.
- `obj/<variant>.<compiler>.o` (`ok`/`swap`, `gcc`/`clang`): the compiled objects, pinned in
  `objects.sha256`; the compilers and flags are the pins of `../toolchains.txt`.
  `tools/litmus-x86 chan compile --check` recompiles all 8 and compares bytes.

`tools/litmus-x86 chan` translation-validates the objects into CIR
(`Silmaril/X86/Concurrency/Cir/Tv/Chan/Defs.lean`) and writes `tools/litmus-x86/export/chan.json`
for `tools/litmus-run --json`.
