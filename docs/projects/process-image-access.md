# Instruction reads through process images

`Silmaril.Process.ImageAccess.Contract.{Defs,Thms}` is the ISA- and
backing-independent contract. It fixes byte-span requests and outcomes but is
parameterized by the result type and by the reader. It imports neither an ISA
nor `Process.Memory`. `Silmaril.Process.ImageAccess.Defs` re-exports it and
implements the concrete image adapter. Together they separate three jobs:

| Layer | Job in this slice |
|---|---|
| Instruction | Computes an address and width, issues a data or fetch request, and interprets the returned bytes. A decoded x86 `MOV` load uses the pre-state and consumed instruction length, including for RIP-relative addresses. |
| Image | Chooses visibility for the whole span: mapped bytes, hidden by policy, or delegated to a named service. Mapped reads still enforce the existing data/execute permissions, bounds and byte backing. |
| Process | Supplies the delegated service answers for a fixed snapshot. Delegation checks the bounds and reply size; it does not imply permission, freshness or equivalence to a concrete image. |

`Image.full` exposes the existing mapping policy. `Image.owned` restricts visibility
without reclassifying hidden memory as unmapped. A hidden span yields `unavailable`
if the view does not describe it, or `ub` if the client promised not to access it.
`fault` remains a separate outcome for a backing/permission failure. Ownership and
service routing are metadata outside the instruction's register state. They do not
create bytes that a load can observe.

## Proof workflow

For this deterministic, read-only fragment, `Program.wp simple post` requires a
successful answer at each request and the postcondition at the final value.
`Program.wp_bind` makes the second fragment's WP the first fragment's
postcondition, including when the next address depends on the first reply.
`Program.wp_iff_run` gives successful
completion, not just the absence of UB: it also excludes unavailable views and
concrete faults. To reuse the proof, show that `Reader.Refines complex simple`
preserves each successful simple reply, then use `Program.wp_transfer`. Chain
independent agreements with `Reader.Refines.trans`. The relation says nothing about
failed source requests. `X86.load_exec_of_wp` transfers the result to the existing
`Ext.exec` while framing the original memory; `X86.load_full` also preserves the
legacy concrete fault. Neither theorem changes any existing entry point.

`Silmaril.Process.ImageAccess.X86.Checks` proves this chain for one decoded
`mov eax, [rbx]`: from the owned view, through a delegated snapshot service,
to the full view and then `Ext.exec`. It checks the fixture's instruction bytes
with the existing decoder, checks fetch separately, and proves the exact successor
core. A third, mapped byte is hidden from both restricted views. Separate cases
distinguish a hidden span, a request straddling ownership, a concrete permission
failure, and a malformed service response.

The architectural check uses the [Intel SDM, order 325462-090](https://cdrdv2-public.intel.com/874240/325462-090-sdm-vol-1-2abcd-3abcd-4.pdf):
Vol. 2, `MOV` (`8B /r`, with `REX.W` for the 64-bit operand), and Vol. 1 §3.4.1.1
for 32-bit destination zero extension in 64-bit mode. The legacy equivalence
theorem is relative to this repository's decoded address and memory rules; it
does not establish architectural fault priority, exception delivery, or generic
fetch/decode correctness.

`Silmaril.Process.ImageAccess.X86.FragmentChecks` composes two loads:
`mov eax, [rbx]` reads a pointer and `mov ecx, [rax]` follows it. The small
reader is just a table of two admitted requests and their bytes: it has no page
map, byte backing, or permission machinery. The full reader uses concrete
`Memory` over the whole region. A proof checks that each admitted reply agrees;
`wp_bind` and `wp_transfer` then prove the same fragment postcondition for both,
and the bridge recovers two legacy `Ext.exec` steps. Removing the target table
entry makes the small reader stop with UB; it does not establish a hardware
fault. A bare `Reader` is only a function type: a new backend must establish any
needed reply-shape, permission and agreement properties.

```sh
lake build --wfail Silmaril.Process.ImageAccess.X86.Checks Silmaril.Process.ImageAccess.X86.FragmentChecks
```

There are no writes, service transitions, Linux events, scheduler steps, or
concurrency claims in this slice. A future allocator adapter should specify a
service call at an ABI boundary, using pre/post ownership and a footprint; an
ordinary data read should not silently execute an allocator. A concurrent lift
needs an explicit rely that the served bytes/permissions are stable until the
operation commits (or a linearization proof), and a guarantee that the operation
changes only its declared resources. Nondeterministic services need a relation
that covers every concrete reply and a separate progress obligation; the
deterministic equality of replies here does not supply those facts.
