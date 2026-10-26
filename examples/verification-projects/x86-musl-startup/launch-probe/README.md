# Real launches of `checksum.elf`

`launch_dump.c` is a small static musl ptrace tracer. It forks; the child
`execve`s the target with an empty environment and stops right after the exec,
before the target runs any instruction. The tracer then prints the entry
registers, the initial program break (`start_brk` from `/proc/<pid>/stat`),
`/proc/<pid>/maps`, and every byte from RSP to the top of `[stack]`.

    python3 tools/verification-projects/x86_launch_probe.py record    # bwrap, else podman
    python3 tools/verification-projects/x86_launch_probe.py gen-lean  # X86RealisticLaunchData.lean

`recorded-norandom.txt` is recorded with `ADDR_NO_RANDOMIZE` and
`recorded-randomized.txt` with full ASLR. Both run as `/checksum` with argv
`checksum` under `bwrap --unshare-all --clearenv`. The Lean module
`Silmaril.Process.LPS.Machines.X86RealisticLaunchRecorded` proves each
recording is in the realistic launch domain (`X86RealisticLaunch`), with the
exact stack bytes, and proves that no old `X86Launch` entry stack with that RSP
agrees with the recording, even on their common prefix.
