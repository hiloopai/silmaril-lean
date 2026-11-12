module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Frame
public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcPut

/-!
# ptmalloc: x86 block simulation — definitions

Layer (d) on silmaril's x86 machines (namespace `Silmaril.Libc.Ptmalloc.X86sim`):

* the machines as `Mach`: `fsMach` (`Str9Fs`, where blocks are proved) and `str9kMach` (`Str9K`,
  the process machine), the memory as a `MemView` (`memView`), lifts `Triple.liftK`,
  `BlockSim.liftK`;
* the **generic blocks**, independent of the glibc version: gcc's inlined `tcache_get`
  (`TcGetSeq`, `tcGetBlock`, footprint `tcGetCells`) and `tcache_put` (`TcPutSeq`,
  `tcPutBlock`, `tcPutCells`), for any code bytes carrying the sequence, any load address, any
  `Config`/`Layout` of the x86-64 tcache shape (`TcShape`);
* the address facts block pres use: `FpApart` (footprint apart from the surroundings and the
  code), `PayloadFresh`, `RepTouches` (the bytes `LocalAt` reads);
* the layer-(c) leaf lemmas the blocks consume: `Task.x86sim.repTcacheGet`,
  `Task.x86sim.repTcachePut` (open).

Per-version content (code bytes, decode facts, entry records) is in
`Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.*` (glibc 2.39).
-/
