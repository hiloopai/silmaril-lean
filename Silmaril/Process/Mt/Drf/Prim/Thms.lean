module

public import Silmaril.Process.Mt.Drf.Prim.Defs
public import Silmaril.Process.Mt.Drf.Thms

/-!
# The bridge with implemented primitives

* **`drf_prims`** (proved): if the primitive implementations are correct under `M`
  (`PrimsCorrect`, the explicit per-model assumption) and the client with atomic primitives is
  race free modulo synchronisation (`Cert`), then every drained configuration that the real
  process (primitives implemented, store buffers, model `M`) reaches with all threads in client
  code is, seen through `β`, reached by the SC semantics with atomic primitives. Safety proved of
  that semantics (by decomposing it into single-threaded problems) therefore holds of the real
  process under x86-TSO and XL.
* `drf_glibc`: the instance for glibc's locks, conditional on `Task.glibcLocks M`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Drf

/-- **DRF modulo primitives, with implemented primitives, under TSO and XL.** -/
theorem drf_prims {M : Model} {P : Nat → PrimSpec} {I : Nat → PrimImpl} {cells : Nat → Prop}
    {β : Mem → Mem} (hP : PrimsCorrect M P I cells β) {cl : Client} {N : Nat}
    {cts0 : Nat → cl.St} {m0 : Mem} (hav : cl.Avoids cells)
    (hok : cl.CallsOk P M N ⟨cts0, β m0⟩) {R : Cfg (cl.withSpec P) → Own → Prop}
    (hc : Cert (cl.withSpec P) N R) {o : Own} (h0 : R ⟨cts0, β m0⟩ o)
    {C : BCfg (cl.withImpl I)} {cts : Nat → cl.St}
    (h : BReach M (cl.withImpl I) N (⟨fun u => .cl (cts0 u), m0⟩ : Cfg (cl.withImpl I)).toB C)
    (hd : C.Drained) (hq : ∀ u, C.ts u = .cl (cts u)) :
    ScReach (cl.withSpec P) N ⟨cts0, β m0⟩ ⟨cts, β C.mem⟩ :=
  drf_sc_drained hc h0 (hP cl N cts0 m0 hav hok C cts h hd hq) (fun _ => rfl)

/-- **glibc's locks**: with `Task.glibcLocks M`, a client of glibc's mutex and recursive stream
lock that is race free modulo those locks has, under TSO and XL, only the drained quiescent
configurations of its SC semantics with atomic locks. -/
theorem drf_glibc {M : Model} (hT : Task.glibcLocks M) {self : Nat → Nat} {locks : Nat → Bool}
    (hself : ∀ t u, self t = self u → t = u) (hnz : ∀ t, self t ≠ 0)
    (hdisj : Glibc.LocksDisjoint locks) {cl : Client} {N : Nat} {cts0 : Nat → cl.St} {m0 : Mem}
    (hav : cl.Avoids (Glibc.lockCells locks))
    (hok : cl.CallsOk (Glibc.spec self locks) M N ⟨cts0, Glibc.absMem locks m0⟩)
    {R : Cfg (cl.withSpec (Glibc.spec self locks)) → Own → Prop}
    (hc : Cert (cl.withSpec (Glibc.spec self locks)) N R) {o : Own}
    (h0 : R ⟨cts0, Glibc.absMem locks m0⟩ o) {C : BCfg (cl.withImpl (Glibc.impl self))}
    {cts : Nat → cl.St}
    (h : BReach M (cl.withImpl (Glibc.impl self)) N
      (⟨fun u => .cl (cts0 u), m0⟩ : Cfg (cl.withImpl (Glibc.impl self))).toB C)
    (hd : C.Drained) (hq : ∀ u, C.ts u = .cl (cts u)) :
    ScReach (cl.withSpec (Glibc.spec self locks)) N ⟨cts0, Glibc.absMem locks m0⟩
      ⟨cts, Glibc.absMem locks C.mem⟩ :=
  drf_prims (hT self locks hself hnz hdisj) hav hok hc h0 h hd hq

end Silmaril.Process.Mt.Drf
