module

public import Silmaril.Project.Shapes.CompilesTo.Defs
public import Silmaril.Project.CompilesTo.Thms
public import Silmaril.Project.Shapes.C.Thms
public import Silmaril.X86.Open9.Thms

/-!
# Proofs for `Silmaril.Project.Shapes.CompilesTo.Thms`: from segments to `c.compiles_to`

* `wholeFirst_of_segments`: the composition theorem of `Silmaril.Compiler.CompilesTo.Sim`, to the
  **first** target return: when no related state at a point is a return, the composed target
  run passes no return before its end (each segment run stops at its first cut point).
* `FnData.implements_of_segments`: every segment of a `FnData` simulated on `Open.isa`, its
  placement enterable and its C function read from entry states `E` (Core entries, one for each
  argument tuple) safe on some tuple give `SysV.Implements` against `F.cfn.meaningFrom E`.
* `canonicalEntry_entry`: the canonical entry of a function with `int` parameters is a Core
  entry (`Params.inv_params`, `argsMem_alloc`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.CompilesTo

open Silmaril.Compiler.CompilesTo
open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.CompilesTo
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified
open Silmaril.Project.Shapes.C (CFn argValues ValueIs)
open Silmaril.X86.SystemV.CApi (Signature Scalar Arguments ReturnValue)

/-! ## Runs that avoid a set until their end -/

/-- A run of `step` from `x` to `y` whose every state before `y` satisfies `P`. -/
inductive RunsAvoid {τ : Type} (step : τ → τ → Prop) (P : τ → Prop) : τ → τ → Prop where
  | refl (x : τ) : RunsAvoid step P x x
  | cons {x x' y : τ} : P x → step x x' → RunsAvoid step P x' y → RunsAvoid step P x y

theorem RunsAvoid.trans {τ : Type} {step : τ → τ → Prop} {P : τ → Prop} {x y z : τ}
    (h₁ : RunsAvoid step P x y) (h₂ : RunsAvoid step P y z) : RunsAvoid step P x z := by
  induction h₁ with
  | refl => exact h₂
  | cons hp hs _ ih => exact .cons hp hs (ih h₂)

theorem RunsAvoid.of_hop {τ : Type} {step : τ → τ → Prop} {cut P : τ → Prop}
    (hP : ∀ u, ¬ cut u → P u) {x y : τ} (h : Hop step cut x y) (hx : P x) :
    RunsAvoid step P x y := by
  induction h with
  | one h => exact .cons hx h (.refl _)
  | more h hu _ ih => exact .cons hx h (ih (hP _ hu))

/-! ## The composition to the first return -/

section Generic

variable {σ τ R : Type}

/-- **Segments give the whole run to the first return**: if every segment is simulated and no
related state at a point is a target return, then from related states at `k` the target runs
to a return through no earlier return. -/
theorem wholeFirst_of_segments (C : Corr σ τ R) (h : ∀ k, C.Segment k)
    (hnf : ∀ k x0 s x, C.rel k x0 s x → ¬ C.tgtFinal x0 x) (k : Nat) (x0 : τ) (s : σ) (x : τ)
    (hs : C.srcAt k s) (hx : C.tgtAt k x) (hr : C.rel k x0 s x) (hsafe : C.src.Safe s) :
    ∃ t r y, Relation.ReflTransGen C.src.step s t ∧ C.src.final t r ∧
      RunsAvoid C.tgtStep (fun m => ¬ C.tgtFinal x0 m) x y ∧ C.tgtFinal x0 y ∧
      C.result x0 r y := by
  have key : ∀ s, Acc (Relation.TransGen fun t u => C.src.step u t) s →
      ∀ k x, C.srcAt k s → C.tgtAt k x → C.rel k x0 s x → C.src.Safe s →
      ∃ t r y, Relation.ReflTransGen C.src.step s t ∧ C.src.final t r ∧
        RunsAvoid C.tgtStep (fun m => ¬ C.tgtFinal x0 m) x y ∧ C.tgtFinal x0 y ∧
        C.result x0 r y := by
    intro s hacc
    induction hacc with
    | intro s _ ih =>
      intro k x hs hx hr hsafe
      obtain ⟨t, y, hst, hxy, hnext⟩ := h k x0 s x hs hx hr hsafe
      have hst' := hst.1
      have hav : RunsAvoid C.tgtStep (fun m => ¬ C.tgtFinal x0 m) x y :=
        RunsAvoid.of_hop (cut := C.tgtCut x0) (P := fun m => ¬ C.tgtFinal x0 m)
          (fun u hu hf => hu (.inr hf)) hxy.1 (hnf k x0 s x hr)
      rcases hnext with ⟨j, htj, hyj, hrj⟩ | ⟨r, hfin, hyf, hres⟩
      · have hsafe' := hsafe.of_reaches hst'.to_reflTransGen
        obtain ⟨u, r, z, h1, h2, h3, h4, h5⟩ := ih t hst'.swap j y htj hyj hrj hsafe'
        exact ⟨u, r, z, hst'.to_reflTransGen.trans h1, h2, hav.trans h3, h4, h5⟩
      · exact ⟨t, r, y, hst'.to_reflTransGen, hfin, hav, hyf, hres⟩
  exact key s (acc_transGen hsafe.2) k x hs hx hr hsafe

end Generic

/-! ## The machine side of the System V shapes -/

theorem rsp_ne_add8 (a : BitVec 64) : a ≠ a + 8#64 := by
  intro h
  bv_omega

theorem sub8_ne_add8 (a : BitVec 64) : a - 8#64 ≠ a + 8#64 := by
  intro h
  bv_omega

/-- **No related state at a point is a return**: at the entry the stack pointer is the entry's,
past it the frame `Frame0` holds it eight bytes below. -/
theorem FnData.notFinal (F : FnData) (I : Model) (k0 : List Frame) :
    ∀ k x0 s x, (F.corr I k0).rel k x0 s x → ¬ (F.corr I k0).tgtFinal x0 x := by
  rintro k x0 s x ⟨p, -, hh⟩ ⟨-, hrsp⟩
  match hk : p.kind with
  | .entry =>
    rw [hk] at hh
    obtain ⟨rfl, -⟩ := hh
    exact rsp_ne_add8 _ hrsp
  | .slots _ _ =>
    rw [hk] at hh
    exact sub8_ne_add8 _ (hh.1.rsp.symm.trans hrsp)
  | .ret _ =>
    rw [hk] at hh
    exact sub8_ne_add8 _ (hh.1.rsp.symm.trans hrsp)

/-- A System V call of the placed function is a `MachineEntry`. -/
theorem machineEntry_of_callEntry {F : FnData} (haddr : F.addr < 2 ^ 64)
    {a : Arguments F.sig.arguments} {m : MState}
    (habi : Silmaril.X86.FnContract.AbiEntry m.core m.memory)
    (hce : Silmaril.Project.Shapes.SysV.CallEntry F.placement F.sig F.frame a m) :
    MachineEntry F.sig F.addr F.code F.frame a m := by
  have hbase : (BitVec.ofNat 64 F.addr).toNat = F.addr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt haddr
  refine ⟨hce.entered.1, ?_, habi, hce.args, hce.room, ⟨hce.read, hce.write⟩, ?_⟩
  · rw [hce.entered.2]
    simp [Silmaril.Project.Shapes.Placement.entry, FnData.placement]
  · have := hce.apart
    simp only [FnData.placement, hbase] at this
    exact this

/-- Runs of `Open.isa` that avoid the returns are `RunsIn` runs. -/
theorem runsIn_of_runsAvoid {m0 x y : MState}
    (h : RunsAvoid (fun x y => Silmaril.X86.Open.isa.step x = some y)
      (fun m => ¬ Returned m0 m) x y) :
    Silmaril.X86.FnContract.RunsIn Silmaril.X86.Open.isa
      (fun m => ¬ Silmaril.X86.FnContract.Returned Silmaril.X86.Open.isa m0 m) x y := by
  induction h with
  | refl => exact .refl _
  | cons hp hs _ ih => exact .step hp hs ih

/-! ## Arguments and results -/

theorem argumentWord_unique {m : MState} {i : Nat} {w w' : Silmaril.X86.Word}
    (h : Silmaril.X86.SystemV.ArgumentWord m i w)
    (h' : Silmaril.X86.SystemV.ArgumentWord m i w') : w = w' := by
  unfold Silmaril.X86.SystemV.ArgumentWord at h h'
  cases hr : Silmaril.X86.sysv64.intArgRegs[i]? with
  | some reg =>
    simp only [hr] at h h'
    exact h.symm.trans h'
  | none =>
    simp only [hr] at h h'
    rw [h] at h'
    have := congrArg Silmaril.X86.wordOfBytes? (Option.some.inj h')
    simpa using this

theorem encodes_unique : ∀ {kind : Scalar} {v v' : kind.Value} {w : Silmaril.X86.Word},
    Silmaril.X86.SystemV.Encodes kind v w → Silmaril.X86.SystemV.Encodes kind v' w → v = v'
  | .int32, _, _, _, h, h' => h.symm.trans h'
  | .uint32, _, _, _, h, h' => h.symm.trans h'
  | .int64, _, _, _, h, h' => h.symm.trans h'
  | .uint64, _, _, _, h, h' => h.symm.trans h'
  | .pointer, _, _, _, h, h' => h.symm.trans h'

/-- The arguments of a System V call are determined by the entry state. -/
theorem argumentsAt_unique {m : MState} :
    ∀ {kinds : List Scalar} (a a' : Arguments kinds) (base : Nat),
      Silmaril.X86.SystemV.ArgumentsAt m a base → Silmaril.X86.SystemV.ArgumentsAt m a' base →
      a = a'
  | _, .nil, .nil, _, _, _ => rfl
  | _, .cons v t, .cons v' t', base, h, h' => by
    simp only [Silmaril.X86.SystemV.ArgumentsAt] at h h'
    obtain ⟨⟨w, hw, he⟩, ht⟩ := h
    obtain ⟨⟨w', hw', he'⟩, ht'⟩ := h'
    obtain rfl := argumentWord_unique hw hw'
    obtain rfl := encodes_unique he he'
    rw [argumentsAt_unique t t' (base + 1) ht ht']

/-- A Core result value held in `rax` is a System V result of the C function. -/
theorem result_of_resultAt : ∀ (kind : Option Scalar) (v : Val) (m : MState),
    ResultAt kind v m → ∃ r : ReturnValue kind, ValueIs kind v r ∧
      Silmaril.X86.SystemV.ResultAt m kind r
  | none, _, _, _ => ⟨(), trivial, trivial⟩
  | some _, _, _, ⟨_, hv, w, henc, hw⟩ => ⟨w, by subst hv; simp only [ValueIs, hw], henc⟩

/-! ## The bridge -/

/-- **Segments give the System V row**: every segment of `F` simulated on `Open.isa`, its
placement enterable, its entry point the procedure body at offset 0, and the C function read
from entry states `E` (Core entries with the empty continuation, one at least for each argument
tuple) safe on some tuple give `SysV.Implements` against `F.cfn.meaningFrom E`. -/
theorem FnData.implements_of_segments (F : FnData)
    (E : Arguments F.sig.arguments → State → Prop)
    (hE : ∀ a s, E a s → F.cfn.CoreEntry [] (argValues a) s) (hex : ∀ a, ∃ s, E a s)
    (haddr : F.addr < 2 ^ 64) (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩)
    (hseg : ∀ k, F.Segment Silmaril.X86.Open.isa k)
    (henter : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open.isa F.placement F.sig
      F.frame)
    (hinh : (F.cfn.meaningFrom E).Inhabited) :
    Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa F.placement F.sig F.frame
      (F.cfn.meaningFrom E) := by
  refine ⟨henter, hinh, ?_⟩
  rintro m - habi ⟨a, hce, hsafeA⟩
  obtain ⟨s, hs⟩ := hex a
  have hcore := hE a s hs
  have hme := machineEntry_of_callEntry haddr habi hce
  have hrel : (F.corr Silmaril.X86.Open.isa []).rel 0 m s m :=
    ⟨_, hp0, rfl, a, hme, hcore⟩
  have hsrc : (F.corr Silmaril.X86.Open.isa []).srcAt 0 s := by
    obtain ⟨-, env, hctl, -⟩ := hcore
    exact ⟨_, hp0, env, hctl⟩
  have htgt : (F.corr Silmaril.X86.Open.isa []).tgtAt 0 m := ⟨_, hp0, by simpa using hme.rip⟩
  obtain ⟨t, v, y, hrun, hfin, hav, hret, hframe, hres⟩ :=
    wholeFirst_of_segments (F.corr Silmaril.X86.Open.isa []) (fun k => hseg k [])
      (FnData.notFinal F _ _) 0 m s m hsrc htgt hrel (hsafeA s hs)
  refine ⟨y, runsIn_of_runsAvoid hav, rfl, ⟨hret.1, hret.2, hframe.calleeSaved⟩,
    hframe.writes, ?_⟩
  intro a' ha' _
  obtain rfl := argumentsAt_unique a' a 0 ha' hce.args
  obtain ⟨r, hv, hr⟩ := result_of_resultAt F.sig.result v y hres
  exact ⟨r, ⟨s, t, v, hs, hrun, hfin, hv⟩, hr⟩

/-! ## The canonical entry -/

theorem canonicalObjs_succ (n : Nat) :
    canonicalObjs (n + 1) = canonicalObjs n ++ [((n : Int), 65536 - 4 * ((n : Int) + 1))] := by
  simp [canonicalObjs, List.range_succ]

theorem length_canonicalObjs (n : Nat) : (canonicalObjs n).length = n := by
  simp [canonicalObjs]

/-- The memory after allocating `ns` from the empty memory at `65536`: the objects
`canonicalObjs` hold `ns`, and the allocator stands below them. -/
theorem canonicalMem_args : ∀ (ns : List Int), ns.length ≤ 15000 →
    Params.ArgsMem (canonicalMem ns) (canonicalObjs ns.length) ns ∧
      (canonicalMem ns).nextId = ns.length ∧
      (canonicalMem ns).lastAddress = 65536 - 4 * (ns.length : Int) ∧
      (canonicalMem ns).dead = [] := by
  intro ns
  induction ns using List.reverseRecOn with
  | nil => intro _; exact ⟨Params.ArgsMem.nil _, rfl, by simp [canonicalMem], rfl⟩
  | append_singleton ns n ih =>
    intro hlen
    simp only [List.length_append, List.length_singleton] at hlen
    obtain ⟨hmem, hid, hlast, hdead⟩ := ih (by omega)
    have hfold : canonicalMem (ns ++ [n]) = argAlloc (canonicalMem ns) n := by
      simp [canonicalMem, List.foldl_append]
    have hnext : Mem.Concrete.nextIntAddress (canonicalMem ns) =
        65536 - 4 * ((ns.length : Int) + 1) := by
      simp only [Mem.Concrete.nextIntAddress, hlast]; omega
    have h := argsMem_alloc hmem (by rw [hlast]; omega) (by rw [hdead]; simp) n
    rw [hid, hnext] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfold, List.length_append, List.length_singleton, canonicalObjs_succ]
      exact h
    · rw [hfold, argAlloc_nextId, hid, List.length_append, List.length_singleton]
      push_cast; ring
    · rw [hfold, argAlloc_lastAddress, hnext, List.length_append, List.length_singleton]
      push_cast; ring
    · rw [hfold, argAlloc_dead, hdead]

/-- The values of `int` arguments are `int`s. -/
theorem argValues_isInt : ∀ {kinds : List Scalar} (a : Arguments kinds),
    (∀ k ∈ kinds, k = .int32) → ∀ n ∈ argValues a, ConvInt.IsInt n
  | _, .nil, _, _, hn => by simp [argValues] at hn
  | _, .cons (kind := kind) v t, hk, n, hn => by
    obtain rfl : kind = .int32 := hk kind (by simp)
    simp only [argValues, List.mem_cons] at hn
    rcases hn with rfl | hn
    · have h1 := BitVec.toInt_lt (x := (v : BitVec 32))
      have h2 := BitVec.le_toInt (x := (v : BitVec 32))
      simp only [Silmaril.X86.SystemV.CApi.Scalar.signed, ConvInt.IsInt]
      constructor <;> omega
    · exact argValues_isInt t (fun k hk' => hk k (by simp [hk'])) n hn

theorem length_argValues : ∀ {kinds : List Scalar} (a : Arguments kinds),
    (argValues a).length = kinds.length
  | _, .nil => rfl
  | _, .cons _ t => by simp [argValues, length_argValues t]

/-- **The canonical entry is a Core entry** for a function with at most six `int` parameters
whose parameter keys are distinct. -/
theorem canonicalEntry_entry {sig : Signature} (F : CFn sig)
    (hint : ∀ k ∈ sig.arguments, k = .int32) (hlen : F.params.length = sig.arguments.length)
    (hsix : sig.arguments.length ≤ 6) (hnd : (F.params.map (·.1.key)).Nodup)
    (a : Arguments sig.arguments) : F.Entry a (F.canonicalEntry a) := by
  have hla : (argValues a).length = F.params.length := by rw [length_argValues, hlen]
  obtain ⟨hmem, hid, hlast, hdead⟩ := canonicalMem_args (argValues a) (by omega)
  rw [hla] at hmem hid hlast
  have hnd' : ((F.params.map (·.1)).map (·.key)).Nodup := by rw [List.map_map]; exact hnd
  have hplen : (F.params.map (·.1)).length = (canonicalObjs F.params.length).length := by
    simp [length_canonicalObjs]
  refine ⟨rfl, _, rfl, by rw [length_argValues, hlen], Params.locals (F.params.map (·.1))
    (canonicalObjs F.params.length), ?_, ?_, ?_⟩
  · have := Params.keys_locals (ps := F.params.map (·.1))
      (objs := canonicalObjs F.params.length) hplen
    simpa [StateStmt.Keys, Function.comp_def] using this
  · rw [paramDefs_eq]
    exact Params.inv_params hnd' hplen hmem (argValues_isInt a hint)
  · refine ⟨fun id hid' => by
      simp [Silmaril.Project.Shapes.C.CFn.canonicalEntry, hdead] at hid', ?_, ?_, ?_, ?_⟩
    · intro l hl
      obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
      have := hmem.below _ (List.of_mem_zip hxo).2
      simpa [Silmaril.Project.Shapes.C.CFn.canonicalEntry, hid] using this
    · intro l hl
      obtain ⟨xo, hxo, rfl⟩ := List.mem_map.mp hl
      have := hmem.above _ (List.of_mem_zip hxo).2
      simpa [Silmaril.Project.Shapes.C.CFn.canonicalEntry, hlast] using this
    · simp only [Silmaril.Project.Shapes.C.CFn.canonicalEntry, hlast]; omega
    · simp only [Silmaril.Project.Shapes.C.CFn.canonicalEntry, hlast]; omega

/-! ## The two readings, and the models -/

/-- A canonical row with universal safety is a standard row: the canonical entry is a Core entry,
so the canonical contract is a sub-spec of the standard one (`SysV.strict_mono`). -/
theorem compilesTo_of_canonical {sig : Signature} {M : Model}
    {p : Silmaril.Project.Shapes.Placement} {frame : Nat} {F : CFn sig}
    (hentry : ∀ a, F.Entry a (F.canonicalEntry a)) (h : CompilesToCanonical M p frame F)
    (hs : F.meaning.Inhabited) : Silmaril.Project.Shapes.C.CompilesTo M p frame F := by
  refine ⟨h.1, hs, Silmaril.Project.Shapes.SysV.strict_mono h.2.2 ?_⟩
  refine ⟨fun m ⟨a, hce, hsafe⟩ => ⟨a, hce, fun s hs' => hs' ▸ hsafe _ (hentry a)⟩,
    fun _ _ _ hf => hf, ?_⟩
  intro m t _ hpost a ha hsafe
  obtain ⟨r, ⟨s, t', v, hs', hrun, hfin, hv⟩, hres⟩ :=
    hpost a ha (fun s hs' => hs' ▸ hsafe _ (hentry a))
  subst hs'
  exact ⟨r, ⟨_, t', v, hentry a, hrun, hfin, hv⟩, hres⟩

/-- A System V implementation on `Open.isa` is one on `Open9.isa` (every state of both is live;
`FnContract.Spec.Strict.toOpen9`). -/
theorem implements_open9_of_open {sig : Signature} {p : Silmaril.Project.Shapes.Placement}
    {frame : Nat} {spec : Silmaril.Project.Shapes.SysV.Meaning sig}
    (h : Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open.isa p sig frame spec) :
    Silmaril.Project.Shapes.SysV.Implements Silmaril.X86.Open9.isa p sig frame spec :=
  ⟨fun a => let ⟨m, _, habi, hce⟩ := h.1 a; ⟨m, trivial, habi, hce⟩, h.2.1,
    Silmaril.X86.FnContract.Spec.Strict.toOpen9 h.2.2⟩

end Silmaril.Proofs.Project.Shapes.CompilesTo

end
