module

public import Silmaril.Wasm.Jco.Real.Step.Defs
public import Silmaril.Proofs.Wasm.Jco.Real.Exec
public import Silmaril.Wasm.Jco.Styles.EncWrap.Thms

/-!
# Adaptor instructions against the reference engine: theorems

Proofs in `Silmaril.Proofs.Wasm.Jco.Real.{Top,Mem,Step,Load,Exec}`. Everything is over the real
instance `realInst H P host mi ma` (a Core 3.0 module instance run by silmaril's reference
semantics) at every profile `P` and host `host`, and in a Core frame linked to it (`FrameEnv`).

* **`step_agree`**: for an instruction `i` of the fragment `Frag`, every returned run of
  `XInstr.step` (new locals and stack, new store) is a reference-semantics run of the Core 3.0
  image of `XInstr.toLime fi i` (through `Lime1.Instr.toCore`) from the old stack to the new
  one, ending in a frame of the same module with the new locals. `call g` runs the export `g`
  of `mi` in the adaptor's own frame (`$invoke` replayed under that frame, `Steps.reframe`).
* **`exec_agree`**: the same for instruction sequences of the fragment (`execX`).
* **`invoke_agree`**: an adaptor function with `i32` locals whose body is in the fragment,
  stored as a function instance with the Core image of its Lime1 encoding (`XFn.toLime`), is
  invoked by `$invoke` and returns exactly the values of `XFn.run`, in the same final store.
* `reallocShim_frag`, `exportShim_frag`, **`wrap_adaptor_frag`**: every function of the adaptor
  of `wrap md` (the first FFI style: `cabi_realloc` and the export shims) is in the fragment
  (when the flat parameters fit in `2^32` locals). So `invoke_agree` applies to the whole adaptor
  of `wrap`, and with `wrap_correct_real` the wrapper's behaviour is computed by real Core 3.0
  code over a real Core 3.0 instance.

**Direction.** These are forward simulations: returned runs of the abstract adaptor are runs of
the reference semantics. Traps are not covered (the abstract adaptor traps on operands of the
wrong core type, where Core would be stuck; out-of-bounds loads trap on both sides but this is
not stated). The converse (every Core run is an abstract one) is not stated; at a deterministic
profile it would follow from determinism of Core.

**Fragment.** Not covered: `memory.copy` (Core 3.0 copies byte by byte), `if … else … end`
(an `XInstr` branch runs on the whole operand stack, a Wasm block only on its parameters), and
stores (they need a typing hypothesis on the stored value; see the open items in
`docs/projects/wasm-components.md`). So the moving `cabi_realloc` of `Styles/Realloc` and the multi-value shim
`mvShim` are not covered yet.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)

/-- **One instruction of the fragment agrees with the reference engine.** -/
theorem step_agree {i : XInstr} (hi : Frag i) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) i f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    ∃ cf' : Silmaril.Wasm.Execution.Core.Frame, cf'.module = cf.module ∧
      cf'.locals = localsOf f'.locals ∧
      Steps P host ⟨s, cf, stackCode f.stack ++ [.plain (coreOf fi i)]⟩
        ⟨s', cf', stackCode f'.stack⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.sim_step P host mi ma fi hi h he hl

/-- **A sequence of instructions of the fragment agrees with the reference engine.** -/
theorem exec_agree {is : List XInstr} (hF : ∀ i ∈ is, Frag i) {f f' : Silmaril.Wasm.Jco.Frame}
    {s s' : Store H} (h : execX (realInst H P host mi ma) is f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    ∃ cf' : Silmaril.Wasm.Execution.Core.Frame, cf'.module = cf.module ∧
      cf'.locals = localsOf f'.locals ∧
      Steps P host ⟨s, cf, stackCode f.stack ++ codeOf fi is⟩ ⟨s', cf', stackCode f'.stack⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.sim_exec P host mi ma fi is hF h he hl

/-- **An invoked adaptor function agrees with `XFn.run`.** -/
theorem invoke_agree (fn : XFn) (ty : Nat) (hF : ∀ i ∈ fn.body, Frag i) {args rs : List Flat}
    {s s' : Store H} (h : fn.run (realInst H P host mi ma) args s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts))
    (hps : args.length = ps.length) (hrts : rs.length = rts.length) :
    Steps P host (invoke s b (args.map toVal)) ⟨s', {}, vals (rs.map toVal)⟩ :=
  Silmaril.Proofs.Wasm.Jco.Real.invoke_xfn P host mi ma fi fn ty hF h hb hcode he hexp hps hrts

/-- The same for an `AFn` (the adaptor functions of `wrap`), through `AFn.toX`. -/
theorem invoke_agree_afn (fn : AFn) (ty : Nat) (hF : ∀ i ∈ fn.body, Frag (.base i))
    {args rs : List Flat} {s s' : Store H}
    (h : fn.run (realInst H P host mi ma) args s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toX.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts))
    (hps : args.length = ps.length) (hrts : rs.length = rts.length) :
    Steps P host (invoke s b (args.map toVal)) ⟨s', {}, vals (rs.map toVal)⟩ := by
  have hF' : ∀ i ∈ fn.toX.body, Frag i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact hF j hj
  rw [← AFn.toX_run] at h
  exact invoke_agree P host mi ma fi fn.toX ty hF' h hb hcode he hexp hps hrts

theorem gets_frag {n : Nat} (hn : n < 2 ^ 32) : ∀ i ∈ gets n, Frag (.base i) := by
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
  exact .localGet (by simp at hk; omega)

/-- The adaptor's `cabi_realloc` of `wrap` is in the fragment. -/
theorem reallocShim_frag (alloc : String) : ∀ i ∈ (reallocShim alloc).body, Frag (.base i) := by
  intro i hi
  simp only [reallocShim, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact .localGet (by decide)
  · exact .localGet (by decide)
  · exact .call _ _

/-- An export shim of `wrap` is in the fragment when its locals fit in `2^32`. -/
theorem exportShim_frag (md : Meta) (s : Sig) (hn : (flatParams s.params).length + 1 < 2 ^ 32) :
    ∀ i ∈ (exportShim md s).body, Frag (.base i) := by
  intro i hi
  unfold exportShim at hi
  split at hi
  · simp only [outShimBody, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (((rfl | rfl | rfl | rfl) | hg) | rfl | rfl)
    · exact .i32Const _
    · exact .i32Const _
    · exact .call _ _
    · exact .localSet (by omega)
    · exact gets_frag (by omega) i hg
    · exact .call _ _
    · exact .localGet (by omega)
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hg | rfl
    · exact gets_frag (by omega) i hg
    · exact .call _ _

/-- **Every function of the adaptor of `wrap md` is in the fragment** (when the flat parameters
of every world function fit in `2^32` locals). -/
theorem wrap_adaptor_frag (md : Meta)
    (hn : ∀ s ∈ md.world, (flatParams s.params).length + 1 < 2 ^ 32) :
    ∀ p ∈ (adaptorOf md).funcs, ∀ i ∈ p.2.body, Frag (.base i) := by
  intro p hp
  simp only [adaptorOf, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨s, hs, rfl⟩
  · exact reallocShim_frag md.alloc
  · exact exportShim_frag md s (hn s hs)

end Silmaril.Wasm.Jco.Real
