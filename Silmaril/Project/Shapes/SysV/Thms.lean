module

public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.Project.Shapes.X86.Thms
public import Silmaril.X86.FnContract.Thms
public import Silmaril.X86.Link.Blob.Thms
public import Silmaril.X86.Bir9.Defs

/-! # Standard problem shapes: System V functions (theorems)

* `Meaning.Refines.refl`, `Meaning.Refines.trans`: refinement of meanings is a preorder.
* `sysvSpec_sub`: a refinement of meanings gives a refinement of the System V contracts
  (`FnContract.Spec.Sub`), from the implementing meaning to the refined one.
* **`Implements.of_refines`**: a placed function that implements `lo` implements every `hi`
  that `lo` refines (and that is safe somewhere). This is the composition step used by
  `Silmaril.Project.Shapes.C.CompilesTo.of_lift`; `Lifts.implements_of_refines` is it for a lift.
* `Implements.abiFn`: an `Implements` row is a row of `silmaril.shapes.x86.abi_function` for its
  System V contract, on a model whose views are the open state's (the standard ones).
* `Implements.not_of_never_safe`: a source that is never safe has no `Implements` row.
* `ObjectFn.of_blob`: a row of `elf.object_fn` from a `Blob` certificate of the file and one run
  of the kernel-fast object reader.
* `bir9`: Bir9 blocks (`Silmaril.X86.Bir9.Block`, the public symbolic block IR) as an `Ir` of
  leaf functions.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.SysV

open Silmaril.X86 (MState Word Byte FnContract)
open Silmaril.X86.SystemV.CApi (Signature Scalar Arguments ReturnValue)

variable {sig : Signature}

/-! ## Refinement of meanings -/

theorem Meaning.Refines.refl {m : Meaning sig} (h : ∀ a, m.Safe a → ∃ r, m.Returns a r) :
    m.Refines m :=
  ⟨fun _ hs => hs, h, fun _ _ _ hr => hr⟩

theorem Meaning.Refines.trans {a b c : Meaning sig} (h₁ : a.Refines b) (h₂ : b.Refines c) :
    a.Refines c :=
  ⟨fun x hc => h₁.safe x (h₂.safe x hc), fun x hc => h₁.returns x (h₂.safe x hc),
    fun x r hc hr => h₂.sound x r hc (h₁.sound x r (h₂.safe x hc) hr)⟩

/-- **A refinement of meanings is a refinement of the System V contracts**: the contract against
`lo` is a sub-spec of the contract against `hi` (a weaker entry, the same footprint, a stronger
postcondition under `hi`'s entry). -/
theorem sysvSpec_sub {p : Placement} {frame : Nat} {lo hi : Meaning sig} (h : lo.Refines hi) :
    (sysvSpec p sig frame lo).Sub (sysvSpec p sig frame hi) where
  entry _ := fun ⟨a, he, hs⟩ => ⟨a, he, h.safe a hs⟩
  footprint _ _ _ hf := hf
  post _ _ _ hpost a ha hs :=
    let ⟨r, hr, hres⟩ := hpost a ha (h.safe a hs)
    ⟨r, h.sound a r hs hr, hres⟩

/-- Strict (first-return) correctness is monotone along `Spec.Sub`. -/
theorem strict_mono {M : Model} {S T : FnContract.Spec MState} (h : ContractStrict M S)
    (hs : S.Sub T) : ContractStrict M T := fun s hl ha he =>
  let ⟨t, hrun, hres⟩ := h s hl ha (hs.entry s he)
  ⟨t, hrun, ⟨hres.silent, hres.abi, hres.frame.mono (hs.footprint s · he), hs.post s t he hres.post⟩⟩

/-! ## Composition -/

/-- **A placed function that implements `lo` implements every `hi` that `lo` refines.** -/
theorem Implements.of_refines {M : Model} {p : Placement} {frame : Nat} {lo hi : Meaning sig}
    (h : Implements M p sig frame lo) (hr : lo.Refines hi) (hi_inh : hi.Inhabited) :
    Implements M p sig frame hi :=
  ⟨h.1, hi_inh, strict_mono h.2.2 (sysvSpec_sub hr)⟩

/-- A lift implements its IR function. -/
theorem Lifts.implements {M : Model} {p : Placement} {frame : Nat} {I : Ir} {f : I.Fn}
    (h : Lifts M p frame I f) : Implements M p (I.sig f) frame (I.meaning f) := h.1

/-- **A lift and a refinement of the IR function give an implementation.** -/
theorem Lifts.implements_of_refines {M : Model} {p : Placement} {frame : Nat} {I : Ir}
    {f : I.Fn} {hi : Meaning (I.sig f)} (h : Lifts M p frame I f)
    (hr : (I.meaning f).Refines hi) (hi_inh : hi.Inhabited) :
    Implements M p (I.sig f) frame hi :=
  h.implements.of_refines hr hi_inh

/-! ## Relation to the x86 function shapes -/

/-- The System V contract against `spec` is about the function placed by `p`. -/
theorem entersAt_sysvSpec {M : Model} (hmem : ∀ s, M.mem s = s.memory)
    (hcore : ∀ s, M.core s = s.core) {p : Placement} {frame : Nat} {spec : Meaning sig} :
    EntersAt M p (sysvSpec p sig frame spec) := fun s ⟨_, he, _⟩ => by
  rw [hmem, hcore]; exact he.entered

/-- **An `Implements` row is an `abi_function` row** for its System V contract, on a model
whose views are the open state's (`Open.isa`, `Open9.isa`, `Str9.isa`: `rfl`). -/
theorem Implements.abiFn {M : Model} (hmem : ∀ s, M.mem s = s.memory)
    (hcore : ∀ s, M.core s = s.core) {p : Placement} {frame : Nat} {spec : Meaning sig}
    (h : Implements M p sig frame spec) : AbiFn M p (sysvSpec p sig frame spec) := by
  obtain ⟨hen, ⟨a, ha⟩, hc⟩ := h
  obtain ⟨m, hl, habi, hce⟩ := hen a
  refine ⟨entersAt_sysvSpec hmem hcore, ⟨m, hl, ?_, a, hce, ha⟩, hc.contract⟩
  rw [hmem, hcore]; exact habi

/-- **A source that is never safe has no `Implements` row.** -/
theorem Implements.not_of_never_safe {M : Model} {p : Placement} {frame : Nat}
    {spec : Meaning sig} (h : ∀ a, ¬ spec.Safe a) : ¬ Implements M p sig frame spec :=
  fun ⟨_, ⟨a, ha⟩, _⟩ => h a ha

/-! ## The bytes of an object file -/

/-- The object-code check on a `Blob`, with the kernel-fast reader `Blob.readObjectN`. -/
def objectCodeN (B : Silmaril.X86.Link.Blob) (fn : String) (off : Nat) (code : List Byte) :
    Bool :=
  match Silmaril.X86.Link.Blob.readObjectN B.n B.len with
  | some o => objectCode o fn off code
  | none => false

/-- **A row of `elf.object_fn`** from a certificate that the file is the `Blob` literal `B`
(`Silmaril.Project.Shapes.blob_of_decode`) and one run of the kernel-fast reader. -/
theorem ObjectFn.of_blob {V : Type} {obj : Value V} {B : Silmaril.X86.Link.Blob} {fn : String}
    {code : List Byte} (off : Nat)
    (hB : Silmaril.X86.Link.Blob.ofBytes (Silmaril.Project.Formats.elfBytes obj.bytes) = B)
    (h : objectCodeN B fn off code = true) : ObjectFn obj fn code := by
  have hb : Silmaril.Project.Formats.elfBytes obj.bytes = B.bytes := by
    rw [← hB, Silmaril.X86.Link.Blob.bytes_ofBytes]
  unfold objectCodeN at h
  split at h
  · rename_i o ho
    refine ⟨o, off, ?_, h⟩
    rw [hb, Silmaril.X86.Link.Blob.bytes, Silmaril.X86.Link.Blob.readObject_bytesOf, ho]
  · exact absurd h (by simp)

/-! ## Bir9 blocks as an IR -/

/-- **A Bir9 leaf function**: a C signature, one block (`Silmaril.X86.Bir9.Block`) whose final
`rip` is the return, and the stack bytes below the entry `rsp` it may use. -/
structure Bir9Fn where
  sig : Signature
  block : Silmaril.X86.Bir9.Block
  frame : Nat

/-- The machine states a Bir9 leaf function is entered in with arguments `a`: the System V
entry obligations, the arguments in their registers and stack slots, and the frame and return
address readable and writable. -/
structure Bir9Fn.Entry (f : Bir9Fn) (a : Arguments f.sig.arguments) (m : MState) : Prop where
  abi : FnContract.AbiEntry m.core m.memory
  args : Silmaril.X86.SystemV.ArgumentsAt m a 0
  room : f.frame ≤ rspOf m
  read : m.memory.Permitted .read (rspOf m - f.frame) (f.frame + 8)
  write : m.memory.Permitted .write (rspOf m - f.frame) (f.frame + 8)

/-- **Bir9 leaf functions as an IR.** Safe on `a`: the block runs to completion (no fault) from
every entry state with `a` and any XMM state. Returns `r`: from some entry state the block
completes with the result `r` in `rax`. -/
def bir9 : Ir where
  Fn := Bir9Fn
  sig := Bir9Fn.sig
  meaning f :=
    { Safe := fun a => ∀ (m : MState) (x : Silmaril.X86.Bir9.XState), f.Entry a m →
        x.core = m.core → ∃ s mem, f.block.run x m.memory = .ok s mem
      Returns := fun a r => ∃ (m : MState) (x : Silmaril.X86.Bir9.XState) (s : Silmaril.X86.Bir9.XState)
        (mem : Silmaril.Process.Memory), f.Entry a m ∧
        x.core = m.core ∧ f.block.run x m.memory = .ok s mem ∧
        Silmaril.X86.SystemV.ResultAt ⟨s.core, mem⟩ f.sig.result r }

end Silmaril.Project.Shapes.SysV

end
