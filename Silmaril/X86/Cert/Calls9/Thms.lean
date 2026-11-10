module

public import Silmaril.X86.Cert.Kinds.Thms
public import Silmaril.X86.Open9.Thms

/-!
# Call certificates on the open machine over `Ext9`

`BlockCert.CallCert` yields `Spec.Total Open.isa`, with callees that are
`FnContract Open.isa`. The generic certificate (`Cert I K`, `BlockKind.call`) is already
generic in the machine; this module adds a call-block kind on `Open9`, whose callees may be
`Open9` contracts (an `Ext9` function, or a function with a jump table).

* `BlockKind.map K hstep hcore hmem hlive`: **a block kind transported to a machine `J` on the
  same states** whose core and memory are `I`'s and whose steps include `I`'s. Its blocks, check
  and WP are `K`'s; soundness is `K.sound` followed by `runsIn_map`.
* `Kinds.store9`: the writing Bir9 listings of `Kinds.store`, on `Open9.isa`.
* **`Kinds.calls9 : BlockKind Open9.isa`**: `Ext9` block code (`Kinds.ext9`), writing Bir9
  listings (`store9`), and call blocks `call store9` whose callee is any `Callee Open9.isa`.
* `Callee.ofOpen`: an `Open.isa` contract as an `Open9` callee (`FnContract.toOpen9`).
* `CallCert.toCert9`, `checked_toCert9`, `vc_toCert9`, **`CallCert.total9`**: every
  `CallCert` is a `Cert Open9.isa calls9` (its callees through `Callee.ofOpen`), so its VCs give
  `Spec.Total Open9.isa` through the generic `Cert.total`.

Not done: no certificate here calls an `Open9`-only callee (the kind admits one).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded)
open FnContract (RunsIn InCode AbiEntry Spec runsIn_map)
open BlockCert (CallCert CBlk CKind listingAtW)

namespace BlockKind

variable {σ : Type} {I J : Isa σ}

/-- **A block kind transported along a refinement of machines on the same states.** -/
def map (K : BlockKind I) (hstep : ∀ {s s' : σ}, I.step s = some s' → J.step s = some s')
    (hcore : J.core = I.core) (hmem : J.mem = I.mem) (hlive : ∀ s, J.live s → I.live s) :
    BlockKind J where
  B := K.B
  check := K.check
  WP := K.WP
  Admits := K.Admits
  admits_top := K.admits_top
  sound {_ _ _ _ _ s _} hok hlv hl hrip hadm hwp := by
    rw [hmem] at hl
    rw [hcore] at hrip
    obtain ⟨t, hr, hq⟩ := K.sound hok (hlive s hlv) hl hrip hadm hwp
    exact ⟨t, runsIn_map hstep hr, hq⟩

/-- An `Open.isa` contract as an `Open9` callee. -/
def Callee.ofOpen (C : FnContract Open.isa) : Callee Open9.isa :=
  Callee.ofContract C.toOpen9

end BlockKind

namespace Cert.Kinds

/-- Writing Bir9 listings, on the open machine over `Ext9`. -/
def store9 : BlockKind Open9.isa :=
  store.map (fun h => Open9.step_of_open h) rfl rfl fun _ _ => trivial

/-- **`Ext9` block code, writing Bir9 listings and call blocks with `Open9` callees**, on the
open machine over `Ext9`. -/
def calls9 : BlockKind Open9.isa :=
  BlockKind.sum (BlockKind.sum ext9 store9) (BlockKind.call store9)

end Cert.Kinds

open Cert.Kinds

/-! ## `BlockCert.CallCert` on `Open9` -/

namespace BlockCert.CallCert

/-- A call-certificate block as a `calls9` block. -/
def blockOf9 (b : CBlk) : CBlock calls9 :=
  match b.kind with
  | .plain L => ⟨b.off, .inl (.inr L)⟩
  | .call rel C => ⟨b.off, .inr ([(.ext (.call rel), 5)], BlockKind.Callee.ofOpen C)⟩

@[simp] theorem blockOf9_off (b : CBlk) : (blockOf9 b).off = b.off := by
  unfold blockOf9; split <;> rfl

/-- A certificate with contract calls as a generic certificate on `Open9`. -/
def toCert9 (F : CallCert) : Cert Open9.isa calls9 :=
  ⟨F.code, F.base, F.blocks.map blockOf9, F.ann, F.measure⟩

theorem mem_toCert9 {F : CallCert} {b : CBlk} (hb : b ∈ F.blocks) :
    blockOf9 b ∈ F.toCert9.blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem check_blockOf9 (code : List Byte) (b : CBlk) :
    calls9.check code (blockOf9 b).off (blockOf9 b).blk = listingAtW code b.off b.kind.listing := by
  obtain ⟨off, k⟩ := b
  cases k <;> rfl

theorem checked_toCert9 {F : CallCert} (hc : F.checked = true) : F.toCert9.checked = true := by
  simp only [Cert.checked, toCert9, List.all_map, Function.comp_def, check_blockOf9]
  exact hc

theorem next_toCert9 {F : CallCert} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat}
    (h : F.NextC Q m0 μ m') : F.toCert9.Next Q m0 μ m' := by
  rcases h with hq | ⟨b', hb', hrip', hl', ha', hlt⟩
  · exact .inl hq
  · exact .inr ⟨_, mem_toCert9 hb', by rw [blockOf9_off]; exact hrip', hl',
      by rw [blockOf9_off]; exact ha', by rw [blockOf9_off]; exact hlt⟩

/-- The result of an `Open9` call is the same notion as on the open machine. -/
theorem result_open9 {S : Spec MState} {s t : MState} (h : S.Result Open9.isa s t) :
    S.Result Open.isa s t :=
  ⟨h.silent, h.abi, h.frame, h.post⟩

theorem result_fun_open9 {S : Spec MState} :
    (fun m0 t => S.Result Open9.isa m0 t) = fun m0 t => S.Result Open.isa m0 t := by
  funext s t
  exact propext ⟨result_open9, fun h => ⟨h.silent, h.abi, h.frame, h.post⟩⟩

theorem vc_toCert9 {F : CallCert} {Q : MState → MState → Prop} (hvc : F.VC Q) :
    F.toCert9.VC Q := by
  intro b hb s0 m ha _ hrip hl
  obtain ⟨⟨off, k⟩, hb0, rfl⟩ := List.mem_map.mp hb
  have hv := hvc _ hb0
  cases k with
  | plain L =>
    obtain ⟨m', hr, hn⟩ := hv s0 m ha hrip hl
    exact ⟨m', hr, next_toCert9 hn⟩
  | call rel C =>
    obtain ⟨⟨m1, hm1⟩, hpost⟩ := hv s0 m ha hrip hl
    obtain ⟨hab, he, hres⟩ := hpost m1 hm1
    exact ⟨m1, hm1, hab, he, fun _ _ => trivial,
      fun t ht => next_toCert9 (hres t (result_open9 ht))⟩

/-- **`CallCert` on the open machine over `Ext9`**, through the generic `Cert.total` and the
`calls9` kind (callees through `Callee.ofOpen`). -/
theorem total9 {F : CallCert} (S : Spec MState) {entry : CBlk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open9.isa :=
  Cert.total (F := F.toCert9) S (mem_toCert9 hentry) (checked_toCert9 hc)
    (by rw [result_fun_open9]; exact vc_toCert9 hvc)
    (fun m hab he => by rw [blockOf9_off]; exact hpre m hab he)

end BlockCert.CallCert

end Silmaril.X86
