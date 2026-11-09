module

public import Silmaril.X86.Cert.ICall.Defs
import Silmaril.Proofs.X86.Cert.ICall

/-!
# Indirect-call blocks for the generic certificate

`BlockKind.call K` (`Cert/Thms.lean`) names its callee in the block data. An indirect call
`call *%r` / `call *d(%base)` / `call *x(%rip)` reaches whatever function the operand holds,
so the callee cannot be in the block. This module adds a block kind whose WP asks, at the
callee's entry state, for **`FnPtr Γ rip T`** (the function-pointer fact of
`Silmaril.X86.Link.Env`, at the address the call jumped to) and for **the callee requirement
`T`'s entry obligations**. The callee's correctness comes from the environment `Γ`, whose entries
are valid once and for all. The requirements, the logic and `Post` are in `Cert/ICall/Defs.lean`.

Generic part (any machine `I : Isa σ`):

* `Req.Sub.refl`, `Req.Sub.trans`, `Req.Valid.sub` (validity is monotone along `Sub`),
  `Req.valid_ofCallee`;
* `valid_of_envSafe`, `envSafe_of_valid`: with `logic I`, `Link.Env.Env.Safe` is the validity
  of Γ; `Link.Env.FnPtr (logic I) J Γ p T` is the unit-contract function-pointer fact;
* `post_runs`: from `Post`, the Γ entry's callee runs to a state in `Q`;
* **`BlockKind.icall K J Γ hΓ`**: blocks `(b, T)`, a `K`-block `b` (the call instruction)
  followed by the callee reached through `FnPtr Γ`. `hΓ : ∀ a c, Γ a c → (J Γ c).Valid I`.
  Soundness (`icall_sound`): `K.sound` to `m1`, then the Γ entry found by `FnPtr`, weakened
  along `Req.Sub`;
* `icall_of_call`: a direct-call WP is an indirect-call WP for the singleton Γ (sanity check:
  the indirect kind generalises the direct one).

On the open machine over `Ext9` (`Open9.isa`):

* `Cert.Kinds.insn9 : BlockKind Open9.isa`: **one `Ext9` instruction**, which may write memory
  and need not fall through (`call r/m64`, `jmp r/m64`, `push`, …). Check: `insn9Check`
  (`Open9.decode` at the offset); WP: `Ext9.exec` succeeds into `Q`. `Admits := BlockKind.Local`.
* `Cert.Kinds.icall9 J Γ hΓ := sum (icall insn9 J Γ hΓ) calls9`: indirect calls plus the
  `calls9` blocks (Ext9 code, writing Bir9 listings, direct calls);
  `Cert.Kinds.icallSeg9 J Γ hΓ code := sum (icall insn9 J Γ hΓ) (segCalls9 code)` adds the
  segment blocks. `Cert.ICall.calls9_icall9` lifts a `calls9` certificate unchanged
  (`Cert.inr`, checks and VC preserved).
* WP lemmas for `call r/m64` (`FF /2`): `callInd_wp` (any operand: the value `v` read by
  `readRM .q src` is the `FnPtr` target), `callInd_reg_wp` (`call *%r`: `FnPtr Γ (s.read r) T`);
  `push_abiEntry`: after the push of any return word from an aligned stack, the System V entry
  obligations;
* `icall9_totalIn`, `icall9_total`: `Cert.totalIn` / `Cert.total` at the `icall9` kind.

Tests (`Cert.ICall.Test`): the `insn9` check on one encoding of each `call r/m64` form that
compiled C code commonly uses (register, `[base+disp8]`, SIB, `[base+disp32]`, `[base]`,
RIP-relative, indexed); a two-entry method table Γ (`pairEnv`, `pairJ`, `pair_valid`,
`pair_envSafe`); the `icall9` kind and `Cert.totalIn` instantiated with it; a mutation check
(`post_wrong_pointer`). Callee-side non-vacuity with a real callee is in
`Cert/ICall/LibMini/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded)
open FnContract (RunsIn InCode AbiEntry Spec runsIn_mono runsIn_trans runsIn_live)
open Silmaril.X86.Link.Env (Env FnPtr)

namespace Cert.ICall

variable {σ : Type}

theorem Req.Sub.refl (r : Req σ) : r.Sub r :=
  ⟨FnContract.Spec.Sub.refl _, fun _ _ _ h => h⟩

theorem Req.Sub.trans {r t u : Req σ} (h₁ : r.Sub t) (h₂ : t.Sub u) : r.Sub u :=
  ⟨h₁.spec.trans h₂.spec, fun s m he h => h₂.run s m he (h₁.run s m (h₂.spec.entry s he) h)⟩

variable {I : Isa σ}

/-- A safe environment (at a positive index) has valid entries. -/
theorem valid_of_envSafe {Code : Type} {J : Env Code → Code → Req σ} {Γ : Env Code} {n : Nat}
    {ctx : Silmaril.X86.Link.Contract.Image}
    (h : Silmaril.X86.Link.Env.Env.Safe (logic I) J Γ (n + 1) ctx) :
    ∀ a c, Γ a c → (J Γ c).Valid I :=
  fun a c hc => h a c hc (Nat.succ_pos n)

/-- An environment with valid entries is safe at every index and image. -/
theorem envSafe_of_valid {Code : Type} {J : Env Code → Code → Req σ} {Γ : Env Code}
    (h : ∀ a c, Γ a c → (J Γ c).Valid I) (n : Nat) (ctx : Silmaril.X86.Link.Contract.Image) :
    Silmaril.X86.Link.Env.Env.Safe (logic I) J Γ n ctx :=
  fun a c hc _ => h a c hc

theorem Req.valid_ofCallee (c : BlockKind.Callee I) : (Req.ofCallee c).Valid I := c.totalIn

/-- From `Post`: the Γ entry's callee runs from `m1` inside `R` to a state in `Q`. -/
theorem post_runs {Code : Type} {J : Env Code → Code → Req σ} {Γ : Env Code}
    (hΓ : ∀ a c, Γ a c → (J Γ c).Valid I) {T : Req σ} {R Q : σ → Prop} {m1 : σ}
    (hlv : I.live m1) (h : Post (I := I) J Γ T R Q m1) : ∃ t, RunsIn I R m1 t ∧ Q t :=
  Silmaril.Proofs.X86.Cert.ICall.post_runs hΓ hlv h

end Cert.ICall

namespace BlockKind

open Cert.ICall

variable {σ : Type} {I : Isa σ}

/-- Soundness of an indirect-call block. -/
theorem icall_sound {Code : Type} {J : Env Code → Code → Req σ} {Γ : Env Code}
    (hΓ : ∀ a c, Γ a c → (J Γ c).Valid I) {K : BlockKind I} {code : List Byte} {base : Word}
    {o : Nat} {b : K.B} {T : Req σ} {R : σ → Prop} {s : σ} {Q : σ → Prop}
    (hok : K.check code o b = true) (hlv : I.live s) (hl : Loaded (I.mem s) base code)
    (hrip : (I.core s).rip = base + BitVec.ofNat 64 o) (hadm : K.Admits base code.length R)
    (hwp : K.WP b R s (Post (I := I) J Γ T R Q)) : ∃ t, RunsIn I R s t ∧ Q t := by
  obtain ⟨m1, hr, hp⟩ := K.sound hok hlv hl hrip hadm hwp
  obtain ⟨t, hr', hq⟩ := post_runs hΓ (runsIn_live hr hlv) hp
  exact ⟨t, runsIn_trans hr hr', hq⟩

/-- **Indirect-call blocks**: a `K`-block (the call instruction) followed by the function the
call reached, which must be a function pointer of `Γ` for the requirement `T` named in the
block. `hΓ`: every entry of `Γ` is valid. -/
def icall (K : BlockKind I) {Code : Type} (J : Env Code → Code → Req σ) (Γ : Env Code)
    (hΓ : ∀ a c, Γ a c → (J Γ c).Valid I) : BlockKind I where
  B := K.B × Req σ
  check code o b := K.check code o b.1
  WP b R s Q := K.WP b.1 R s (Post (I := I) J Γ b.2 R Q)
  Admits := K.Admits
  admits_top := K.admits_top
  sound hok hlv hl hrip hadm hwp := icall_sound hΓ hok hlv hl hrip hadm hwp

/-- **The indirect kind generalises the direct one**: a direct call's postcondition whose
callee is entered at `a` is an indirect-call postcondition for the singleton environment at
`a`, with the callee's own requirement. -/
theorem icall_of_call (c : Callee I) {a : Nat} {R Q : σ → Prop} {m1 : σ}
    (h : CallPost c R Q m1) (hrip : (I.core m1).rip.toNat = a) :
    Post (I := I) (fun _ _ => Req.ofCallee c) (single a) (Req.ofCallee c) R Q m1 :=
  ⟨⟨(), hrip, Req.Sub.refl _⟩, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem single_valid (c : Callee I) (a : Nat) :
    ∀ a' u, single a a' u → ((fun _ _ => Req.ofCallee c) (single a) u :
      Req σ).Valid I :=
  fun _ _ _ => Req.valid_ofCallee c

end BlockKind

/-! ## On the open machine over `Ext9` -/

namespace Cert.Kinds

open Cert.ICall

theorem insn9_sound {code : List Byte} {base : Word} {o : Nat} {b : Ext9.Instr × Nat}
    {R : MState → Prop} {s : MState} {Q : MState → Prop} (hok : insn9Check code o b = true)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hadm : BlockKind.Local Open9.isa base code.length R) (hwp : insn9WP b s Q) :
    ∃ t, RunsIn Open9.isa R s t ∧ Q t :=
  Silmaril.Proofs.X86.Cert.ICall.insn9_sound hok hl hrip hadm hwp

/-- **One `Ext9` instruction**, which may write memory and need not fall through (`call r/m64`,
`jmp r/m64`, `push imm`, …), on the open machine over `Ext9`. -/
def insn9 : BlockKind Open9.isa where
  B := Ext9.Instr × Nat
  check := insn9Check
  WP b _ s Q := insn9WP b s Q
  Admits := BlockKind.Local Open9.isa
  admits_top _ _ _ _ := trivial
  sound hok _ hl hrip hadm hwp := insn9_sound hok hl hrip hadm hwp

variable {Code : Type} (J : Env Code → Code → Req MState) (Γ : Env Code)
  (hΓ : ∀ a c, Γ a c → (J Γ c).Valid Open9.isa)

/-- **Indirect calls through Γ, plus `calls9`** (`Ext9` code, writing Bir9 listings, direct
calls), on the open machine over `Ext9`. -/
def icall9 : BlockKind Open9.isa :=
  BlockKind.sum (BlockKind.icall insn9 J Γ hΓ) calls9

/-- **Indirect calls through Γ, plus `segCalls9 code`** (segment blocks, `Ext9` code, writing
Bir9 listings, direct calls). -/
def icallSeg9 (code : List Byte) : BlockKind Open9.isa :=
  BlockKind.sum (BlockKind.icall insn9 J Γ hΓ) (segCalls9 code)

/-- An indirect-call block of `icall9`: the call instruction (with its length) and the
requirement `T` on the callee. -/
def icallBlk (off : Nat) (src : Ext.RM) (l : Nat) (T : Req MState) : CBlock (icall9 J Γ hΓ) :=
  ⟨off, .inl ((.new (.callInd src), l), T)⟩

end Cert.Kinds

namespace Cert.ICall

open Cert.Kinds
open Silmaril.X86.Ext (RM Stored readRM)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

variable {Code : Type} (J : Env Code → Code → Req MState) (Γ : Env Code)
  (hΓ : ∀ a c, Γ a c → (J Γ c).Valid Open9.isa)

/-- After pushing the return address `ret` from a 16-byte-aligned stack pointer whose slot is
readable, the System V entry obligations hold and the return address is `ret` (`call_abiEntry`
for any return word). -/
theorem push_abiEntry {c0 : State} {mem mem' : Memory} {target ret : Word}
    (hal : (c0.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (c0.read .rsp).toNat)
    (hr : mem.Permitted .read (c0.read .rsp - 8#64).toNat 8)
    (hs : Stored mem mem' (c0.read .rsp - 8#64).toNat (encodeWords [ret])) :
    let c : State := { c0.write .rsp (c0.read .rsp - 8#64) with rip := target }
    AbiEntry c mem' ∧ FnContract.retOf c mem' = ret :=
  Silmaril.Proofs.X86.Cert.ICall.push_abiEntry hal h8 hr hs

/-- **The WP of `call r/m64` through Γ**, for any operand `src` that `Ext9` reads as the word
`v`: `v` is a function pointer of Γ for `T`, the stack pointer is 16-byte aligned with a
readable and writable return slot, and, for the memory after the push (opaque, `Stored`), the
callee entry state meets `T`'s precondition, `T`'s run stays in `R`, and `T`'s results are in
`Q`. The callee entry state's return address is the instruction after the call. -/
theorem callInd_wp {src : RM} {l : Nat} {T : Req MState} {R Q : MState → Prop} {s : MState}
    {v : Word} (hv : readRM .q src s.core s.memory (s.core.rip + BitVec.ofNat 64 l) = some v)
    (hfp : FnPtr (logic Open9.isa) J Γ v T)
    (hal : (s.core.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (s.core.read .rsp).toNat)
    (hw : s.memory.Permitted .write (s.core.read .rsp - 8#64).toNat 8)
    (hr : s.memory.Permitted .read (s.core.read .rsp - 8#64).toNat 8)
    (hpost : ∀ mem', Stored s.memory mem' (s.core.read .rsp - 8#64).toNat
        (encodeWords [s.core.rip + BitVec.ofNat 64 l]) →
      let m1 : MState := ⟨{ s.core.write .rsp (s.core.read .rsp - 8#64) with rip := v }, mem'⟩
      FnContract.retOf m1.core m1.memory = s.core.rip + BitVec.ofNat 64 l →
      T.spec.entry m1 ∧ (∀ m, T.P m1 m → R m) ∧ ∀ t, T.spec.Result Open9.isa m1 t → Q t) :
    (BlockKind.icall insn9 J Γ hΓ).WP ((.new (.callInd src), l), T) R s Q :=
  Silmaril.Proofs.X86.Cert.ICall.callInd_wp J Γ hv hfp hal h8 hw hr hpost

/-- **`call *%r` through Γ**: the register's value is the function pointer. -/
theorem callInd_reg_wp {r : Reg} {l : Nat} {T : Req MState} {R Q : MState → Prop} {s : MState}
    (hfp : FnPtr (logic Open9.isa) J Γ (s.core.read r) T)
    (hal : (s.core.read .rsp).toNat % 16 = 0) (h8 : 8 ≤ (s.core.read .rsp).toNat)
    (hw : s.memory.Permitted .write (s.core.read .rsp - 8#64).toNat 8)
    (hr : s.memory.Permitted .read (s.core.read .rsp - 8#64).toNat 8)
    (hpost : ∀ mem', Stored s.memory mem' (s.core.read .rsp - 8#64).toNat
        (encodeWords [s.core.rip + BitVec.ofNat 64 l]) →
      let m1 : MState :=
        ⟨{ s.core.write .rsp (s.core.read .rsp - 8#64) with rip := s.core.read r }, mem'⟩
      FnContract.retOf m1.core m1.memory = s.core.rip + BitVec.ofNat 64 l →
      T.spec.entry m1 ∧ (∀ m, T.P m1 m → R m) ∧ ∀ t, T.spec.Result Open9.isa m1 t → Q t) :
    (BlockKind.icall insn9 J Γ hΓ).WP ((.new (.callInd (.reg r)), l), T) R s Q :=
  callInd_wp J Γ hΓ (src := .reg r) rfl hfp hal h8 hw hr hpost

/-- **`Cert.totalIn` at the `icall9` kind**: a checked certificate with indirect calls through a
valid Γ, whose VC holds for `R`, gives `Spec.TotalIn Open9.isa R`. -/
theorem icall9_totalIn {F : Cert Open9.isa (icall9 J Γ hΓ)} (S : Spec MState)
    {R : MState → MState → Prop} {entry : CBlock (icall9 J Γ hΓ)} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VCIn R fun s0 t => S.Result Open9.isa s0 t)
    (hadm : ∀ s, AbiEntry s.core s.memory → S.entry s →
      BlockKind.Local Open9.isa F.base F.code.length (R s))
    (hpre : ∀ s, AbiEntry s.core s.memory → S.entry s →
      Loaded s.memory F.base F.code ∧ s.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.TotalIn Open9.isa R :=
  Cert.totalIn S hentry hc hvc
    (fun s _ hab he => let h := hadm s hab he
      ⟨h, ⟨h, fun m hm => h m hm⟩, fun m hm => h m hm⟩) hpre

/-- `Cert.total` at the `icall9` kind. -/
theorem icall9_total {F : Cert Open9.isa (icall9 J Γ hΓ)} (S : Spec MState)
    {entry : CBlock (icall9 J Γ hΓ)} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun s0 t => S.Result Open9.isa s0 t)
    (hpre : ∀ s, AbiEntry s.core s.memory → S.entry s →
      Loaded s.memory F.base F.code ∧ s.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.Total Open9.isa :=
  Cert.total S hentry hc hvc hpre

/-- Every `calls9` certificate is an `icall9` certificate (with the same checks and VC). -/
theorem calls9_icall9 {F : Cert Open9.isa calls9} {Q : MState → MState → Prop}
    (hc : F.checked = true) (hvc : F.VC Q) :
    (F.inr (BlockKind.icall insn9 J Γ hΓ)).checked = true ∧
      (F.inr (BlockKind.icall insn9 J Γ hΓ)).VC Q :=
  ⟨Cert.checked_inr hc, Cert.vc_inr hvc⟩

end Cert.ICall

/-! ## Tests -/

namespace Cert.ICall.Test

open Cert.Kinds

/-- A decoded indirect call of `bytes`, with its length, if `Open9.decode` reads one. -/
def callIndOf (bytes : List Byte) : Option (Ext9.Instr × Nat) :=
  match Open9.decode bytes with
  | some (.new (.callInd src), l) => if l = bytes.length then some (.new (.callInd src), l) else none
  | _ => none

/-- The one-instruction check accepts `call *%rax` (`FF D0`). -/
theorem check_FF_D0 : insn9Check [0xFF, 0xD0] 0 (.new (.callInd (.reg .rax)), 2) = true := by
  decide

/-- Common forms of `call r/m64`, one encoding each: register (`call *%rax`, `call *%r13`),
`[base+disp8]` (`call *0x48(%rbx)`, zlib's `strm->zfree`), `[r12+disp8]` (SIB),
`[base+disp32]`, `[base]`, RIP-relative (before relocation) and indexed. Each decodes as
`callInd` with its full length, and that decode passes the `insn9` check. -/
theorem census_forms_check :
    ([[0xFF, 0xD0], [0x41, 0xFF, 0xD5], [0xFF, 0x53, 0x48], [0x41, 0xFF, 0x54, 0x24, 0x38],
      [0xFF, 0x90, 0x90, 0x00, 0x00, 0x00], [0xFF, 0x10], [0xFF, 0x15, 0x00, 0x00, 0x00, 0x00],
      [0xFF, 0x54, 0x02, 0x08]] : List (List Byte)).all (fun bs =>
        match callIndOf bs with
        | some b => insn9Check bs 0 b
        | none => false) = true := by
  decide

/-- **A two-entry method table** (the shape of a `zalloc`/`zfree` pair or a VFS table): code
`true` at `e₁` and code `false` at `e₂`, interpreted by two contracts. -/
def pairEnv (e₁ e₂ : Nat) : Env Bool := fun a c => (c = true ∧ a = e₁) ∨ (c = false ∧ a = e₂)

/-- The interpretation of the method table. -/
def pairJ (C₁ C₂ : BlockKind.Callee Open9.isa) : Env Bool → Bool → Req MState
  | _, true => Req.ofCallee C₁
  | _, false => Req.ofCallee C₂

theorem pair_valid (C₁ C₂ : BlockKind.Callee Open9.isa) (e₁ e₂ : Nat) :
    ∀ a c, pairEnv e₁ e₂ a c → (pairJ C₁ C₂ (pairEnv e₁ e₂) c).Valid Open9.isa := by
  intro a c _
  cases c
  · exact Req.valid_ofCallee C₂
  · exact Req.valid_ofCallee C₁

/-- The method table's environment is safe at every index (so it can be the Γ of
`Link.Env`'s unit composition for the certificate logic). -/
theorem pair_envSafe (C₁ C₂ : BlockKind.Callee Open9.isa) (e₁ e₂ : Nat) (n : Nat)
    (ctx : Silmaril.X86.Link.Contract.Image) :
    Silmaril.X86.Link.Env.Env.Safe (logic Open9.isa) (pairJ C₁ C₂) (pairEnv e₁ e₂) n ctx :=
  envSafe_of_valid (pair_valid C₁ C₂ e₁ e₂) n ctx

/-- The second method is a function pointer for its own requirement at `e₂`. -/
theorem pair_fnptr₂ (C₁ C₂ : BlockKind.Callee Open9.isa) (e₁ : Nat) (p : Word) :
    FnPtr (logic Open9.isa) (pairJ C₁ C₂) (pairEnv e₁ p.toNat) p (Req.ofCallee C₂) :=
  ⟨false, .inr ⟨rfl, rfl⟩, Req.Sub.refl _⟩

/-- **The kind instantiates** with a method table of two contracts, and a block
`call *0x48(%rbx)` (`FF 53 48`) passes the check inside a concrete code region. -/
example (C₁ C₂ : BlockKind.Callee Open9.isa) (e₁ e₂ : Nat) (T : Req MState) :
    (icall9 (pairJ C₁ C₂) (pairEnv e₁ e₂) (pair_valid C₁ C₂ e₁ e₂)).check
      [0x90, 0xFF, 0x53, 0x48, 0xC3] 1
      (.inl (((callIndOf [0xFF, 0x53, 0x48]).getD (.new (.callInd (.reg .rax)), 0)), T)) =
      true := by
  show insn9Check [0x90, 0xFF, 0x53, 0x48, 0xC3] 1
    ((callIndOf [0xFF, 0x53, 0x48]).getD (.new (.callInd (.reg .rax)), 0)) = true
  decide

/-- **`Cert.totalIn` instantiates** at the `icall9` kind with the method table. -/
example (C₁ C₂ : BlockKind.Callee Open9.isa) (e₁ e₂ : Nat)
    (F : Cert Open9.isa (icall9 (pairJ C₁ C₂) (pairEnv e₁ e₂) (pair_valid C₁ C₂ e₁ e₂)))
    (S : Spec MState) (R : MState → MState → Prop) (entry : CBlock _) (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VCIn R fun s0 t => S.Result Open9.isa s0 t)
    (hadm : ∀ s, AbiEntry s.core s.memory → S.entry s →
      BlockKind.Local Open9.isa F.base F.code.length (R s))
    (hpre : ∀ s, AbiEntry s.core s.memory → S.entry s →
      Loaded s.memory F.base F.code ∧ s.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off s s) :
    S.TotalIn Open9.isa R :=
  icall9_totalIn _ _ _ S hentry hc hvc hadm hpre

/-- **Mutation check**: a pointer outside Γ makes `Post` false, so the kind does check the
function pointer (here: the singleton environment at `a`, entered at another address). -/
theorem post_wrong_pointer {σ : Type} {I : Isa σ} (r : Req σ) {a : Nat} {T : Req σ}
    {R Q : σ → Prop} {m1 : σ} (hne : (I.core m1).rip.toNat ≠ a) :
    ¬ Post (I := I) (fun _ _ => r) (single a) T R Q m1 :=
  fun ⟨⟨_, hc, _⟩, _⟩ => hne hc

end Cert.ICall.Test

end Silmaril.X86
