module

public import Silmaril.Compiler.Core.Verified.PrintLink.Defs
public import Silmaril.Compiler.Core.Verified.IntExprLir.Defs

/-! # The link of a `main` that writes guarded output and returns a closed expression

`PrintLink` writes a fixed list of items. The statement machine of `PrintState` chooses its
output at run time: every output carries a guard, a closed `int` expression whose value is `1`
when the output is written and `0` when it is skipped (`if` arms: exactly one arm's guards are
`1`). `link os T` is one Lir block:

* the buffer prologue of `PrintLink`;
* for each guarded output: the guard's value into `rGuard`, the current length into `rSave`, the
  output written as `PrintLink` writes it (a character, or the decimal digits of a closed
  expression computed at run time from registers), then the length set back to
  `rSave + (len - rSave) * guard`, so a skipped output leaves its bytes past the counted length,
  where the next output overwrites them;
* the control words, then the value of `T` in register 0.

Closed expressions are computed by `IntExpr.Term.ops` into register 24 and above, which keeps the
buffer registers 10–23 and the guard registers 7 and 8 (`Term.ops_exec`).

`link_sound`: when the outputs fit (`Fits`), their guards are `0` or `1` and the written ones are
defined (`Ok`), every observation of the artifact is exhaustion or the exit with `T`'s value and
the written outputs (`render`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintStateLink

open Silmaril.Machine
open Spec Backend
open PrintLink (Op Item rBase rLen rPtr rOne rZero rTen rChar0 rByte rVal rFlag rAbs rPow rDig rCtl
  outBase Buf Regs Inv Free inv_set get_set_eq get_set_ne exec_const exec_binary exec_store
  store_some toNat_ofNat_lt)
open IntExpr (Term)

/-! ## Outputs -/

/-- What a statement writes: a character, or the decimal of a closed `int` expression. -/
inductive Out where
  | char (c : Char)
  | dec (t : Term)

/-- An output and its guard. -/
abbrev GOut := Term × Out

/-- What Cerberus's `printf` appends for an output. -/
def Out.text : Out → String
  | .char c => String.singleton c
  | .dec t => toString (t.val 0)

def Out.item : Out → Item
  | .char c => .byte c.toNat.toUInt8
  | .dec t => .int (t.val 0)

/-- A decimal is of a defined expression. -/
def Out.Ok : Out → Prop
  | .char _ => True
  | .dec t => t.Ok 0

/-- At most how many bytes an output writes. -/
def Out.room : Out → Nat
  | .char _ => 1
  | .dec _ => 11

/-- The guard selects the output. -/
def On (g : Term) : Prop := g.val 0 = 1

instance (g : Term) : Decidable (On g) := by unfold On; infer_instance

/-- The selected outputs, as text. -/
def text (os : List GOut) : String :=
  String.join (os.map fun p => if On p.1 then p.2.text else "")

/-- The selected outputs, as bytes. -/
def render (os : List GOut) : List UInt8 :=
  os.flatMap fun p => if On p.1 then p.2.item.render else []

/-- Every guard is a defined `0` or `1`, every output defined. -/
def Ok (os : List GOut) : Prop :=
  ∀ p ∈ os, p.1.Ok 0 ∧ (p.1.val 0 = 0 ∨ p.1.val 0 = 1) ∧ p.2.Ok

/-- The outputs fit below the argument block, all of them written. -/
def Fits (os : List GOut) : Prop := outBase + (os.map fun p => p.2.room).sum ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase

instance (os : List GOut) : Decidable (Fits os) := by unfold Fits; infer_instance

theorem text_nil : text [] = "" := by simp [text]

theorem text_cons (p : GOut) (os : List GOut) :
    text (p :: os) = (if On p.1 then p.2.text else "") ++ text os := by
  simp [text]

theorem text_append (o₁ o₂ : List GOut) : text (o₁ ++ o₂) = text o₁ ++ text o₂ := by
  simp [text, String.join_append]

theorem render_append (o₁ o₂ : List GOut) : render (o₁ ++ o₂) = render o₁ ++ render o₂ := by
  simp [render]

theorem coreBytes_out (o : Out) : coreBytes o.text = o.item.render := by
  cases o <;> simp [Out.text, Out.item, Item.render, coreBytes]

theorem coreBytes_text (os : List GOut) : coreBytes (text os) = render os := by
  induction os with
  | nil => simp [text, render, coreBytes]
  | cons p os ih =>
    rw [text_cons]
    simp only [coreBytes, String.toList_append, List.map_append] at ih ⊢
    rw [ih]
    simp only [render, List.flatMap_cons]
    split
    · rw [← coreBytes_out]; rfl
    · rfl

/-! ## The code -/

def rGuard : Mir.Reg := 7
def rSave : Mir.Reg := 8
def rTmp : Mir.Reg := 9
def rTerm : Mir.Reg := 24

/-- A closed expression into `rTerm`. -/
def termOps (t : Term) : List Op := .const 3 (BitVec.ofInt 64 0) :: t.ops rTerm

def outOps : Out → List Op
  | .char c => PrintLink.itemOps (.byte c.toNat.toUInt8)
  | .dec t => termOps t ++ .move rVal rTerm :: PrintLink.decimalOps

/-- The length back to `rSave` unless the guard is `1`. -/
def restoreOps : List Op :=
  [.binary .sub rTmp rLen rSave, .binary .mul rTmp rTmp rGuard, .binary .add rLen rSave rTmp]

def gOps (p : GOut) : List Op :=
  termOps p.1 ++ .move rGuard rTerm :: .move rSave rLen :: (outOps p.2 ++ restoreOps)

def epilogue : List Op :=
  [.const rCtl (BitVec.ofNat 64 ctlAddr), .store .b8 rCtl 24 rLen, .store .b8 rCtl 48 rBase,
    .store .b8 rCtl 56 rLen]

/-- The whole block before the return. -/
def ops (os : List GOut) (T : Term) : List Op :=
  PrintLink.prologue ++ os.flatMap gOps ++ epilogue ++ termOps T ++ [.move 0 rTerm]

def startFunc (os : List GOut) (T : Term) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0, blocks := [⟨(ops os T).map .op, .ret [.reg 0]⟩] }

/-- The linked program of a `main` that writes `os` and returns `T`. -/
def link (os : List GOut) (T : Term) : Mir.Linked where
  prog := ⟨[startFunc os T]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

/-! ## Registers an operation keeps -/

/-- The register an operation writes. -/
def dst : Op → Option Mir.Reg
  | .const d _ => some d
  | .move d _ => some d
  | .unary _ d _ => some d
  | .binary _ d _ _ => some d
  | .load _ _ d _ _ => some d
  | .slotGet d _ => some d
  | .store .. => none
  | .slotSet .. => none

theorem exec_keep {o : Op} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory}
    {p : Lir.Frame Mir.Reg × Lir.Memory} (h : o.exec fr m = some p) {r : Mir.Reg}
    (hr : dst o ≠ some r) : p.1.get r = fr.get r := by
  cases o with
  | const d v =>
    simp only [Lir.Op.exec, Option.some.injEq] at h
    subst h
    exact get_set_ne _ (fun e => hr (by simp [dst, e])) _
  | move d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact get_set_ne _ (fun e => hr (by simp [dst, e])) _
  | unary op d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact get_set_ne _ (fun e => hr (by simp [dst, e])) _
  | binary op d a b =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, -, y, -, z, -, rfl⟩ := h
    exact get_set_ne _ (fun e => hr (by simp [dst, e])) _
  | load w e d base off =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, z, -, rfl⟩ := h
    exact get_set_ne _ (fun e => hr (by simp [dst, e])) _
  | store w base off src =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, x, -, m', -, rfl⟩ := h
    rfl
  | slotGet d n =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact get_set_ne _ (fun e => hr (by simp [dst, e])) _
  | slotSet n s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    rfl

/-- Operations that never write `r` keep it. -/
theorem execOps_keep : ∀ (os : List Op) {fr fr' : Lir.Frame Mir.Reg} {m m' : Lir.Memory},
    Lir.execOps os fr m = some (fr', m') → ∀ {r : Mir.Reg}, (os.all fun o => dst o != some r) = true →
    fr'.get r = fr.get r
  | [], fr, fr', m, m', h, r, _ => by
    simp only [Lir.execOps_nil, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | o :: os, fr, fr', m, m', h, r, hr => by
    rw [Lir.execOps_cons] at h
    cases ho : o.exec fr m with
    | none => simp [ho] at h
    | some p =>
      simp only [ho, Option.bind_some] at h
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
      rw [execOps_keep os h hr.2, exec_keep ho hr.1]

theorem split_exec {xs : List Op} {fr fr' : Lir.Frame Mir.Reg} {m m' : Lir.Memory}
    (h : Lir.execOps (xs ++ []) fr m = Lir.execOps [] fr' m') (os : List Op) :
    Lir.execOps (xs ++ os) fr m = Lir.execOps os fr' m' ∧ Lir.execOps xs fr m = some (fr', m') := by
  rw [List.append_nil, Lir.execOps_nil] at h
  exact ⟨by rw [Lir.execOps_append, h]; rfl, h⟩

theorem exec_move {d s : Mir.Reg} {x : Lir.Word} (os : List Op) {fr : Lir.Frame Mir.Reg}
    {m : Lir.Memory} (hs : fr.get s = some x) :
    Lir.execOps (.move d s :: os) fr m = Lir.execOps os (fr.set d x) m := by
  simp [Lir.execOps_cons, Lir.Op.exec, hs]

/-! ## Running the code -/

section Run

/-- A closed expression into `rTerm`, every register below it but `3` kept. -/
theorem termOps_exec (t : Term) (fr : Lir.Frame Mir.Reg) (m : Lir.Memory) (os : List Op) :
    ∃ fr' w, Lir.execOps (termOps t ++ os) fr m = Lir.execOps os fr' m ∧
      fr'.get rTerm = some w ∧ (t.Ok 0 → w = BitVec.ofInt 64 (t.val 0)) ∧
      ∀ r : Nat, r < rTerm → r ≠ 3 → fr'.get r = fr.get r := by
  obtain ⟨fr', w, hx, hw, hv, below⟩ := IntExpr.Term.ops_exec (n := 0) t rTerm (by decide)
    (fr.set 3 (BitVec.ofInt 64 0)) m (get_set_eq _ _ _)
  refine ⟨fr', w, ?_, hw, hv, fun r hr h3 => by rw [below r hr, get_set_ne _ h3]⟩
  rw [termOps, List.cons_append, exec_const, Lir.execOps_append, hx]
  rfl

theorem inv_below {size : Nat} {fr fr' : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (h : ∀ r : Nat, r < rTerm → r ≠ 3 → fr'.get r = fr.get r) :
    Inv size fr' m out :=
  ⟨⟨by rw [h rBase (by decide) (by decide)]; exact inv.regs.base,
    by rw [h rLen (by decide) (by decide)]; exact inv.regs.len,
    by rw [h rOne (by decide) (by decide)]; exact inv.regs.one,
    by rw [h rZero (by decide) (by decide)]; exact inv.regs.zero,
    by rw [h rTen (by decide) (by decide)]; exact inv.regs.ten,
    by rw [h rChar0 (by decide) (by decide)]; exact inv.regs.char0⟩, inv.buf, inv.size⟩

theorem buf_prefix {m : Lir.Memory} {out extra : List UInt8} (h : Buf m (out ++ extra)) : Buf m out := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

theorem inv_setLen {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out out' : List UInt8}
    (inv : Inv size fr m out) (buf : Buf m out') :
    Inv size (fr.set rLen (BitVec.ofNat 64 out'.length)) m out' :=
  ⟨⟨by rw [get_set_ne _ (by decide)]; exact inv.regs.base, get_set_eq _ _ _,
    by rw [get_set_ne _ (by decide)]; exact inv.regs.one,
    by rw [get_set_ne _ (by decide)]; exact inv.regs.zero,
    by rw [get_set_ne _ (by decide)]; exact inv.regs.ten,
    by rw [get_set_ne _ (by decide)]; exact inv.regs.char0⟩, buf, inv.size⟩

theorem sub_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]
  rw [show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]

/-- **The length restored by the guard.** -/
theorem restore_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out extra : List UInt8}
    (inv : Inv size fr m (out ++ extra)) (hroom : outBase + (out ++ extra).length ≤ size)
    (hs : size < 2 ^ 64) (hsave : fr.get rSave = some (BitVec.ofNat 64 out.length)) {c : Prop}
    [Decidable c] (hg : fr.get rGuard = some (BitVec.ofNat 64 (if c then 1 else 0))) (os : List Op) :
    ∃ fr', Lir.execOps (restoreOps ++ os) fr m = Lir.execOps os fr' m ∧
      Inv size fr' m (out ++ if c then extra else []) := by
  have hL : (out ++ extra).length < 2 ^ 64 := by omega
  have hle : out.length ≤ (out ++ extra).length := by simp
  let d := (out ++ extra).length - out.length
  have hsub : Lir.Binop.eval .sub (BitVec.ofNat 64 (out ++ extra).length) (BitVec.ofNat 64 out.length) =
      some (BitVec.ofNat 64 d) := by
    rw [Lir.Binop.eval, sub_ofNat hL hle]
  have hmul : Lir.Binop.eval .mul (BitVec.ofNat 64 d) (BitVec.ofNat 64 (if c then 1 else 0)) =
      some (BitVec.ofNat 64 (if c then d else 0)) := by
    by_cases hc : c <;> simp [Lir.Binop.eval, hc]
  have hlen : (out ++ if c then extra else []).length = out.length + (if c then d else 0) := by
    by_cases hc : c <;> simp [hc, d]
  have hadd : Lir.Binop.eval .add (BitVec.ofNat 64 out.length) (BitVec.ofNat 64 (if c then d else 0)) =
      some (BitVec.ofNat 64 (out ++ if c then extra else []).length) := by
    rw [PrintLink.add_ofNat, hlen]
  let fr1 := fr.set rTmp (BitVec.ofNat 64 d)
  let fr2 := fr1.set rTmp (BitVec.ofNat 64 (if c then d else 0))
  have inv2 : Inv size fr2 m (out ++ extra) := inv_set (inv_set inv (by decide) _) (by decide) _
  have buf : Buf m (out ++ if c then extra else []) := by
    by_cases hc : c
    · simpa [hc] using inv.buf
    · simpa [hc] using buf_prefix inv.buf
  refine ⟨fr2.set rLen (BitVec.ofNat 64 (out ++ if c then extra else []).length), ?_,
    inv_setLen inv2 buf⟩
  show Lir.execOps (.binary .sub rTmp rLen rSave :: .binary .mul rTmp rTmp rGuard ::
    .binary .add rLen rSave rTmp :: os) fr m = _
  rw [exec_binary _ inv.regs.len hsave hsub,
    exec_binary _ (get_set_eq _ _ _) (by rw [get_set_ne _ (by decide)]; exact hg) hmul,
    exec_binary _ (by rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact hsave)
      (get_set_eq _ _ _) hadd]

theorem decimalOps_keep7 : (PrintLink.decimalOps.all fun o => dst o != some rGuard) = true := by
  decide

theorem decimalOps_keep8 : (PrintLink.decimalOps.all fun o => dst o != some rSave) = true := by
  decide

/-- **Writing one output.** -/
theorem outOps_exec {size : Nat} (hs : size < 2 ^ 64) {o : Out} (ok : o.Ok) {fr : Lir.Frame Mir.Reg}
    {m : Lir.Memory} {out : List UInt8} (inv : Inv size fr m out)
    (room : outBase + out.length + o.room ≤ size) (os : List Op) :
    ∃ fr' m', Lir.execOps (outOps o ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ o.item.render) ∧ fr'.get rSave = fr.get rSave ∧
      fr'.get rGuard = fr.get rGuard ∧ (out ++ o.item.render).length ≤ out.length + o.room := by
  cases o with
  | char c =>
    obtain ⟨fr', m', hx, inv'⟩ := PrintLink.byte_exec inv (by simpa [Out.room] using room) hs
      c.toNat.toUInt8 []
    obtain ⟨hx', hx0⟩ := split_exec hx os
    have keep : ∀ r, r = rSave ∨ r = rGuard → fr'.get r = fr.get r := by
      intro r hr
      refine execOps_keep _ hx0 ?_
      rcases hr with rfl | rfl <;>
        simp [PrintLink.itemOps, PrintLink.emit, dst, rSave, rGuard, rByte, rPtr, rLen]
    exact ⟨fr', m', hx', inv', keep _ (.inl rfl), keep _ (.inr rfl),
      by simp [Out.item, Item.render, Out.room]⟩
  | dec t =>
    have okt : t.Ok 0 := ok
    have hint := IntExpr.Term.ok_int (n := 0) (by constructor <;> omega) t okt
    have hn : (t.val 0).natAbs < 10 ^ 10 := by
      obtain ⟨h1, h2⟩ := hint
      omega
    obtain ⟨fr1, w, hx1, hw, hv, below⟩ := termOps_exec t fr m (.move rVal rTerm :: PrintLink.decimalOps ++ os)
    have inv1 := inv_below inv below
    have inv2 := inv_set inv1 (r := rVal) (by decide) w
    rw [hv okt] at hw inv2
    obtain ⟨fr', m', hx, inv'⟩ := PrintLink.decimal_exec inv2 (by simpa [Out.room] using room) hs hn
      (get_set_eq _ _ _) []
    obtain ⟨hx', hx0⟩ := split_exec hx os
    refine ⟨fr', m', ?_, inv', ?_, ?_, ?_⟩
    · rw [outOps, List.append_assoc, hx1, List.cons_append, exec_move _ hw]
      exact hx'
    · rw [execOps_keep _ hx0 decimalOps_keep8, get_set_ne _ (by decide), below _ (by decide) (by decide)]
    · rw [execOps_keep _ hx0 decimalOps_keep7, get_set_ne _ (by decide), below _ (by decide) (by decide)]
    · have := PrintLink.render_int_length _ hn
      simp only [Out.item, Out.room, List.length_append]
      omega

/-- **Writing one guarded output.** -/
theorem gOps_exec {size : Nat} (hs : size < 2 ^ 64) {p : GOut} (okg : p.1.Ok 0)
    (h01 : p.1.val 0 = 0 ∨ p.1.val 0 = 1) (oko : p.2.Ok) {fr : Lir.Frame Mir.Reg} {m : Lir.Memory}
    {out : List UInt8} (inv : Inv size fr m out) (room : outBase + out.length + p.2.room ≤ size)
    (os : List Op) :
    ∃ fr' m', Lir.execOps (gOps p ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ if On p.1 then p.2.item.render else []) ∧
      (out ++ if On p.1 then p.2.item.render else []).length ≤ out.length + p.2.room := by
  obtain ⟨g, o⟩ := p
  obtain ⟨fr1, w, hx1, hw, hv, below⟩ := termOps_exec g fr m
    (.move rGuard rTerm :: .move rSave rLen :: (outOps o ++ (restoreOps ++ os)))
  have inv1 := inv_below inv below
  rw [hv okg] at hw
  let fr2 := fr1.set rGuard (BitVec.ofInt 64 (g.val 0))
  let fr3 := fr2.set rSave (BitVec.ofNat 64 out.length)
  have inv3 : Inv size fr3 m out := inv_set (inv_set inv1 (by decide) _) (by decide) _
  obtain ⟨fr4, m4, hx4, inv4, ks, kg, hlen4⟩ := outOps_exec hs oko inv3 room (restoreOps ++ os)
  have hg : fr4.get rGuard = some (BitVec.ofNat 64 (if On g then 1 else 0)) := by
    rw [kg, get_set_ne _ (by decide), get_set_eq]
    rcases h01 with h | h <;> simp [On, h]
  have hsv : fr4.get rSave = some (BitVec.ofNat 64 out.length) := by rw [ks, get_set_eq]
  have hroom4 : outBase + (out ++ o.item.render).length ≤ size := by
    dsimp only at hlen4 room; omega
  obtain ⟨fr5, hx5, inv5⟩ := restore_exec inv4 hroom4 hs hsv hg os
  refine ⟨fr5, m4, ?_, inv5, ?_⟩
  · show Lir.execOps (termOps g ++ (.move rGuard rTerm :: .move rSave rLen ::
      (outOps o ++ restoreOps)) ++ os) fr m = _
    rw [List.append_assoc, List.cons_append, List.cons_append, List.append_assoc, hx1,
      exec_move _ hw, exec_move _ (by rw [get_set_ne _ (by decide)]; exact inv1.regs.len), hx4, hx5]
  · simp only [List.length_append] at hlen4 ⊢
    split <;> simp; omega

theorem render_length : ∀ (os : List GOut), Ok os →
    (render os).length ≤ (os.map fun p => p.2.room).sum
  | [], _ => by simp [render]
  | p :: os, h => by
    have ih := render_length os (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h1 : (if On p.1 then p.2.item.render else []).length ≤ p.2.room := by
      split
      · obtain ⟨-, -, ok⟩ := h p List.mem_cons_self
        cases hp : p.2 with
        | char c => simp [Out.item, Item.render, Out.room]
        | dec t =>
          rw [hp] at ok
          have hint := IntExpr.Term.ok_int (n := 0) (by constructor <;> omega) t ok
          have hn : (t.val 0).natAbs < 10 ^ 10 := by obtain ⟨h1, h2⟩ := hint; omega
          exact PrintLink.render_int_length _ hn
      · simp
    simp only [render, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- **Writing the guarded outputs.** -/
theorem gitems_exec {size : Nat} (hs : size < 2 ^ 64) :
    ∀ (os : List GOut), Ok os → ∀ {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8},
    Inv size fr m out → outBase + out.length + (os.map fun p => p.2.room).sum ≤ size →
    ∀ (rest : List Op), ∃ fr' m', Lir.execOps (os.flatMap gOps ++ rest) fr m =
      Lir.execOps rest fr' m' ∧ Inv size fr' m' (out ++ render os)
  | [], _, fr, m, out, inv, _, rest => ⟨fr, m, rfl, by simpa [render] using inv⟩
  | p :: os, ok, fr, m, out, inv, room, rest => by
    obtain ⟨okg, h01, oko⟩ := ok p List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at room
    obtain ⟨fr1, m1, hx1, inv1, hlen1⟩ := gOps_exec hs okg h01 oko inv (by omega)
      (os.flatMap gOps ++ rest)
    obtain ⟨fr2, m2, hx2, inv2⟩ := gitems_exec hs os (fun q hq => ok q (List.mem_cons_of_mem _ hq))
      inv1 (by omega) rest
    refine ⟨fr2, m2, ?_, by simpa [render, List.append_assoc] using inv2⟩
    rw [List.flatMap_cons, List.append_assoc, hx1, hx2]

end Run

/-! ## The block and the observation -/

section Observe

open PrintLink (memWord_store memWord_outside store_bytes_outside artifact_memSize)

/-- The whole block, from any frame: the output written, control words 3 and 6 naming it, the
value of `T` in register 0. -/
theorem ops_exec {os : List GOut} {T : Term} (ok : Ok os) (okT : T.Ok 0) (fits : Fits os)
    (fr0 : Lir.Frame Mir.Reg) (m0 : Lir.Memory) (hsize : m0.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ fr m, Lir.execOps (ops os T) fr0 m0 = some (fr, m) ∧
      fr.get 0 = some (BitVec.ofInt 64 (T.val 0)) ∧
      memWord m (ctlAddr + 24) = (render os).length ∧ memWord m (ctlAddr + 48) = outBase ∧
      Buf m (render os) ∧ m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  have hroom := fits
  have hs : Silmaril.Compile.Forks.CoreComp.Target.memSize < 2 ^ 64 := by decide
  have hab : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
  let fin : List Op := termOps T ++ [.move 0 rTerm]
  obtain ⟨fr1, hx1, inv1⟩ := PrintLink.prologue_exec fr0 m0 (os.flatMap gOps ++ (epilogue ++ fin))
  rw [hsize] at inv1
  obtain ⟨fr2, m2, hx2, inv2⟩ := gitems_exec hs os ok inv1 (by simp [Fits] at hroom ⊢; omega)
    (epilogue ++ fin)
  simp only [List.nil_append] at inv2
  have hlen := render_length os ok
  let L := (render os).length
  have hL : L < 2 ^ 64 := by simp [Fits] at hroom; omega
  let fr3 := fr2.set rCtl (BitVec.ofNat 64 ctlAddr)
  have hctl : fr3.get rCtl = some (BitVec.ofNat 64 ctlAddr) := get_set_eq _ _ _
  have hlen3 : fr3.get rLen = some (BitVec.ofNat 64 L) := by
    rw [get_set_ne _ (by decide)]; exact inv2.regs.len
  have hbase3 : fr3.get rBase = some (BitVec.ofNat 64 outBase) := by
    rw [get_set_ne _ (by decide)]; exact inv2.regs.base
  have hc : (BitVec.ofNat 64 ctlAddr).toNat = ctlAddr := by decide
  have hsz2 := inv2.size
  let m3 : Lir.Memory := ⟨m2.size, Lir.writeLE m2.bytes (ctlAddr + 24) 8 (BitVec.ofNat 64 L)⟩
  have hst3 : m2.store .b8 ((BitVec.ofNat 64 ctlAddr).toNat + 24) (BitVec.ofNat 64 L) = some m3 := by
    rw [hc, store_some (by simp [Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  let m4 : Lir.Memory := ⟨m3.size, Lir.writeLE m3.bytes (ctlAddr + 48) 8 (BitVec.ofNat 64 outBase)⟩
  have hst4 : m3.store .b8 ((BitVec.ofNat 64 ctlAddr).toNat + 48) (BitVec.ofNat 64 outBase) = some m4 := by
    rw [hc, store_some (by simp [m3, Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  let m5 : Lir.Memory := ⟨m4.size, Lir.writeLE m4.bytes (ctlAddr + 56) 8 (BitVec.ofNat 64 L)⟩
  have hst5 : m4.store .b8 ((BitVec.ofNat 64 ctlAddr).toNat + 56) (BitVec.ofNat 64 L) = some m5 := by
    rw [hc, store_some (by simp [m4, m3, Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  rw [hc] at hst3 hst4 hst5
  obtain ⟨fr6, w, hx6, hw, hv, -⟩ := termOps_exec T fr3 m5 [.move 0 rTerm]
  rw [hv okT] at hw
  refine ⟨fr6.set 0 (BitVec.ofInt 64 (T.val 0)), m5, ?_, get_set_eq _ _ _, ?_, ?_, ?_,
    by simp [m5, m4, m3, hsz2]⟩
  · rw [ops, List.append_assoc, List.append_assoc, List.append_assoc, hx1, hx2]
    show Lir.execOps (.const rCtl (BitVec.ofNat 64 ctlAddr) :: .store .b8 rCtl 24 rLen ::
      .store .b8 rCtl 48 rBase :: .store .b8 rCtl 56 rLen :: (termOps T ++ [.move 0 rTerm])) fr2 m2 = _
    rw [exec_const, exec_store _ hctl hlen3 (by rw [hc]; exact hst3),
      exec_store _ hctl hbase3 (by rw [hc]; exact hst4),
      exec_store _ hctl hlen3 (by rw [hc]; exact hst5), hx6, exec_move _ hw]
    rfl
  · rw [memWord_outside hst5 (by left; decide), memWord_outside hst4 (by left; decide),
      memWord_store hst3, toNat_ofNat_lt hL]
  · rw [memWord_outside hst5 (by left; decide), memWord_store hst4, toNat_ofNat_lt (by decide)]
  · intro i hi
    rw [store_bytes_outside hst5 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega),
      store_bytes_outside hst4 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega),
      store_bytes_outside hst3 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega)]
    exact inv2.buf i hi

/-- The output buffer of the final memory is `bs`. -/
theorem stdout_eq {m : Lir.Memory} {bs : List UInt8}
    (h24 : memWord m (ctlAddr + 24) = bs.length) (h48 : memWord m (ctlAddr + 48) = outBase)
    (hbuf : Buf m bs) (hroom : outBase + bs.length ≤ m.size)
    {out : List UInt8} (ho : StdoutOf m out) : out = bs := by
  apply ho
  simp only [memStdout?, h24, h48, hroom, ↓reduceIte, Option.some.injEq]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_ofFn, Fin.val_cast]
  rw [hbuf i h2]
  simp [Nat.toUInt8]

theorem link_funcs (os : List GOut) (T : Term) :
    (link os T).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The Lir run of `__ccomp_start` returns `T`'s value with the output written. -/
theorem link_returns {os : List GOut} {T : Term} (ok : Ok os) (okT : T.Ok 0) (fits : Fits os)
    (argc argv : Lir.Word) (mem : Lir.Memory) (hsize : mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ s m, (link os T).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link os T).prog s (.returned [BitVec.ofInt 64 (T.val 0)] m) ∧
      memWord m (ctlAddr + 24) = (render os).length ∧ memWord m (ctlAddr + 48) = outBase ∧
      Buf m (render os) ∧ m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  obtain ⟨fr, m, hx, hw, h24, h48, hbuf, hm⟩ :=
    ops_exec ok okT fits ((Lir.Frame.empty.set 1 argc).set 2 argv) mem hsize
  refine ⟨⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩, m, rfl, ?_, h24, h48, hbuf, hm⟩
  have hb : (link os T).prog.block? 0 0 = some ⟨(ops os T).map .op, .ret [.reg 0]⟩ := rfl
  have steps := Lir.steps_execOps (p := (link os T).prog) (os := ops os T)
    (s := ⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  refine ⟨_, steps, ?_⟩
  have hf : (link os T).prog.fetch ⟨0, 0, (ops os T).length⟩ = some (.term (.ret [.reg 0])) :=
    Lir.Prog.fetch_eq_term (pt := ⟨0, 0, (ops os T).length⟩) hb (by simp)
  have hr' : fr.regs 0 = some (BitVec.ofInt 64 (T.val 0)) := hw
  simp [Lir.step, hf, Lir.Frame.readAll, Lir.Frame.read, hr']

/-- **The guarded output link is correct.** Every observation of the loaded artifact of
`link os T` is exhaustion or the exit with `T`'s value after writing the selected outputs. -/
theorem link_sound {os : List GOut} {T : Term} (ok : Ok os) (okT : T.Ok 0) (fits : Fits os)
    {a : Artifact} (h : artifactOf (link os T) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit ((BitVec.ofInt 64 (T.val 0)).toNat % 256) (render os) := by
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  have hsize : (a.lmem args).size = Silmaril.Compile.Forks.CoreComp.Target.memSize := artifact_memSize h
  obtain ⟨s', m, hs', hret, h24, h48, hbuf, hm⟩ := link_returns ok okT fits
    (BitVec.ofNat 64 args.length) (BitVec.ofNat 64 a.argBase) (a.lmem args) hsize
  rw [hs] at hs'
  cases hs'
  have hroom : outBase + (render os).length ≤ m.size := by
    have := render_length os ok
    have := fits
    have : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
    simp only [Fits] at *
    omega
  rcases ho with ho | hstuck | ⟨b, hb', hobs⟩
  · exact .inl ho
  · cases Lir.Behaves.unique hstuck hret
  · right
    cases Lir.Behaves.unique hb' hret
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    rw [hk _ rfl, stdout_eq h24 h48 hbuf hroom hout]

end Observe

end Silmaril.Compile.Core.Verified.PrintStateLink
