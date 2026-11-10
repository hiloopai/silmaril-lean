module

public import Silmaril.X86.MemEvent.Defs

/-!
# Locality of `X86.Ext`: the relational closure lemmas and `ext_local`

The relation `Rel (writeSet es) m m'` between the outcomes of one executor on two memories that
agree on the read set (`Agree (readSet es) m m'`) is built goal-directed:

* reads are **rewritten**: `readRM_agree`, `readNarrow_agree`, `popWord_agree`, ... turn every
  read of `m'` into the same read of `m` (side condition: the read's span lies in the read
  set, discharged by `mev_span`). After that both outcomes branch on the same values;
* writes are **related**: `writeRM_rel`, `storeN_rel`, `pushWord_rel` give `OptRel W` for the
  write set `W` of exactly that store (side condition: `W` is the store's span, discharged by
  `mev_span`);
* the shapes (`retire`, `Option.map`, `match`, `if`) are closed by the `mev_rel` tactic.

The case split over `Ext.exec` uses `cases` on the instruction and the `RM` operands only
through `rmSpan`, so it is one tactic call per constructor.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemEvent

open Silmaril.X86 (State MState Word Reg Byte)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Ext
open Silmaril.X86.MemEvent

/-! ## Read and write sets of the builders -/

/-- The span of an `r/m` operand of `size` bytes: empty for a register. -/
def rmSpan (size : Nat) (op : RM) (s : State) (next : Word) (a : Nat) : Prop :=
  match op with
  | .reg _ => False
  | .mem m => (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + size

/-- The span of an `r/m8` operand: empty for a register. -/
def rm8Span (op : Silmaril.X86.Ext8.RM8) (s : State) (next : Word) (a : Nat) : Prop :=
  match op with
  | .reg _ => False
  | .mem m => (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + 1

/-- The span of an `xmm/m` operand of `size` bytes: empty for a register. -/
def xrmSpan (size : Nat) (op : Silmaril.X86.Sse9.XRM) (s : State) (next : Word)
    (a : Nat) : Prop :=
  match op with
  | .reg _ => False
  | .mem m => (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + size

@[simp] theorem readSet_nil (a : Nat) : readSet [] a ↔ False := by simp [readSet]
@[simp] theorem writeSet_nil (a : Nat) : writeSet [] a ↔ False := by simp [writeSet]

@[simp] theorem readSet_append (es fs : List Event) (a : Nat) :
    readSet (es ++ fs) a ↔ readSet es a ∨ readSet fs a := by
  simp only [readSet, List.mem_append]
  constructor
  · rintro ⟨e, he | he, h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, Or.inl he, h⟩
    · exact ⟨e, Or.inr he, h⟩

@[simp] theorem writeSet_append (es fs : List Event) (a : Nat) :
    writeSet (es ++ fs) a ↔ writeSet es a ∨ writeSet fs a := by
  simp only [writeSet, List.mem_append]
  constructor
  · rintro ⟨e, he | he, h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, Or.inl he, h⟩
    · exact ⟨e, Or.inr he, h⟩

@[simp] theorem readSet_singleton (e : Event) (a : Nat) :
    readSet [e] a ↔ e.kind.reads = true ∧ e.addr ≤ a ∧ a < e.addr + e.size := by
  simp [readSet, Event.Covers]

@[simp] theorem writeSet_singleton (e : Event) (a : Nat) :
    writeSet [e] a ↔ e.kind.writes = true ∧ e.addr ≤ a ∧ a < e.addr + e.size := by
  simp [writeSet, Event.Covers]

@[simp] theorem Sz_bytes_d : Sz.d.bytes = 4 := rfl
@[simp] theorem Sz_bytes_q : Sz.q.bytes = 8 := rfl
@[simp] theorem Narrow_bytes_b : Narrow.b.bytes = 1 := rfl
@[simp] theorem Narrow_bytes_w : Narrow.w.bytes = 2 := rfl

@[simp] theorem rmSpan_reg (size : Nat) (r : Reg) (s : State) (next : Word) (a : Nat) :
    rmSpan size (.reg r) s next a ↔ False := Iff.rfl

@[simp] theorem rmSpan_mem (size : Nat) (m : Mem) (s : State) (next : Word) (a : Nat) :
    rmSpan size (.mem m) s next a ↔
      (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + size := Iff.rfl

@[simp] theorem rm8Span_reg (r : Silmaril.X86.Ext8.BReg) (s : State) (next : Word) (a : Nat) :
    rm8Span (.reg r) s next a ↔ False := Iff.rfl

@[simp] theorem rm8Span_mem (m : Mem) (s : State) (next : Word) (a : Nat) :
    rm8Span (.mem m) s next a ↔
      (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + 1 := Iff.rfl

@[simp] theorem xrmSpan_reg (size : Nat) (r : Silmaril.X86.XReg) (s : State) (next : Word)
    (a : Nat) : xrmSpan size (.reg r) s next a ↔ False := Iff.rfl

@[simp] theorem xrmSpan_mem (size : Nat) (m : Mem) (s : State) (next : Word) (a : Nat) :
    xrmSpan size (.mem m) s next a ↔
      (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + size := Iff.rfl

@[simp] theorem readSet_memEv (k : Kind) (lk : Bool) (size : Nat) (m : Mem) (s : State)
    (next : Word) (a : Nat) :
    readSet (memEv k lk size m s next) a ↔
      k.reads = true ∧ (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + size := by
  simp [memEv]

@[simp] theorem writeSet_memEv (k : Kind) (lk : Bool) (size : Nat) (m : Mem) (s : State)
    (next : Word) (a : Nat) :
    writeSet (memEv k lk size m s next) a ↔
      k.writes = true ∧ (m.addr s next).toNat ≤ a ∧ a < (m.addr s next).toNat + size := by
  simp [memEv]

@[simp] theorem readSet_rmEv (k : Kind) (lk : Bool) (size : Nat) (op : RM) (s : State)
    (next : Word) (a : Nat) :
    readSet (rmEv k lk size op s next) a ↔ k.reads = true ∧ rmSpan size op s next a := by
  cases op <;> simp [rmEv, memEv, rmSpan]

@[simp] theorem writeSet_rmEv (k : Kind) (lk : Bool) (size : Nat) (op : RM) (s : State)
    (next : Word) (a : Nat) :
    writeSet (rmEv k lk size op s next) a ↔ k.writes = true ∧ rmSpan size op s next a := by
  cases op <;> simp [rmEv, memEv, rmSpan]

@[simp] theorem readSet_rm8Ev (k : Kind) (lk : Bool) (op : Silmaril.X86.Ext8.RM8) (s : State)
    (next : Word) (a : Nat) :
    readSet (rm8Ev k lk op s next) a ↔ k.reads = true ∧ rm8Span op s next a := by
  cases op <;> simp [rm8Ev, memEv, rm8Span]

@[simp] theorem writeSet_rm8Ev (k : Kind) (lk : Bool) (op : Silmaril.X86.Ext8.RM8) (s : State)
    (next : Word) (a : Nat) :
    writeSet (rm8Ev k lk op s next) a ↔ k.writes = true ∧ rm8Span op s next a := by
  cases op <;> simp [rm8Ev, memEv, rm8Span]

@[simp] theorem readSet_xrmEv (k : Kind) (size : Nat) (op : Silmaril.X86.Sse9.XRM)
    (s : State) (next : Word) (a : Nat) :
    readSet (xrmEv k size op s next) a ↔ k.reads = true ∧ xrmSpan size op s next a := by
  cases op <;> simp [xrmEv, memEv, xrmSpan]

@[simp] theorem writeSet_xrmEv (k : Kind) (size : Nat) (op : Silmaril.X86.Sse9.XRM)
    (s : State) (next : Word) (a : Nat) :
    writeSet (xrmEv k size op s next) a ↔ k.writes = true ∧ xrmSpan size op s next a := by
  cases op <;> simp [xrmEv, memEv, xrmSpan]

@[simp] theorem reads_load : Kind.load.reads = true := rfl
@[simp] theorem reads_store : Kind.store.reads = false := rfl
@[simp] theorem reads_rmw : Kind.rmw.reads = true := rfl
@[simp] theorem reads_fence (k : Silmaril.X86.Atomic9.FenceKind) :
    (Kind.fence k).reads = false := rfl
@[simp] theorem writes_load : Kind.load.writes = false := rfl
@[simp] theorem writes_store : Kind.store.writes = true := rfl
@[simp] theorem writes_rmw : Kind.rmw.writes = true := rfl
@[simp] theorem writes_fence (k : Silmaril.X86.Atomic9.FenceKind) :
    (Kind.fence k).writes = false := rfl

@[simp] theorem readSet_pushEv (s : State) (a : Nat) : readSet (pushEv s) a ↔ False := by
  simp [pushEv]

@[simp] theorem writeSet_pushEv (s : State) (a : Nat) :
    writeSet (pushEv s) a ↔ (s.read .rsp - 8#64).toNat ≤ a ∧ a < (s.read .rsp - 8#64).toNat + 8 := by
  simp only [pushEv, writeSet_singleton]; simp

@[simp] theorem readSet_popEv (s : State) (a : Nat) :
    readSet (popEv s) a ↔ (s.read .rsp).toNat ≤ a ∧ a < (s.read .rsp).toNat + 8 := by
  simp only [popEv, readSet_singleton]; simp

@[simp] theorem writeSet_popEv (s : State) (a : Nat) : writeSet (popEv s) a ↔ False := by
  simp [popEv]

@[simp] theorem aluKind_reads (op : Silmaril.X86.AluOp) : (aluKind op).reads = true := by
  unfold aluKind; split <;> rfl

@[simp] theorem aluKind_writes (op : Silmaril.X86.AluOp) :
    (aluKind op).writes = true ↔ op ≠ .cmp := by
  unfold aluKind; split <;> simp_all [Kind.writes]

/-! ## Agreement -/

theorem Agree.refl (R : Nat → Prop) (m : Memory) : Agree R m m := ⟨rfl, fun _ _ => rfl⟩

theorem Agree.mono {R R' : Nat → Prop} {m m' : Memory} (h : Agree R m m')
    (hs : ∀ a, R' a → R a) : Agree R' m m' :=
  ⟨h.1, fun a ha => h.2 a (hs a ha)⟩

theorem readBytes_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {a k : Nat}
    (hs : ∀ o < k, R (a + o)) : m'.readBytes a k = m.readBytes a k := by
  unfold Memory.readBytes Memory.readWith
  have hc : m'.checkSpan .read a k = m.checkSpan .read a k := by
    unfold Memory.checkSpan Memory.permits; rw [h.1]
  rw [hc, Memory.readBacking_congr (fun o ho => by
    have := h.2 _ (hs o ho)
    simpa using this.symm)]

theorem loadN_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {a : Word} {k : Nat}
    (hs : ∀ x, a.toNat ≤ x ∧ x < a.toNat + k → R x) : loadN m' a k = loadN m a k := by
  unfold loadN
  rw [readBytes_agree h (fun o ho => hs _ ⟨by omega, by omega⟩)]

theorem readRM_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {sz : Sz} {op : RM}
    {s : State} {next : Word} (hs : ∀ x, rmSpan sz.bytes op s next x → R x) :
    readRM sz op s m' next = readRM sz op s m next := by
  cases op with
  | reg r => rfl
  | mem a => simp only [readRM]; rw [loadN_agree h hs]

theorem readNarrow_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {n : Narrow}
    {op : RM} {s : State} {next : Word} (hs : ∀ x, rmSpan n.bytes op s next x → R x) :
    readNarrow n op s m' next = readNarrow n op s m next := by
  cases op with
  | reg r => rfl
  | mem a => simp only [readNarrow]; rw [loadN_agree h hs]

theorem popWord_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {s : State}
    (hs : ∀ x, (s.read .rsp).toNat ≤ x ∧ x < (s.read .rsp).toNat + 8 → R x) :
    Silmaril.X86.popWord s m' = Silmaril.X86.popWord s m := by
  unfold Silmaril.X86.popWord
  rw [readBytes_agree h (fun o ho => hs _ ⟨by omega, by omega⟩)]

/-! ## Writes -/

theorem Patched.none {W : Nat → Prop} {m m' : Memory} (hW : ∀ a, ¬ W a) :
    Patched W m m m' m' :=
  ⟨rfl, rfl, fun a h => absurd h (hW a), fun _ _ => rfl, fun _ _ => rfl,
    fun a h => absurd h (hW a)⟩

theorem Patched.congrW {W W' : Nat → Prop} {m m₁ m' m₁' : Memory} (h : Patched W m m₁ m' m₁')
    (e : ∀ a, W' a ↔ W a) : Patched W' m m₁ m' m₁' :=
  ⟨h.regions, h.regions', fun a ha => h.inside a ((e a).1 ha),
    fun a ha => h.outside a (fun hw => ha ((e a).2 hw)),
    fun a ha => h.outside' a (fun hw => ha ((e a).2 hw)), fun a ha => h.wrote a ((e a).1 ha)⟩

/-- Two writes of the same bytes at the same address. -/
theorem writeBytes_patched {W : Nat → Prop} {m m' m₁ m₁' : Memory} {a : Nat} {bs : List Byte}
    (hW : ∀ x, W x ↔ a ≤ x ∧ x < a + bs.length)
    (h₁ : m.writeBytes a bs = some m₁) (h₁' : m'.writeBytes a bs = some m₁') :
    Patched W m m₁ m' m₁' := by
  have w := Memory.writeBytes_writesOnly h₁
  have w' := Memory.writeBytes_writesOnly h₁'
  have hp := Memory.writeBytes_permitted h₁
  rw [Memory.Permitted, Memory.checkSpan_iff] at hp
  refine ⟨w.1, w'.1, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have hx' := (hW x).1 hx
    have g := Memory.writeBytes_get h₁ (x - a) (by omega)
    have g' := Memory.writeBytes_get h₁' (x - a) (by omega)
    rw [show a + (x - a) = x by omega] at g g'
    simp only [Std.ExtHashMap.get?_eq_getElem?] at g g'
    rw [g, g']
  · rw [hW] at hx
    have := w.2 x (by omega)
    simpa using this
  · rw [hW] at hx
    have := w'.2 x (by omega)
    simpa using this
  · have hx' := (hW x).1 hx
    refine ⟨by simpa [show a + (x - a) = x by omega] using hp.2.2 (x - a) (by omega), ?_⟩
    have g := Memory.writeBytes_get h₁ (x - a) (by omega)
    rw [show a + (x - a) = x by omega] at g
    simp only [Std.ExtHashMap.get?_eq_getElem?] at g
    rw [g]; rfl

theorem writeBytes_none_iff {m m' : Memory} (h : m.regions = m'.regions) (a : Nat)
    (bs : List Byte) : m.writeBytes a bs = none ↔ m'.writeBytes a bs = none := by
  have hc : m'.checkSpan .write a bs.length = m.checkSpan .write a bs.length := by
    unfold Memory.checkSpan Memory.permits; rw [h]
  unfold Memory.writeBytes
  rw [hc]
  split <;> simp

/-- The relation of two optional writes of the same bytes, with any payload. -/
theorem writeBytes_rel {α : Type} {W : Nat → Prop} {m m' : Memory} {a : Nat} {bs : List Byte}
    (hW : ∀ x, W x ↔ a ≤ x ∧ x < a + bs.length) (h : m.regions = m'.regions) (t : α) :
    OptRel W m m' ((m.writeBytes a bs).map fun m₁ => (t, m₁))
      ((m'.writeBytes a bs).map fun m₁ => (t, m₁)) := by
  cases h₁ : m.writeBytes a bs with
  | none =>
    rw [(writeBytes_none_iff h a bs).1 h₁]; trivial
  | some m₁ =>
    cases h₁' : m'.writeBytes a bs with
    | none => rw [← writeBytes_none_iff h a bs, h₁] at h₁'; cases h₁'
    | some m₁' => exact ⟨rfl, writeBytes_patched hW h₁ h₁'⟩

theorem storeN_rel {α : Type} {W : Nat → Prop} {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (hW : ∀ x, W x ↔ a.toNat ≤ x ∧ x < a.toNat + k) (h : m.regions = m'.regions) (t : α) :
    OptRel W m m' ((storeN m a k v).map fun m₁ => (t, m₁))
      ((storeN m' a k v).map fun m₁ => (t, m₁)) :=
  writeBytes_rel (by simpa using hW) h t

/-! ## `OptRel` and `Rel` -/

theorem OptRel.none {α : Type} {W : Nat → Prop} {m m' : Memory} :
    OptRel W m m' (Option.none : Option (α × Memory)) Option.none := trivial

/-- No write: both succeed with the same payload and their input memories. -/
theorem OptRel.pure {α : Type} {W : Nat → Prop} {m m' : Memory} (hW : ∀ a, ¬ W a) (t : α) :
    OptRel W m m' (some (t, m)) (some (t, m')) :=
  ⟨rfl, Patched.none hW⟩

/-- A read whose value becomes the payload, memory unchanged. -/
theorem OptRel.read {α β : Type} {W : Nat → Prop} {m m' : Memory} (hW : ∀ a, ¬ W a)
    (o : Option β) (g : β → α) :
    OptRel W m m' (o.map fun v => (g v, m)) (o.map fun v => (g v, m')) := by
  cases o with
  | none => trivial
  | some v => exact OptRel.pure hW (g v)

/-- A payload transformation that ignores the memory. -/
theorem OptRel.map {α β : Type} {W : Nat → Prop} {m m' : Memory}
    {o o' : Option (α × Memory)} (h : OptRel W m m' o o') (f : α × Memory → β × Memory)
    (h2 : ∀ p, (f p).2 = p.2) (h1 : ∀ a b b', (f (a, b)).1 = (f (a, b')).1) :
    OptRel W m m' (o.map f) (o'.map f) := by
  cases o with
  | none => cases o' with
    | none => trivial
    | some _ => cases h
  | some p => cases o' with
    | none => cases h
    | some p' =>
      obtain ⟨e, hp⟩ := h
      refine ⟨?_, ?_⟩
      · obtain ⟨a, b⟩ := p; obtain ⟨a', b'⟩ := p'
        simp only at e; subst e
        exact h1 a b b'
      · simpa [Option.map, h2] using hp

theorem OptRel.congrW {α : Type} {W W' : Nat → Prop} {m m' : Memory}
    {o o' : Option (α × Memory)} (h : OptRel W m m' o o') (e : ∀ a, W' a ↔ W a) :
    OptRel W' m m' o o' := by
  cases o with
  | none => cases o' with
    | none => trivial
    | some _ => cases h
  | some p => cases o' with
    | none => cases h
    | some p' => exact ⟨h.1, Patched.congrW h.2 e⟩

theorem Rel.congrW {ε α : Type} {W W' : Nat → Prop} {m m' : Memory}
    {r r' : ε ⊕ (α × Memory)} (h : Rel W m m' r r') (e : ∀ a, W' a ↔ W a) :
    Rel W' m m' r r' := by
  cases r with
  | inl x => cases r' with
    | inl _ => exact h
    | inr _ => cases h
  | inr p => cases r' with
    | inl _ => cases h
    | inr p' => exact ⟨h.1, Patched.congrW h.2 e⟩

theorem Rel.refl_inl {ε α : Type} {W : Nat → Prop} {m m' : Memory} (e : ε) :
    Rel (α := α) W m m' (.inl e) (.inl e) := rfl

/-! ## `Ext.Result` -/

theorem extView_ok_rel {W : Nat → Prop} {m m' m₁ m₁' : Memory} {c : State}
    (h : Patched W m m₁ m' m₁') : Rel W m m' (extView (.ok c m₁)) (extView (.ok c m₁')) :=
  ⟨rfl, h⟩

theorem extView_ok_pure {W : Nat → Prop} {m m' : Memory} (hW : ∀ a, ¬ W a) (c : State) :
    Rel W m m' (extView (.ok c m)) (extView (.ok c m')) :=
  ⟨rfl, Patched.none hW⟩

theorem extView_fault {W : Nat → Prop} {m m' : Memory} (r : Result) (hr : ∀ c mm, r ≠ .ok c mm) :
    Rel W m m' (extView r) (extView r) := by
  cases r with
  | ok c mm => exact absurd rfl (hr c mm)
  | _ => rfl

theorem extView_dataFault {W : Nat → Prop} {m m' : Memory} :
    Rel W m m' (extView .dataFault) (extView .dataFault) := rfl

theorem extView_divideError {W : Nat → Prop} {m m' : Memory} :
    Rel W m m' (extView .divideError) (extView .divideError) := rfl

theorem extView_trap {W : Nat → Prop} {m m' : Memory} :
    Rel W m m' (extView .trap) (extView .trap) := rfl

theorem extView_undefinedCondition {W : Nat → Prop} {m m' : Memory} (c : Cond) :
    Rel W m m' (extView (.undefinedCondition c)) (extView (.undefinedCondition c)) := rfl

/-- Case analysis of two related optional successors. -/
theorem OptRel.cases {α : Type} {W : Nat → Prop} {m m' : Memory} {o o' : Option (α × Memory)}
    (h : OptRel W m m' o o') :
    (o = Option.none ∧ o' = Option.none) ∨
      ∃ a m₁ m₁', o = some (a, m₁) ∧ o' = some (a, m₁') ∧ Patched W m m₁ m' m₁' := by
  cases o with
  | none => cases o' with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some _ => cases h
  | some p => cases o' with
    | none => cases h
    | some p' =>
      obtain ⟨a, b⟩ := p; obtain ⟨a', b'⟩ := p'
      obtain ⟨e, hp⟩ := h
      simp only at e; subst e
      exact Or.inr ⟨a, b, b', rfl, rfl, hp⟩

theorem retire_rel {W : Nat → Prop} {m m' : Memory} {o o' : Option (State × Memory)}
    {next : Word} (h : OptRel W m m' o o') :
    Rel W m m' (extView (retire next o)) (extView (retire next o')) := by
  cases o with
  | none => cases o' with
    | none => rfl
    | some _ => cases h
  | some p => cases o' with
    | none => cases h
    | some p' =>
      obtain ⟨t, mm⟩ := p; obtain ⟨t', mm'⟩ := p'
      obtain ⟨e, hp⟩ := h
      simp only at e; subst e
      exact ⟨rfl, hp⟩

/-! ## Operand writes -/

theorem writeRM_rel {W : Nat → Prop} {m m' : Memory} {sz : Sz} {op : RM} {v : BitVec sz.bits}
    {s : State} {next : Word} (hW : ∀ x, W x ↔ rmSpan sz.bytes op s next x)
    (h : m.regions = m'.regions) :
    OptRel W m m' (writeRM sz op v s m next) (writeRM sz op v s m' next) := by
  cases op with
  | reg r => exact OptRel.pure (fun a ha => by simpa [rmSpan] using (hW a).1 ha) _
  | mem a => exact storeN_rel (by simpa [rmSpan] using hW) h s

theorem writeNarrow_rel {W : Nat → Prop} {m m' : Memory} {n : Narrow} {op : RM}
    {v : BitVec n.bits} {s : State} {next : Word} (hW : ∀ x, W x ↔ rmSpan n.bytes op s next x)
    (h : m.regions = m'.regions) :
    OptRel W m m' (writeNarrow n op v s m next) (writeNarrow n op v s m' next) := by
  cases op with
  | reg r => exact OptRel.pure (fun a ha => by simpa [rmSpan] using (hW a).1 ha) _
  | mem a => exact storeN_rel (by simpa [rmSpan] using hW) h s

theorem writeRM8_rel {W : Nat → Prop} {m m' : Memory} {op : RM} {v : BitVec 8} {s : State}
    {next : Word} (hW : ∀ x, W x ↔ rmSpan 1 op s next x) (h : m.regions = m'.regions) :
    OptRel W m m' (writeRM8 op v s m next) (writeRM8 op v s m' next) := by
  cases op with
  | reg r => exact OptRel.pure (fun a ha => by simpa [rmSpan] using (hW a).1 ha) _
  | mem a => exact storeN_rel (by simpa [rmSpan] using hW) h s

theorem pushWord_rel {W : Nat → Prop} {m m' : Memory} {s : State} {v : Word}
    (hW : ∀ x, W x ↔ (s.read .rsp - 8#64).toNat ≤ x ∧ x < (s.read .rsp - 8#64).toNat + 8)
    (h : m.regions = m'.regions) :
    OptRel W m m' (Silmaril.X86.pushWord s m v) (Silmaril.X86.pushWord s m' v) := by
  unfold Silmaril.X86.pushWord
  exact writeBytes_rel (by simpa using hW) h _

/-! ## The ALU helpers -/

theorem aluStep_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m') {sz : Sz}
    {op : Silmaril.X86.AluOp} {dst : RM} {y : BitVec sz.bits} {s : State} {next : Word}
    (hR : ∀ x, rmSpan sz.bytes dst s next x → R x)
    (hW : ∀ x, W x ↔ op ≠ .cmp ∧ rmSpan sz.bytes dst s next x) :
    OptRel W m m' (aluStep sz op dst y s m next) (aluStep sz op dst y s m' next) := by
  unfold aluStep
  rw [readRM_agree hA hR]
  cases readRM sz dst s m next with
  | none => trivial
  | some x =>
    by_cases hc : op = .cmp
    · simp only [hc, ite_true]
      exact OptRel.pure (fun a ha => by simpa [hc] using (hW a).1 ha) _
    · simp only [hc, ite_false]
      exact OptRel.map (writeRM_rel (fun a => by simpa [hc] using hW a) hA.1) _
        (fun _ => rfl) (fun _ _ _ => rfl)

theorem aluStepR_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m') {sz : Sz}
    {op : Silmaril.X86.AluOp} {dst : Reg} {src : RM} {s : State} {next : Word}
    (hR : ∀ x, rmSpan sz.bytes src s next x → R x) (hW : ∀ x, ¬ W x) :
    OptRel W m m' (aluStepR sz op dst src s m next) (aluStepR sz op dst src s m' next) := by
  unfold aluStepR
  rw [readRM_agree hA hR]
  cases readRM sz src s m next with
  | none => trivial
  | some x =>
    dsimp only
    split
    · exact OptRel.pure hW _
    · exact OptRel.pure hW _

/-! ## The `mev_rel` tactic -/

/-- Discharge a span side condition: a read span inside a read set (`∀ x, span x → R x`), a
write set equal to a store's span (`∀ x, W x ↔ span x`), or an empty write set. -/
syntax "mev_span" : tactic

macro_rules
  | `(tactic| mev_span) => `(tactic| first
    | (intro x hx; (try simp at hx); simp [hx])
    | (intro x; simp))

/-- One closing or decomposing step of `mev_rel` with the agreement hypothesis `hA`. The later
families add their own helper lemmas as further `macro_rules`. -/
syntax "mev_leaf" ident : tactic

macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| exact OptRel.none)
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| exact extView_dataFault)
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| exact extView_divideError)
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| exact extView_trap)
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| exact extView_undefinedCondition _)
macro_rules
  | `(tactic| mev_leaf $hA) =>
    `(tactic| (rw [readRM_agree $hA]; rotate_left; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) =>
    `(tactic| (rw [readNarrow_agree $hA]; rotate_left; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) =>
    `(tactic| (rw [popWord_agree $hA]; rotate_left; mev_span))
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| apply retire_rel)
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply aluStep_rel $hA <;> mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply aluStepR_rel $hA <;> mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply writeRM_rel _ ($hA).1; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply writeNarrow_rel _ ($hA).1; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply writeRM8_rel _ ($hA).1; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply pushWord_rel _ ($hA).1; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply storeN_rel _ ($hA).1; mev_span))
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| (apply OptRel.read; mev_span))
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| (apply OptRel.pure; mev_span))
macro_rules
  | `(tactic| mev_leaf $_) => `(tactic| (apply extView_ok_pure; mev_span))
macro_rules
  | `(tactic| mev_leaf $_) =>
    `(tactic| (apply OptRel.map; rotate_left; (intros; rfl); (intros; rfl)))

/-- Close `Rel W m m' (view (exec … m)) (view (exec … m'))` (or an `OptRel` goal) by
rewriting reads and relating writes, through `retire`, `Option.map`, `match` and `if`. -/
syntax "mev_rel" ident : tactic

macro_rules
  | `(tactic| mev_rel $hA) => `(tactic| repeat' (first | mev_leaf $hA | split))

/-! ## `Ext.exec` -/

section
-- The helpers are closed by their own lemmas; keeping them folded keeps failed matches cheap.
attribute [local irreducible] Silmaril.X86.pushWord Silmaril.X86.popWord writeRM writeNarrow
  writeRM8 storeN loadN aluStep aluStepR readRM readNarrow

/-- **`Ext.exec` is local** for `extAccesses`, for every instruction and length. -/
theorem ext_local (i : Instr) (s : State) (len : Nat) :
    Local extView (fun m => exec i s m len) (extAccesses i s len) := by
  constructor
  intro m m' hA
  cases i
  case unary sz op dst => cases op <;> (simp only [exec, extAccesses] at hA ⊢; mev_rel hA)
  case cxe sz => cases sz <;> (simp only [exec, extAccesses] at hA ⊢; mev_rel hA)
  case call rel =>
    simp only [exec, extAccesses] at hA ⊢
    rcases OptRel.cases (pushWord_rel (s := s) (v := s.rip + BitVec.ofNat 64 len)
      (W := writeSet (pushEv s)) (by mev_span) hA.1) with ⟨h1, h2⟩ | ⟨t, m₁, m₁', h1, h2, hp⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2]; exact ⟨rfl, hp⟩
  all_goals (simp only [exec, extAccesses] at hA ⊢; mev_rel hA)

end

end Silmaril.Proofs.X86.MemEvent
