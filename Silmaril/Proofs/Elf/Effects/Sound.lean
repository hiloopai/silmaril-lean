module

public import Silmaril.Elf.Effects.Defs
public import Silmaril.X86.Cfg.Thms
import Silmaril.X86.Ext.SymExec

/-! Proofs for `Silmaril.Elf.Effects`: soundness of a checked certificate (`sound`).

The invariant of a reachable state `u` (`Inv`): either `rip` is foreign, or it is the address of
an instruction of a block of a function of `N`, at an offset where the block decoder `walk`
accepts the rest of the block, with the block's `rax` constant (if any) in `rax`. Every step
preserves it (`step_ok`) and its event is covered by `N`. -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Effects

open Silmaril.X86 (Word Byte State)
open Silmaril.Process (Memory)
open Silmaril.X86.Flow (FlowDec Kind Admits RaxOk)
open Silmaril.X86.Cfg (Graph Block Term Target walk termOk raxStep wrap walk_cases ofNat_wrap)
open Silmaril.Elf
open Silmaril.Elf.Effects

variable {σ : Type}

/-! ## Arithmetic -/

theorem ofNat_add' (a b : Nat) : BitVec.ofNat 64 (a + b) = BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

theorem toNat_sub_base (base : Word) {c : Nat} (hc : c < 2 ^ 64) :
    (base + BitVec.ofNat 64 c - base).toNat = c := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-! ## Unpacking the check -/

theorem fnOk_of_mem {D : FlowDec} {P : Cert} {roots : List Nat} (h : P.check D roots = true)
    {a : Nat} {C : Graph Ref} (hm : (a, C) ∈ P.fns) : P.fnOk D a C = true := by
  simp only [Cert.check, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 _ hm

theorem has_iff {P : Cert} {a : Nat} : P.has a = true ↔ ∃ C, (a, C) ∈ P.fns := by
  simp only [Cert.has, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨b, C⟩, hm, rfl⟩; exact ⟨C, hm⟩
  · rintro ⟨C, hm⟩; exact ⟨_, hm, rfl⟩

theorem has_of_root {D : FlowDec} {P : Cert} {roots : List Nat} (h : P.check D roots = true)
    {a : Nat} (ha : a ∈ roots) : ∃ C, (a, C) ∈ P.fns := by
  simp only [Cert.check, Bool.and_eq_true, List.all_eq_true] at h
  exact has_iff.1 (h.2 a ha)

structure FnFacts (D : FlowDec) (P : Cert) (a : Nat) (C : Graph Ref) : Prop where
  entry : C.entry = a
  lt : a < 2 ^ 64
  ok : ∀ b ∈ C.blocks, b.ok D = true
  start : C.isStart C.entry = true
  succ : ∀ b ∈ C.blocks, ∀ c ∈ b.term.succs, C.isStart c = true
  edge : ∀ e ∈ edgesOf a C, e ∈ P.graph.edges ∧ ∀ c, e.2 = .fn c → ∃ C', (c, C') ∈ P.fns

theorem fnFacts {D : FlowDec} {P : Cert} {a : Nat} {C : Graph Ref} (h : P.fnOk D a C = true) :
    FnFacts D P a C := by
  simp only [Cert.fnOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Graph.sub, Graph.closed] at h
  obtain ⟨⟨⟨he, hlt⟩, ⟨hok, hst, hsc⟩⟩, hed⟩ := h
  refine ⟨he, hlt, hok, hst, hsc, fun e he' => ?_⟩
  obtain ⟨h1, h2⟩ := hed e he'
  refine ⟨by simpa using h1, fun c hc => ?_⟩
  rw [hc] at h2; exact has_iff.1 h2

theorem isStart_elim {C : Graph Ref} {a : Nat} (h : C.isStart a = true) :
    ∃ b ∈ C.blocks, b.start = a := by
  simp only [Graph.isStart, List.any_eq_true, beq_iff_eq] at h; exact h

theorem mem_edgesOf {f : Nat} {C : Graph Ref} {b : Block Ref} (hb : b ∈ C.blocks) {n : Node}
    (hn : n ∈ termNodes b.term) : (Node.fn f, n) ∈ edgesOf f C := by
  simp only [edgesOf, List.mem_flatMap, List.mem_map]
  exact ⟨b, hb, n, hn, rfl⟩

/-! ## Inverting `termOk` -/

section
variable {ε : Type} {k : Silmaril.X86.Flow.Kind} {stop : Nat} {v : Option Nat}

theorem tok_fall {n : Nat} (h : termOk (.fall n : Term ε) k stop v = true) :
    (k = .seq ∨ k = .rep) ∧ n = stop := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_jcc {a n : Nat} (h : termOk (.jcc a n : Term ε) k stop v = true) :
    ∃ r, k = .jcc r ∧ a = wrap (stop + r) ∧ n = stop := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_jmp {x : Target ε} (h : termOk (.jmp x) k stop v = true) :
    ∃ r a, k = .jmp r ∧ (x = .blk a ∨ x = .fn a) ∧ a = wrap (stop + r) := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_jmpInd {ts : Option (List (Target ε))} {w : Silmaril.X86.Cfg.Why}
    (h : termOk (.jmpInd ts w) k stop v = true) : ∃ op, k = .jmpInd op := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_call {x : Target ε} {r : Option Nat} (h : termOk (.call x r) k stop v = true) :
    ∃ d a, k = .call d ∧ x = .fn a ∧ a = wrap (stop + d) := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_callInd {ts : Option (List (Target ε))} {w : Silmaril.X86.Cfg.Why} {r : Option Nat}
    (h : termOk (.callInd ts w r) k stop v = true) :
    (∃ op, k = .callInd op) ∧ ∀ x ∈ ts.getD [], Target.callable x = true := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_sys {n : Option Nat} {r : Nat} (h : termOk (.sys n r : Term ε) k stop v = true) :
    k = .syscall ∧ r = stop ∧ n = v ∧ n.getD 0 < 2 ^ 64 := by
  unfold termOk at h; split at h <;> simp_all
  obtain ⟨⟨_, rfl⟩, h⟩ := h; exact h

theorem tok_sysOther {r : Nat} (h : termOk (.sysOther r : Term ε) k stop v = true) :
    k = .sysOther ∧ r = stop := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_ret (h : termOk (.ret : Term ε) k stop v = true) : k = .ret := by
  unfold termOk at h; split at h <;> simp_all

theorem tok_trap (h : termOk (.trap : Term ε) k stop v = true) : k = .trap := by
  unfold termOk at h; split at h <;> simp_all

end

theorem rip_def {W : World σ} {t : σ} : W.rip t = (W.J.core t).rip := rfl

theorem node_jump_img {W : World σ} {base : Word} {t : σ} (h : W.cls (W.rip t) = .image) :
    Ev.node W base (.jump (W.J.core t).rip) = none := by
  dsimp only [Ev.node]; rw [← rip_def, h]

theorem node_jump_ent {W : World σ} {base : Word} {t : σ} {r : Ref} (h : W.cls (W.rip t) = .entry r) :
    Ev.node W base (.jump (W.J.core t).rip) = some (.ext r) := by
  dsimp only [Ev.node]; rw [← rip_def, h]

theorem node_call_img {W : World σ} {base : Word} {t : σ} (r : Word) (h : W.cls (W.rip t) = .image) :
    Ev.node W base (.call (W.J.core t).rip r) = some (.fn ((W.rip t) - base).toNat) := by
  dsimp only [Ev.node]; rw [← rip_def, h]

theorem node_call_ent {W : World σ} {base : Word} {t : σ} (r : Word) {x : Ref}
    (h : W.cls (W.rip t) = .entry x) : Ev.node W base (.call (W.J.core t).rip r) = some (.ext x) := by
  dsimp only [Ev.node]; rw [← rip_def, h]

/-! ## The invariant -/

/-- `u` is at an instruction of a certified block of a function of `N`. -/
def ImgInv (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (N : Node → Prop) (u : σ) : Prop :=
  ∃ f C b fuel o v, (f, C) ∈ P.fns ∧ N (.fn f) ∧ b ∈ C.blocks ∧
    walk D b.term b.start fuel o v (b.bytes.drop o) = true ∧
    W.rip u = base + BitVec.ofNat 64 (b.start + o) ∧
    ∀ n, v = some n → (W.J.core u).read .rax = BitVec.ofNat 64 n

/-- The invariant: foreign code, or a certified instruction. -/
def Inv (W : World σ) (D : FlowDec) (base : Word) (P : Cert) (N : Node → Prop) (u : σ) : Prop :=
  W.cls (W.rip u) ≠ .image ∨ ImgInv W D base P N u

section
variable {W : World σ} {D : FlowDec} {base : Word} {P : Cert} {esc : List Nat} {entry : Nat}
  {keep : σ → Prop} {s₀ : σ} {N : Node → Prop}

theorem walk_lt {t : Term Ref} {start fuel o : Nat} {v : Option Nat} {bytes : List Byte}
    (h : walk D t start fuel o v (bytes.drop o) = true) : o < bytes.length := by
  obtain ⟨i, l, _, h0, hl, _⟩ := walk_cases h
  simp at hl; omega

theorem img_cls (hS : Setting W D base P esc entry keep s₀ N) {u : σ}
    (h : ImgInv W D base P N u) : W.cls (W.rip u) = .image := by
  obtain ⟨f, C, b, fuel, o, v, hfC, _, hb, hw, hrip, _⟩ := h
  rw [hrip]; exact hS.image f C hfC b hb o (walk_lt hw)

/-- A state at the start of a block of a function of `N` satisfies the invariant. -/
theorem inv_start (hS : Setting W D base P esc entry keep s₀ N) {f a : Nat} {C : Graph Ref}
    (hfC : (f, C) ∈ P.fns) (hN : N (.fn f)) (ha : C.isStart a = true) {t : σ}
    (ht : W.rip t = base + BitVec.ofNat 64 a) : ImgInv W D base P N t := by
  obtain ⟨b, hb, rfl⟩ := isStart_elim ha
  have hF := fnFacts (fnOk_of_mem hS.check hfC)
  refine ⟨f, C, b, b.bytes.length, 0, none, hfC, hN, hb, ?_, by simpa using ht, by simp⟩
  simpa [Block.ok] using hF.ok b hb

/-- A state at the entry of a function of `N` that has a CFG. -/
theorem inv_fn (hS : Setting W D base P esc entry keep s₀ N) {c : Nat} {C : Graph Ref}
    (hfC : (c, C) ∈ P.fns) (hN : N (.fn c)) {t : σ} (ht : W.rip t = base + BitVec.ofNat 64 c) :
    ImgInv W D base P N t := by
  have hF := fnFacts (fnOk_of_mem hS.check hfC)
  exact inv_start hS hfC hN (hF.entry ▸ hF.start) ht

/-- The node of a terminator's target is in `N`, and a function target has a CFG. -/
theorem node_in (hS : Setting W D base P esc entry keep s₀ N) {f : Nat} {C : Graph Ref}
    (hfC : (f, C) ∈ P.fns) (hN : N (.fn f)) {b : Block Ref} (hb : b ∈ C.blocks) {n : Node}
    (hn : n ∈ termNodes b.term) : N n ∧ ∀ c, n = .fn c → ∃ C', (c, C') ∈ P.fns := by
  have hF := fnFacts (fnOk_of_mem hS.check hfC)
  obtain ⟨he, hc⟩ := hF.edge _ (mem_edgesOf hb hn)
  exact ⟨hS.closed _ he hN, hc⟩

/-- Entering a function target of a terminator. -/
theorem inv_target (hS : Setting W D base P esc entry keep s₀ N) {f : Nat} {C : Graph Ref}
    (hfC : (f, C) ∈ P.fns) (hN : N (.fn f)) {b : Block Ref} (hb : b ∈ C.blocks) {c : Nat}
    (hn : Node.fn c ∈ termNodes b.term) {t : σ} (ht : W.rip t = base + BitVec.ofNat 64 c) :
    ImgInv W D base P N t ∧ N (.fn c) ∧ c < 2 ^ 64 := by
  obtain ⟨hNc, hc⟩ := node_in hS hfC hN hb hn
  obtain ⟨C', hC'⟩ := hc c rfl
  exact ⟨inv_fn hS hC' hNc ht, hNc, (fnFacts (fnOk_of_mem hS.check hC')).lt⟩

/-- Coming back into the image. -/
theorem inv_landing (hS : Setting W D base P esc entry keep s₀ N) {t : σ}
    (h : Landing W base P N esc t) : Inv W D base P N t := by
  rcases h with h | ⟨a, ⟨f, C, b, hfC, hN, hb, hr⟩, ht⟩ | ⟨e, he, ht⟩
  · exact Or.inl h
  · have hF := fnFacts (fnOk_of_mem hS.check hfC)
    have hs : a ∈ b.term.succs := by
      revert hr; cases b.term <;> simp [Term.retTo, Term.succs] <;> (intro h; subst h; simp)
    exact Or.inr (inv_start hS hfC hN (hF.succ b hb a hs) ht)
  · obtain ⟨C, hC⟩ := has_of_root hS.check (List.mem_cons_of_mem _ he)
    exact Or.inr (inv_fn hS hC (hS.escapes e he) ht)

/-- The initial state. -/
theorem inv_init (hS : Setting W D base P esc entry keep s₀ N) : Inv W D base P N s₀ := by
  obtain ⟨C, hC⟩ := has_of_root hS.check (List.mem_cons_self ..)
  exact Or.inr (inv_fn hS hC hS.root hS.start)

/-- The `rax` constant survives a step. -/
theorem rax_step {i : D.Instr} {v : Option Nat} {s t : State}
    (hv : ∀ n, v = some n → s.read .rax = BitVec.ofNat 64 n) (hr : RaxOk (D.rax i) s t) :
    ∀ n, raxStep D v i = some n → t.read .rax = BitVec.ofNat 64 n := by
  intro n hn
  unfold raxStep at hn
  revert hr hn
  cases D.rax i <;> simp [RaxOk] <;> intros <;> simp_all

/-- **The machine reads the block's instruction at a certified address**, which is image code. -/
theorem img_at (hS : Setting W D base P esc entry keep s₀ N) {es : List Ev} {u : σ}
    (hrun : Run W D keep (some s₀) es (some u)) {f : Nat} {C : Graph Ref} (hfC : (f, C) ∈ P.fns)
    {b : Block Ref} (hb : b ∈ C.blocks) {o : Nat}
    (hrip : W.rip u = base + BitVec.ofNat 64 (b.start + o)) {i : D.Instr} {l : Nat}
    (hdec : D.decode (b.bytes.drop o) = some (i, l)) (hl0 : 0 < l)
    (hll : l ≤ (b.bytes.drop o).length) :
    Silmaril.X86.Flow.At W.J D u i l ∧ W.cls (W.rip u) = .image ∧
      ∀ i' l', Silmaril.X86.Flow.At W.J D u i' l' → i' = i ∧ l' = l := by
  have hL := hS.code es u hrun f C hfC b hb
  have hw := Silmaril.X86.Ext.Loaded.noWrap hL
  have ho : o < b.bytes.length := by simp at hll; omega
  have haddr : (W.J.core u).rip.toNat = (base + BitVec.ofNat 64 b.start).toNat + o := by
    change (W.rip u).toNat = _
    rw [hrip, ofNat_add', ← BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Silmaril.Process.addressLimit] at hw
    omega
  have hfs : (W.J.mem u).fetchBytes (W.J.core u).rip.toNat (b.bytes.drop o).length =
      some (b.bytes.drop o) := by
    rw [haddr]
    have := Silmaril.X86.Ext.Loaded.fetchBytes_sub hL (offset := o)
      (len := (b.bytes.drop o).length) (by simp; omega) (by simp; omega)
    rw [this, List.take_of_length_le (by simp)]
  obtain ⟨_, hst⟩ := hS.stable _ _ _ hdec
  have hfl := Silmaril.X86.Flow.fetch_prefix hfs hll
  refine ⟨⟨_, hfl, by simpa using hst []⟩, ?_, ?_⟩
  · rw [hrip]; exact hS.image f C hfC b hb o ho
  · rintro i' l' ⟨w, hw', hdw⟩
    exact Silmaril.X86.Flow.at_unique hS.stable hfs hdec hw' hdw

/-- `next` at a certified instruction. -/
theorem next_eq {s : State} {base : Word} {a l : Nat} (h : s.rip = base + BitVec.ofNat 64 a) :
    Silmaril.X86.Flow.next s l = base + BitVec.ofNat 64 (a + l) := by
  simp only [Silmaril.X86.Flow.next, h, ofNat_add', BitVec.add_assoc]

/-- `rel` at a certified instruction. -/
theorem rel_eq {s : State} {base : Word} {a l : Nat} {r : Int} (h : s.rip = base + BitVec.ofNat 64 a) :
    Silmaril.X86.Flow.rel s l r = base + BitVec.ofNat 64 (wrap ((a + l : Nat) + r)) := by
  simp only [Silmaril.X86.Flow.rel, next_eq h, ofNat_wrap, BitVec.add_assoc]

theorem drop_drop' (bytes : List Byte) (o l : Nat) : (bytes.drop o).drop l = bytes.drop (o + l) := by
  rw [List.drop_drop]

/-- **One step**: its event is covered by `N`, and the next state satisfies the invariant. -/
theorem step_ok (hS : Setting W D base P esc entry keep s₀ N) {es : List Ev} {u : σ}
    (hrun : Run W D keep (some s₀) es (some u)) (hk : keep u) (hI : Inv W D base P N u)
    {e : Ev} {y : Option σ} (hst : Step W D (some u) e y) :
    (∀ n, e.node W base = some n → Covered N n) ∧ ∀ t, y = some t → keep t → Inv W D base P N t := by
  rcases hI with hfor | ⟨f, C, b, fuel, o, v, hfC, hNf, hb, hw, hrip, hrax⟩
  · cases hst with
    | user hc => exact absurd hc hfor
    | unknown hc => exact absurd hc hfor
    | sys hc => exact absurd hc hfor
    | sysOther hc => exact absurd hc hfor
    | lib hc hL =>
      refine ⟨fun n hn => (by cases hn), fun t ht hkt => ?_⟩
      subst ht
      exact inv_landing hS (hS.lib es u t hrun hk hc hL hkt)
  obtain ⟨i, l, hdec, hl0, hll, hrep, hcase⟩ := walk_cases hw
  obtain ⟨hAt, hcls, huniq⟩ := img_at hS hrun hfC hb hrip hdec hl0 hll
  have hlen : (b.bytes.drop o).length = b.bytes.length - o := List.length_drop ..
  have hob := walk_lt hw
  have hnext := next_eq (l := l) hrip
  -- the state after the block, or after this instruction
  have fresh : ∀ {c : Nat}, c ∈ b.term.succs → ∀ {t : σ}, W.rip t = base + BitVec.ofNat 64 c →
      ImgInv W D base P N t := fun {c} hc {t} ht =>
    inv_start hS hfC hNf ((fnFacts (fnOk_of_mem hS.check hfC)).succ b hb _ hc) ht
  cases hst with
  | unknown _ hno => exact absurd hAt (hno i l)
  | lib hc => exact absurd hcls hc
  | @user _ t i' l' _ hAt' hk1 hk2 hstep =>
    obtain ⟨rfl, rfl⟩ := huniq i' l' hAt'
    obtain ⟨hadm, hraxok⟩ := hS.law u t i' l' hAt' hstep
    refine ⟨?_, fun t' ht' hkt => ?_⟩
    · -- the event
      intro n hn
      rcases hcase with ⟨hl, hok⟩ | ⟨_, hkind, _⟩
      · cases hT : b.term with
        | fall m =>
          rw [hT] at hok; obtain ⟨hk', _⟩ := tok_fall hok
          rcases hk' with hk' | hk' <;> (rw [hk'] at hn; cases hn)
        | jcc a m =>
          rw [hT] at hok; obtain ⟨r, hk', ha, hm⟩ := tok_jcc hok
          rw [hk'] at hadm hn
          change Ev.node W base (.jump (W.J.core t).rip) = some n at hn
          have : W.cls (W.rip t) = .image := by
            rcases hadm with h | h
            · exact img_cls hS (fresh (c := m) (by simp [hT, Term.succs]) (by rw [rip_def, h, hnext, hm]))
            · exact img_cls hS (fresh (c := a) (by simp [hT, Term.succs])
                (by rw [rip_def, h, rel_eq hrip, ha]))
          rw [node_jump_img this] at hn; cases hn
        | jmp x =>
          rw [hT] at hok; obtain ⟨r, a, hk', hx, ha⟩ := tok_jmp hok
          rw [hk'] at hadm hn
          change Ev.node W base (.jump (W.J.core t).rip) = some n at hn
          simp only [Admits] at hadm
          have hta : W.rip t = base + BitVec.ofNat 64 a := by rw [rip_def, hadm, rel_eq hrip, ha]
          have : W.cls (W.rip t) = .image := by
            rcases hx with rfl | rfl
            · exact img_cls hS (fresh (by simp [hT, Term.succs]) hta)
            · exact img_cls hS (inv_target hS hfC hNf hb (by simp [hT, termNodes, tgtNode]) hta).1
          rw [node_jump_img this] at hn; cases hn
        | jmpInd ts w =>
          rw [hT] at hok; obtain ⟨op, hk'⟩ := tok_jmpInd hok
          rw [hk'] at hn
          cases ts with
          | none => exact absurd (node_in hS hfC hNf hb (n := .unresolved) (by simp [hT, termNodes])).1 hS.noUnres
          | some ts =>
            obtain ⟨x, hx, hland⟩ := hS.ind es u t i' l' hrun hk hAt' hstep f C hfC b hb o hrip
              (by omega) ts (by simp [hT, Term.listed])
            change Ev.node W base (.jump (W.J.core t).rip) = some n at hn
            cases x with
            | blk c =>
              have := img_cls hS (fresh (c := c) (by simp [hT, Term.succs]; exact ⟨_, hx, rfl⟩) hland)
              rw [node_jump_img this] at hn; cases hn
            | fn c =>
              have := img_cls hS (inv_target hS hfC hNf hb (c := c)
                (by simp [hT, termNodes]; exact ⟨_, hx, by simp [tgtNode]⟩) hland).1
              rw [node_jump_img this] at hn; cases hn
            | ext r =>
              simp only [Lands] at hland
              rw [node_jump_ent hland] at hn
              simp only [Option.some.injEq] at hn; subst hn
              exact Or.inl (node_in hS hfC hNf hb
                (by simp [hT, termNodes]; exact ⟨_, hx, by simp [tgtNode]⟩)).1
        | call x r =>
          rw [hT] at hok; obtain ⟨d, a, hk', rfl, ha⟩ := tok_call hok
          rw [hk'] at hadm hn
          simp only [Admits] at hadm
          have hta : W.rip t = base + BitVec.ofNat 64 a := by rw [rip_def, hadm.1, rel_eq hrip, ha]
          obtain ⟨hI', hNa, hlt⟩ := inv_target hS hfC hNf hb (c := a) (by simp [hT, termNodes, tgtNode]) hta
          have hc' := img_cls hS hI'
          change Ev.node W base (.call (W.J.core t).rip _) = some n at hn
          rw [node_call_img _ hc', hta, toNat_sub_base base hlt] at hn
          simp only [Option.some.injEq] at hn; subst hn
          exact Or.inl hNa
        | callInd ts w r =>
          rw [hT] at hok; obtain ⟨⟨op, hk'⟩, hcall⟩ := tok_callInd hok
          rw [hk'] at hn
          cases ts with
          | none => exact absurd (node_in hS hfC hNf hb (n := .unresolved) (by simp [hT, termNodes])).1 hS.noUnres
          | some ts =>
            obtain ⟨x, hx, hland⟩ := hS.ind es u t i' l' hrun hk hAt' hstep f C hfC b hb o hrip
              (by omega) ts (by simp [hT, Term.listed])
            change Ev.node W base (.call (W.J.core t).rip _) = some n at hn
            cases x with
            | blk c => simpa [Target.callable] using hcall _ hx
            | fn c =>
              obtain ⟨hI', hNc, hlt⟩ := inv_target hS hfC hNf hb (c := c)
                (by simp [hT, termNodes]; exact ⟨_, hx, by simp [tgtNode]⟩) hland
              have hc' := img_cls hS hI'
              simp only [Lands] at hland
              rw [node_call_img _ hc', hland, toNat_sub_base base hlt] at hn
              simp only [Option.some.injEq] at hn; subst hn
              exact Or.inl hNc
            | ext r' =>
              simp only [Lands] at hland
              rw [node_call_ent _ hland] at hn
              simp only [Option.some.injEq] at hn; subst hn
              exact Or.inl (node_in hS hfC hNf hb
                (by simp [hT, termNodes]; exact ⟨_, hx, by simp [tgtNode]⟩)).1
        | sys m r => rw [hT] at hok; exact absurd (tok_sys hok).1 hk1
        | sysOther r => rw [hT] at hok; exact absurd (tok_sysOther hok).1 hk2
        | ret => rw [hT] at hok; rw [tok_ret hok] at hn; cases hn
        | trap => rw [hT] at hok; rw [tok_trap hok] at hadm; simp [Admits] at hadm
      · rcases hkind with hk' | hk' <;> (rw [hk'] at hn; cases hn)
    · -- the next state
      obtain rfl := Option.some.inj ht'
      clear ht'
      rcases hcase with ⟨hl, hok⟩ | ⟨hl, hkind, fuel', hw'⟩
      · cases hT : b.term with
        | fall m =>
          rw [hT] at hok; obtain ⟨hk', hm⟩ := tok_fall hok
          have hsucc : m ∈ b.term.succs := by simp [hT, Term.succs]
          rcases hk' with hk' | hk'
          · rw [hk'] at hadm; simp only [Admits] at hadm
            exact Or.inr (fresh hsucc (by rw [rip_def, hadm, hnext, hm]))
          · rw [hk'] at hadm; simp only [Admits] at hadm
            rcases hadm with h | h
            · refine Or.inr ⟨f, C, b, fuel, o, v, hfC, hNf, hb, hw, by rw [rip_def, h]; exact hrip, ?_⟩
              have := hrep hk'; rw [this] at hraxok; simp only [RaxOk] at hraxok
              intro n hn; rw [hraxok]; exact hrax n hn
            · exact Or.inr (fresh hsucc (by rw [rip_def, h, hnext, hm]))
        | jcc a m =>
          rw [hT] at hok; obtain ⟨r, hk', ha, hm⟩ := tok_jcc hok
          rw [hk'] at hadm; simp only [Admits] at hadm
          rcases hadm with h | h
          · exact Or.inr (fresh (c := m) (by simp [hT, Term.succs]) (by rw [rip_def, h, hnext, hm]))
          · exact Or.inr (fresh (c := a) (by simp [hT, Term.succs]) (by rw [rip_def, h, rel_eq hrip, ha]))
        | jmp x =>
          rw [hT] at hok; obtain ⟨r, a, hk', hx, ha⟩ := tok_jmp hok
          rw [hk'] at hadm; simp only [Admits] at hadm
          have hta : W.rip t = base + BitVec.ofNat 64 a := by rw [rip_def, hadm, rel_eq hrip, ha]
          rcases hx with rfl | rfl
          · exact Or.inr (fresh (by simp [hT, Term.succs]) hta)
          · exact Or.inr (inv_target hS hfC hNf hb (by simp [hT, termNodes, tgtNode]) hta).1
        | jmpInd ts w =>
          cases ts with
          | none => exact absurd (node_in hS hfC hNf hb (n := .unresolved) (by simp [hT, termNodes])).1 hS.noUnres
          | some ts =>
            obtain ⟨x, hx, hland⟩ := hS.ind es u t i' l' hrun hk hAt hstep f C hfC b hb o hrip
              (by omega) ts (by simp [hT, Term.listed])
            cases x with
            | blk c => exact Or.inr (fresh (c := c) (by simp [hT, Term.succs]; exact ⟨_, hx, rfl⟩) hland)
            | fn c => exact Or.inr (inv_target hS hfC hNf hb (c := c)
                (by simp [hT, termNodes]; exact ⟨_, hx, by simp [tgtNode]⟩) hland).1
            | ext r => simp only [Lands] at hland; exact Or.inl (by rw [hland]; simp)
        | call x r =>
          rw [hT] at hok; obtain ⟨d, a, hk', rfl, ha⟩ := tok_call hok
          rw [hk'] at hadm; simp only [Admits] at hadm
          have hta : W.rip t = base + BitVec.ofNat 64 a := by rw [rip_def, hadm.1, rel_eq hrip, ha]
          exact Or.inr (inv_target hS hfC hNf hb (c := a) (by simp [hT, termNodes, tgtNode]) hta).1
        | callInd ts w r =>
          rw [hT] at hok; obtain ⟨_, hcall⟩ := tok_callInd hok
          cases ts with
          | none => exact absurd (node_in hS hfC hNf hb (n := .unresolved) (by simp [hT, termNodes])).1 hS.noUnres
          | some ts =>
            obtain ⟨x, hx, hland⟩ := hS.ind es u t i' l' hrun hk hAt hstep f C hfC b hb o hrip
              (by omega) ts (by simp [hT, Term.listed])
            cases x with
            | blk c => simpa [Target.callable] using hcall _ hx
            | fn c => exact Or.inr (inv_target hS hfC hNf hb (c := c)
                (by simp [hT, termNodes]; exact ⟨_, hx, by simp [tgtNode]⟩) hland).1
            | ext r' => simp only [Lands] at hland; exact Or.inl (by rw [hland]; simp)
        | sys m r => rw [hT] at hok; exact absurd (tok_sys hok).1 hk1
        | sysOther r => rw [hT] at hok; exact absurd (tok_sysOther hok).1 hk2
        | ret =>
          rw [hT] at hok
          exact inv_landing hS (hS.ret es u t i' l' hrun hk hcls hAt (tok_ret hok) hstep hkt)
        | trap => rw [hT] at hok; rw [tok_trap hok] at hadm; simp [Admits] at hadm
      · have hraxt := rax_step hrax hraxok
        have hw'' : walk D b.term b.start fuel' (o + l') (raxStep D v i') (b.bytes.drop (o + l')) = true := by
          rw [← drop_drop']; exact hw'
        have hnx : W.rip t = base + BitVec.ofNat 64 (b.start + (o + l')) → ImgInv W D base P N t :=
          fun h => ⟨f, C, b, fuel', o + l', _, hfC, hNf, hb, hw'', h, hraxt⟩
        rcases hkind with hk' | hk'
        · rw [hk'] at hadm; simp only [Admits] at hadm
          exact Or.inr (hnx (by rw [rip_def, hadm, hnext, Nat.add_assoc]))
        · rw [hk'] at hadm; simp only [Admits] at hadm
          rcases hadm with h | h
          · refine Or.inr ⟨f, C, b, fuel, o, v, hfC, hNf, hb, hw, by rw [rip_def, h]; exact hrip, ?_⟩
            have := hrep hk'; rw [this] at hraxok; simp only [RaxOk] at hraxok
            intro n hn; rw [hraxok]; exact hrax n hn
          · exact Or.inr (hnx (by rw [rip_def, h, hnext, Nat.add_assoc]))
  | @sys _ t i' l' _ hAt' hk1 hK =>
    obtain ⟨rfl, rfl⟩ := huniq i' l' hAt'
    rcases hcase with ⟨hl, hok⟩ | ⟨_, hkind, _⟩
    · cases hT : b.term with
      | sys m r =>
        rw [hT] at hok
        obtain ⟨_, hr, hm, hlt⟩ := tok_sys hok
        refine ⟨fun n hn => ?_, fun t' ht' _ => ?_⟩
        · change some _ = some n at hn; simp only [Option.some.injEq] at hn; subst hn
          cases m with
          | none =>
            exact Or.inr ⟨⟨_, rfl⟩, (node_in hS hfC hNf hb (n := .sysAny) (by simp [hT, termNodes])).1⟩
          | some k =>
            have hv := hrax k hm.symm
            simp only [Option.getD_some] at hlt
            rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
            exact Or.inl (node_in hS hfC hNf hb (n := .sys k) (by simp [hT, termNodes])).1
        · subst ht'
          have := hS.kernel _ u t' i' l' hAt' (Or.inl hk1) hK
          exact Or.inr (fresh (c := r) (by simp [hT, Term.succs]) (by rw [this, hnext, hr]))
      | _ => (rw [hT] at hok; first
        | exact absurd hk1 (by have := tok_fall hok; rcases this.1 with h | h <;> rw [h] <;> simp)
        | (obtain ⟨_, h, _⟩ := tok_jcc hok; rw [hk1] at h; simp at h)
        | (obtain ⟨_, _, h, _⟩ := tok_jmp hok; rw [hk1] at h; simp at h)
        | (obtain ⟨_, h⟩ := tok_jmpInd hok; rw [hk1] at h; simp at h)
        | (obtain ⟨_, _, h, _⟩ := tok_call hok; rw [hk1] at h; simp at h)
        | (obtain ⟨⟨_, h⟩, _⟩ := tok_callInd hok; rw [hk1] at h; simp at h)
        | (have h := (tok_sysOther hok).1; rw [hk1] at h; simp at h)
        | (have h := tok_ret hok; rw [hk1] at h; simp at h)
        | (have h := tok_trap hok; rw [hk1] at h; simp at h))
    · rcases hkind with h | h <;> rw [hk1] at h <;> simp at h
  | @sysOther _ t i' l' n _ hAt' hk1 hK =>
    obtain ⟨rfl, rfl⟩ := huniq i' l' hAt'
    rcases hcase with ⟨hl, hok⟩ | ⟨_, hkind, _⟩
    · cases hT : b.term with
      | sysOther r =>
        rw [hT] at hok
        obtain ⟨_, hr⟩ := tok_sysOther hok
        refine ⟨fun n hn => ?_, fun t' ht' _ => ?_⟩
        · change some _ = some n at hn; simp only [Option.some.injEq] at hn; subst hn
          exact Or.inl (node_in hS hfC hNf hb (n := .sysAny) (by simp [hT, termNodes])).1
        · subst ht'
          have := hS.kernel _ u t' i' l' hAt' (Or.inr hk1) hK
          exact Or.inr (fresh (c := r) (by simp [hT, Term.succs]) (by rw [this, hnext, hr]))
      | _ => (rw [hT] at hok; first
        | exact absurd hk1 (by have := tok_fall hok; rcases this.1 with h | h <;> rw [h] <;> simp)
        | (obtain ⟨_, h, _⟩ := tok_jcc hok; rw [hk1] at h; simp at h)
        | (obtain ⟨_, _, h, _⟩ := tok_jmp hok; rw [hk1] at h; simp at h)
        | (obtain ⟨_, h⟩ := tok_jmpInd hok; rw [hk1] at h; simp at h)
        | (obtain ⟨_, _, h, _⟩ := tok_call hok; rw [hk1] at h; simp at h)
        | (obtain ⟨⟨_, h⟩, _⟩ := tok_callInd hok; rw [hk1] at h; simp at h)
        | (have h := (tok_sys hok).1; rw [hk1] at h; simp at h)
        | (have h := tok_ret hok; rw [hk1] at h; simp at h)
        | (have h := tok_trap hok; rw [hk1] at h; simp at h))
    · rcases hkind with h | h <;> rw [hk1] at h <;> simp at h

/-- Runs extend by a step. -/
theorem run_snoc {x : Option σ} {es : List Ev} {u : σ} (h : Run W D keep x es (some u))
    (hk : keep u) {e : Ev} {y : Option σ} (hs : Step W D (some u) e y) :
    Run W D keep x (es ++ [e]) y := by
  generalize hz : some u = z at h
  induction h with
  | refl x => subst hz; exact Run.step hk hs (Run.refl _)
  | step hk' hs' _ ih => exact Run.step hk' hs' (ih hz)

/-- Every event of a run from an invariant state is covered. -/
theorem run_ok (hS : Setting W D base P esc entry keep s₀ N) :
    ∀ {x : Option σ} {es₂ : List Ev} {z : Option σ}, Run W D keep x es₂ z →
      ∀ u es₁, x = some u → Run W D keep (some s₀) es₁ (some u) → Inv W D base P N u →
        ∀ e ∈ es₂, ∀ n, e.node W base = some n → Covered N n := by
  intro x es₂ z h
  induction h with
  | refl => intro _ _ _ _ _ e he; simp at he
  | @step s e y es z hk hs hr ih =>
    intro u es₁ hx hrun hI e' he' n hn
    obtain rfl := Option.some.inj hx
    obtain ⟨hcov, hnext⟩ := step_ok hS hrun hk hI hs
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hcov n hn
    · cases hr with
      | refl => simp at he'
      | @step t _ _ _ _ hkt hst hrest =>
        exact ih t (es₁ ++ [e]) rfl (run_snoc hrun hk hs) (hnext t rfl hkt) e' he' n hn

/-- **Soundness.** -/
theorem sound (hS : Setting W D base P esc entry keep s₀ N) : ReachIn W D base keep s₀ N :=
  fun _ _ h => run_ok hS h s₀ [] rfl (Run.refl _) (inv_init hS)

end

end Silmaril.Proofs.Elf.Effects
