module

public import Silmaril.X86.Ext.Loop
public import Silmaril.X86.Ext.SymExec

/-!
# A segment VC generator over any x86 instruction-set variant

`ProgramVC.X86.vc` (projects/smt-axioms) is a cut-point VC generator for one *leaf function* of
the fixed `X86.Ext` machine: the paths end at the `ret` to the designated exit, and calls are
not supported. A driver such as `sha256sum-min`'s `digest_file` needs three generalisations,
which this module makes, and nothing else:

* **Any instruction set and any machine** (`Isa`). The decoder, the executor and the
  one-step function are parameters, related by a single law (`Isa.step_of`): a listed
  instruction that the decoder reads at the program counter and that executes successfully
  is one step of the machine. `Isa.ext exit` is `X86.Ext` with its `stepOpt exit`; an
  ISA variant (for example one with 8-bit ALU forms) or a process machine (the `X86Sys`
  `tau` steps, `Apps/Sha256sum/X86Sys/SegVC.lean`) is another instance, and the generator,
  its soundness proof and its tactic are reused unchanged.
* **Segments**, not only functions. Paths end at *stop* offsets (`stops`), each with its
  own postcondition: the `syscall` sites of a driver, a function's `ret`, the head of an
  enclosing loop. The conclusion is a `Machine.Execution.Reaches` run of the machine, so a
  segment composes with whatever the caller proves about the stop (a system call, a
  return, the next segment).
* **Summaries** (`subs`, entries `(offset, exit offset, summary)`). At a listed offset, a proved sub-segment (for example an inner loop
  proved separately, `Digest.Copy`) is used instead of the instructions: its precondition is
  asked and every state its postcondition allows continues. A `Call` value carries the proof.
* **Contracted calls** (`calls`, entries `(offset, return offset, contract)`). At a listed call offset, the generator executes the call
  instruction but not the callee; it asks for the callee's precondition at the callee's entry
  and continues from every state the callee's postcondition allows. A `Call` carries its own proof that the callee's precondition leads,
  by a run of the same machine, to a state satisfying its postcondition, so the generator
  is sound without knowing anything about the callee's code (for example
  `Binary.compress_contract` through the call bridge `X86Sys.ext_returns_tauRun`).

Cut points (loop heads) carry an invariant and a measure, as in `ProgramVC.X86.vc`: from a cut
point, reaching a cut point again needs a smaller measure, so the generator proves
termination of the segment, not only partial correctness.

`sound`: if the listing is valid (`Listing.valid`, by `decide`) and the VCs hold, every
state at the entry satisfying the precondition reaches some stop, with that stop's
postcondition, the image still loaded, and the machine's `live` invariant.
-/

@[expose] public section

namespace Silmaril.X86.SegVC

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Machine.Execution (run Reaches)

/-- An instruction-set variant and a machine whose steps its listed instructions determine. -/
structure Isa (σ : Type) where
  /-- The instruction syntax of the variant. -/
  Instr : Type
  instDecEq : DecidableEq Instr
  /-- The decoder: an instruction and its length from a byte string. -/
  decode : List Byte → Option (Instr × Nat)
  /-- The executor: one instruction of this length on a core and a memory. -/
  exec : Instr → State → Memory → Nat → Ext.Result
  /-- The core and the memory of a machine state. -/
  core : σ → State
  mem : σ → Memory
  /-- Replace the core and the memory. -/
  upd : σ → State → Memory → σ
  core_upd : ∀ s c m, core (upd s c m) = c
  mem_upd : ∀ s c m, mem (upd s c m) = m
  /-- A side condition on a successful execution (`Isa.ext`: a `ret` does not pop the
  designated exit; `True` for a process machine). -/
  ok : Instr → State → Prop
  /-- An invariant the machine keeps (for a process machine: not faulted). -/
  live : σ → Prop
  /-- The machine. -/
  step : σ → Option σ
  live_step : ∀ {s t}, live s → step s = some t → live t
  /-- **The law.** A listed instruction at the program counter that executes is one step. -/
  step_of : ∀ {s : σ} {base : Word} {code : List Byte} {o l : Nat} {i : Instr} {c : State}
    {m : Memory}, live s → Loaded (mem s) base code → (core s).rip = base + BitVec.ofNat 64 o →
    o + l ≤ code.length → decode ((code.drop o).take l) = some (i, l) →
    exec i (core s) (mem s) l = .ok c m → ok i c → step s = some (upd s c m)

attribute [instance] Isa.instDecEq

variable {σ : Type} (I : Isa σ)

/-- A lifted listing: byte offset ↦ (instruction, encoded length). -/
abbrev Listing := List (Nat × I.Instr × Nat)

/-- Every listed entry is what the variant's decoder reads at its offset. -/
def Listing.valid (code : List Byte) (L : Listing I) : Bool :=
  L.all fun e => decide (I.decode ((code.drop e.1).take e.2.2) = some (e.2.1, e.2.2)) &&
    decide (e.1 + e.2.2 ≤ code.length)

/-- A cut point's annotation. -/
structure Cut where
  inv : σ → Prop
  measure : σ → Nat

/-- A callee's contract, with its proof: from every live state satisfying `pre` (the state
after the call instruction, at the callee's entry), the machine reaches a state satisfying
`post` (after the callee's return). -/
structure Call where
  pre : σ → Prop
  post : σ → σ → Prop
  runs : ∀ s, I.live s → pre s → ∃ t, Reaches I.step s t ∧ post s t

/-- The measure bound on reaching a cut point: none from the entry. -/
def bound (μ : Option Nat) (w : Nat) : Prop :=
  match μ with
  | some μ => w < μ
  | none => True

section

variable (code : List Byte) (L : Listing I) (cuts : List (Nat × Cut (σ := σ)))
  (stops : List (Nat × (σ → Prop))) (calls : List (Nat × Nat × Call I)) (subs : List (Nat × Nat × Call I))
  (base : Word)

/-- The offset of a core's RIP in the image. -/
def offOf (c : State) : Nat := (c.rip - base).toNat

/-- Arriving at offset `o` in state `s`: a cut point's annotation (with the measure bound),
a stop's postcondition, or the paths onward. -/
def nextAt (μ : Option Nat) (cont : Nat → σ → Prop) (o : Nat) (s : σ) : Prop :=
  match cuts.lookup o with
  | some c => c.inv s ∧ bound μ (c.measure s)
  | none =>
    match stops.lookup o with
    | some q => q s
    | none => cont o s

/-- A successful execution satisfies `P`; a fault, a trap or an undefined condition does
not. -/
def onOk (P : State → Memory → Prop) : Ext.Result → Prop
  | .ok c m => P c m
  | _ => False

/-- The weakest precondition of one listed instruction at offset `o`, given what arriving
at the next offset needs (`cont`): it executes, the image stays loaded, and either it
arrives (`nextAt`), or, at a contracted call, the callee's precondition holds at its entry
and every state its postcondition allows arrives. -/
def after (μ : Option Nat) (cont : Nat → σ → Prop) (o : Nat) (i : I.Instr) (s : σ) (c : State)
    (m : Memory) : Prop :=
  I.ok i c ∧ Loaded m base code ∧
    match calls.lookup o with
    | some (o', cl) => cl.pre (I.upd s c m) ∧ ∀ t, cl.post (I.upd s c m) t →
        (I.core t).rip = base + BitVec.ofNat 64 o' ∧ Loaded (I.mem t) base code ∧
          nextAt cuts stops μ cont (o' % 2 ^ 64) t
    | none => nextAt cuts stops μ cont (offOf base c) (I.upd s c m)

def wpI (μ : Option Nat) (cont : Nat → σ → Prop) (o : Nat) : Option (I.Instr × Nat) → σ → Prop
  | some (i, l), s =>
    onOk (after I code cuts stops calls base μ cont o i s) (I.exec i (I.core s) (I.mem s) l)
  | none, _ => False

/-- The weakest precondition of the paths from offset `o`, at most `k` instructions long,
to a cut point or a stop. -/
def wpN (μ : Option Nat) : Nat → Nat → σ → Prop
  | 0, _, _ => False
  | k + 1, o, s =>
    match subs.lookup o with
    | some (o', sb) => sb.pre s ∧ ∀ t, sb.post s t →
        (I.core t).rip = base + BitVec.ofNat 64 o' ∧ Loaded (I.mem t) base code ∧
          nextAt cuts stops μ (wpN μ k) (o' % 2 ^ 64) t
    | none => wpI I code cuts stops calls base μ (wpN μ k) o (L.lookup o) s

/-- The VCs of an annotated segment entered at `entry`: from the entry under the
precondition, and from every cut point under its invariant. -/
def vc (entry : Nat) (pre : σ → Prop) (K : Nat) : Prop :=
  (∀ s, I.live s → Loaded (I.mem s) base code → (I.core s).rip = base + BitVec.ofNat 64 entry →
    pre s → wpN I code L cuts stops calls subs base none K entry s) ∧
  (∀ oc ∈ cuts, ∀ s, I.live s → Loaded (I.mem s) base code →
    (I.core s).rip = base + BitVec.ofNat 64 oc.1 → oc.2.inv s →
    wpN I code L cuts stops calls subs base (some (oc.2.measure s)) K oc.1 s)

/-- What a state reaches: a stop with its postcondition, or a cut point with its
annotation and the measure bound; the image loaded and the machine live. -/
def Arrive (μ : Option Nat) (s : σ) : Prop :=
  (∃ o q t, stops.lookup o = some q ∧ cuts.lookup o = none ∧ q t ∧ Reaches I.step s t ∧
    (I.core t).rip = base + BitVec.ofNat 64 o ∧ Loaded (I.mem t) base code ∧ I.live t) ∨
  (∃ o c t, cuts.lookup o = some c ∧ c.inv t ∧ bound μ (c.measure t) ∧ Reaches I.step s t ∧
    (I.core t).rip = base + BitVec.ofNat 64 o ∧ Loaded (I.mem t) base code ∧ I.live t)

end

variable {I} {code : List Byte} {L : Listing I} {cuts : List (Nat × Cut (σ := σ))}
  {stops : List (Nat × (σ → Prop))} {calls : List (Nat × Nat × Call I)} {subs : List (Nat × Nat × Call I)}
  {base : Word}

theorem rip_offOf (base : Word) (c : State) :
    c.rip = base + BitVec.ofNat 64 (offOf base c) := by
  simp only [offOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

theorem offOf_of_rip {base : Word} {c : State} {o : Nat} (h : c.rip = base + BitVec.ofNat 64 o) :
    offOf base c = o % 2 ^ 64 := by
  have : base + BitVec.ofNat 64 o - base = BitVec.ofNat 64 o := by bv_omega
  simp only [offOf, h, this, BitVec.toNat_ofNat]

theorem reaches_head {s t : σ} (h : I.step s = some t) : Reaches I.step s t :=
  ⟨1, by simp [run, h]⟩

theorem reaches_cons {s t u : σ} (h : I.step s = some t) (r : Reaches I.step t u) :
    Reaches I.step s u :=
  (reaches_head h).trans r

theorem live_reaches {s t : σ} (hl : I.live s) (r : Reaches I.step s t) : I.live t := by
  obtain ⟨n, hn⟩ := r
  induction n generalizing s with
  | zero => cases Option.some.inj hn; exact hl
  | succ n ih =>
    simp only [Silmaril.Machine.Execution.run_succ] at hn
    cases hs : I.step s with
    | none => simp [hs] at hn
    | some mid =>
      simp only [hs, Option.bind_some] at hn
      exact ih (I.live_step hl hs) hn

theorem Arrive.head {μ : Option Nat} {s t : σ} (r : Reaches I.step s t)
    (h : Arrive I code cuts stops base μ t) : Arrive I code cuts stops base μ s := by
  rcases h with ⟨o, q, u, hq, hc, hu, hr, hrip, hl, hlv⟩ | ⟨o, c, u, hc, hi, hb, hr, hrip, hl, hlv⟩
  · exact .inl ⟨o, q, u, hq, hc, hu, r.trans hr, hrip, hl, hlv⟩
  · exact .inr ⟨o, c, u, hc, hi, hb, r.trans hr, hrip, hl, hlv⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (a', b') :: rest, a, b, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      have : a = a' := by simpa [beq_iff_eq] using he
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem valid_entry (hv : L.valid I code = true) {o : Nat} {i : I.Instr} {l : Nat}
    (h : L.lookup o = some (i, l)) :
    I.decode ((code.drop o).take l) = some (i, l) ∧ o + l ≤ code.length := by
  have := List.all_eq_true.mp hv _ (lookup_mem h)
  simpa using this

/-- Arriving at a state that `nextAt` accepts, with the image loaded and the machine live. -/
theorem arrive_next {μ : Option Nat} {k : Nat}
    (ih : ∀ (o : Nat) (s : σ), wpN I code L cuts stops calls subs base μ k o s → I.live s →
      Loaded (I.mem s) base code → (I.core s).rip = base + BitVec.ofNat 64 o →
      Arrive I code cuts stops base μ s)
    {s : σ} (h : nextAt cuts stops μ (wpN I code L cuts stops calls subs base μ k)
      (offOf base (I.core s)) s)
    (hlv : I.live s) (hl : Loaded (I.mem s) base code) :
    Arrive I code cuts stops base μ s := by
  unfold nextAt at h
  cases hc : cuts.lookup (offOf base (I.core s)) with
  | some c =>
    rw [hc] at h
    exact .inr ⟨_, c, s, hc, h.1, h.2, .refl _ _, rip_offOf base _, hl, hlv⟩
  | none =>
    rw [hc] at h
    simp only at h
    cases hq : stops.lookup (offOf base (I.core s)) with
    | some q =>
      rw [hq] at h
      exact .inl ⟨_, q, s, hq, hc, h, .refl _ _, rip_offOf base _, hl, hlv⟩
    | none =>
      rw [hq] at h
      exact ih _ _ h hlv hl (rip_offOf base _)

/-- **Paths**: `wpN` at offset `o`, with the image loaded and the machine live, arrives at
a stop or a cut point. -/
theorem path (hv : L.valid I code = true) (μ : Option Nat) :
    ∀ (k o : Nat) (s : σ), wpN I code L cuts stops calls subs base μ k o s → I.live s →
      Loaded (I.mem s) base code → (I.core s).rip = base + BitVec.ofNat 64 o →
      Arrive I code cuts stops base μ s := by
  intro k
  induction k with
  | zero => intro o s h; exact absurd h id
  | succ k ih =>
    intro o s h hlv hl hrip
    simp only [wpN] at h
    cases hsb : subs.lookup o with
    | some osb =>
      obtain ⟨o', sb⟩ := osb
      rw [hsb] at h
      obtain ⟨hpre, hpost⟩ := h
      obtain ⟨t, hr, ht⟩ := sb.runs s hlv hpre
      obtain ⟨hrip', hl', hn⟩ := hpost t ht
      rw [← offOf_of_rip hrip'] at hn
      exact Arrive.head hr (arrive_next ih hn (live_reaches hlv hr) hl')
    | none =>
    rw [hsb] at h
    simp only at h
    cases hi : L.lookup o with
    | none => rw [hi] at h; exact h.elim
    | some il =>
      obtain ⟨i, l⟩ := il
      rw [hi] at h
      obtain ⟨hdec, hfit⟩ := valid_entry hv hi
      simp only [wpI] at h
      cases hx : I.exec i (I.core s) (I.mem s) l with
      | ok c m =>
        rw [hx] at h
        simp only [onOk] at h
        obtain ⟨hok, hl', hn⟩ := h
        have hs := I.step_of hlv hl hrip hfit hdec hx hok
        have hlv' := I.live_step hlv hs
        cases hcl : calls.lookup o with
        | some ocl =>
          obtain ⟨o', cl⟩ := ocl
          rw [hcl] at hn
          obtain ⟨hpre, hpost⟩ := hn
          obtain ⟨t, hr, ht⟩ := cl.runs _ hlv' hpre
          obtain ⟨hrip', hl'', hn⟩ := hpost t ht
          rw [← offOf_of_rip hrip'] at hn
          exact Arrive.head (reaches_cons hs hr) (arrive_next ih hn (live_reaches hlv' hr) hl'')
        | none =>
          rw [hcl] at hn
          simp only at hn
          have ho : offOf base c = offOf base (I.core (I.upd s c m)) := by rw [I.core_upd]
          rw [ho] at hn
          rw [← I.mem_upd s c m] at hl'
          exact Arrive.head (reaches_head hs) (arrive_next ih hn hlv' hl')
      | dataFault => rw [hx] at h; exact h.elim
      | divideError => rw [hx] at h; exact h.elim
      | undefinedCondition _ => rw [hx] at h; exact h.elim
      | trap => rw [hx] at h; exact h.elim

/-- The conclusion of a segment: some stop is reached, with its postcondition. -/
def Stops (I : Isa σ) (code : List Byte) (stops : List (Nat × (σ → Prop))) (base : Word) (s : σ) : Prop :=
  ∃ o q t, stops.lookup o = some q ∧ q t ∧ Reaches I.step s t ∧
    (I.core t).rip = base + BitVec.ofNat 64 o ∧ Loaded (I.mem t) base code ∧ I.live t

theorem Stops.head {s t : σ} (r : Reaches I.step s t) (h : Stops I code stops base t) :
    Stops I code stops base s := by
  obtain ⟨o, q, u, hq, hu, hr, hrip, hl, hlv⟩ := h
  exact ⟨o, q, u, hq, hu, r.trans hr, hrip, hl, hlv⟩

/-- From a cut point whose annotation holds, some stop is reached. -/
theorem from_cut (hv : L.valid I code = true) {entry : Nat} {pre : σ → Prop} {K : Nat}
    (hvc : vc I code L cuts stops calls subs base entry pre K) :
    ∀ (w o : Nat) (c : Cut) (s : σ), c.measure s = w → cuts.lookup o = some c → c.inv s →
      I.live s → Loaded (I.mem s) base code → (I.core s).rip = base + BitVec.ofNat 64 o →
      Stops I code stops base s := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro o c s hw hc hinv hlv hl hrip
    have hp := hvc.2 (o, c) (lookup_mem hc) s hlv hl hrip hinv
    rcases path hv _ K o s hp hlv hl hrip with ⟨o', q, t, hq, _, ht, hr, hrip', hl', hlv'⟩ |
        ⟨o', c', t, hc', hi', hb, hr, hrip', hl', hlv'⟩
    · exact ⟨o', q, t, hq, ht, hr, hrip', hl', hlv'⟩
    · simp only [bound] at hb
      exact Stops.head hr (ih _ (hw ▸ hb) o' c' t rfl hc' hi' hlv' hl' hrip')

/-- **Soundness of the segment VC generator.** If the listing is valid and the VCs hold,
every live state at the entry with the image loaded and the precondition true reaches a
stop, with that stop's postcondition. -/
theorem sound (hv : L.valid I code = true) {entry : Nat} {pre : σ → Prop} {K : Nat}
    (hvc : vc I code L cuts stops calls subs base entry pre K) (s : σ) (hlv : I.live s)
    (hl : Loaded (I.mem s) base code) (hrip : (I.core s).rip = base + BitVec.ofNat 64 entry)
    (hpre : pre s) : Stops I code stops base s := by
  have hp := hvc.1 s hlv hl hrip hpre
  rcases path hv _ K entry s hp hlv hl hrip with ⟨o', q, t, hq, _, ht, hr, hrip', hl', hlv'⟩ |
      ⟨o', c', t, hc', hi', _, hr, hrip', hl', hlv'⟩
  · exact ⟨o', q, t, hq, ht, hr, hrip', hl', hlv'⟩
  · exact Stops.head hr (from_cut hv hvc _ o' c' t rfl hc' hi' hlv' hl' hrip')

/-- With a single stop, the conclusion is a run into that stop's postcondition. -/
theorem sound_one {o : Nat} {q : σ → Prop} (hv : L.valid I code = true) {entry : Nat}
    {pre : σ → Prop} {K : Nat} (hvc : vc I code L cuts [(o, q)] calls subs base entry pre K) (s : σ)
    (hlv : I.live s) (hl : Loaded (I.mem s) base code)
    (hrip : (I.core s).rip = base + BitVec.ofNat 64 entry) (hpre : pre s) :
    ∃ t, Reaches I.step s t ∧ q t ∧ (I.core t).rip = base + BitVec.ofNat 64 o ∧
      Loaded (I.mem t) base code ∧ I.live t := by
  obtain ⟨o', q', t, hq, ht, hr, hrip', hl', hlv'⟩ := sound hv hvc s hlv hl hrip hpre
  simp only [List.lookup_cons, List.lookup_nil] at hq
  split at hq
  · rename_i he
    cases hq
    have : o' = o := by simpa [beq_iff_eq] using he
    subst this
    exact ⟨t, hr, ht, hrip', hl', hlv'⟩
  · cases hq

/-! ## The `X86.Ext` instance

`Isa.ext exit` is the fixed extended machine with designated exit `exit`: its steps are
`Ext.stepOpt exit`. A `ret` is an ordinary step unless it pops `exit` (then the function
has returned, which `ok` excludes inside a segment). -/

/-- An instance whose instructions, decoder and executor are `X86.Ext`'s. -/
@[reducible] def Isa.ofExt (core : σ → State) (mem : σ → Memory) (upd : σ → State → Memory → σ)
    (core_upd : ∀ s c m, core (upd s c m) = c) (mem_upd : ∀ s c m, mem (upd s c m) = m)
    (ok : Ext.Instr → State → Prop) (live : σ → Prop) (step : σ → Option σ)
    (live_step : ∀ {s t}, live s → step s = some t → live t)
    (step_of : ∀ {s : σ} {base : Word} {code : List Byte} {o l : Nat} {i : Ext.Instr} {c : State}
      {m : Memory}, live s → Loaded (mem s) base code → (core s).rip = base + BitVec.ofNat 64 o →
      o + l ≤ code.length → Ext.decode ((code.drop o).take l) = some (i, l) →
      Ext.exec i (core s) (mem s) l = .ok c m → ok i c → step s = some (upd s c m)) : Isa σ where
  Instr := Ext.Instr
  instDecEq := inferInstance
  decode := Ext.decode
  exec := fun i s m l => Ext.exec i s m l
  core := core
  mem := mem
  upd := upd
  core_upd := core_upd
  mem_upd := mem_upd
  ok := ok
  live := live
  step := step
  live_step := live_step
  step_of := step_of

/-- `X86.Ext` with designated exit `exit`. -/
@[reducible] def Isa.ext (exit : Word) : Isa MState :=
  Isa.ofExt MState.core MState.memory (fun _ c m => ⟨c, m⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun i c => ¬ (i = .ret ∧ c.rip = exit)) (fun _ => True) (Ext.stepOpt exit)
    (fun _ _ => trivial) (by
      intro s base code o l i c m _ hl hrip hfit hdec hx hok
      have hlen : l = i.length := (Ext.decode_length hdec).1
      subst hlen
      rw [Ext.stepOpt_eq_some_iff, Ext.step_of_loaded hl hrip hfit hdec]
      rw [hx]
      simp only [hok, ite_false])

/-- A run of `Isa.ext exit` is an `Ext.Reaches` run. -/
theorem ext_reaches {exit : Word} {s t : MState} (h : Reaches (Isa.ext exit).step s t) :
    Ext.Reaches exit s t := h

end Silmaril.X86.SegVC
