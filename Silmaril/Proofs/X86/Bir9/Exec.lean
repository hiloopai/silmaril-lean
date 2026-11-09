module

public import Silmaril.Proofs.X86.Bir9.Ir

/-!
# Symbolic execution into Bir, proved once

`symExec` runs a straight-line list of `LInstr`s symbolically and returns the
`Block` it denotes; `symExec_sound` says that whenever it succeeds, the
machine and the block agree on *every* entry state and memory:

```
symExec instrs = some b → execBlock instrs s mem = b.run s mem
```

That is the whole block-simulation certificate. A lifted function is a list
of blocks with their listings; its certificate is `symExec listing = some b`
for each block, closed by kernel reduction (`decide`). Nothing about how a
block was proposed is trusted: if a wrong one is proposed, the equation fails.

The proof mirrors `Silmaril.X86.Ext.exec`'s own helper structure (`readRM`, `writeRM`,
`writeNarrow`, `writeRM8`, `retire`, `pushWord`, `popWord`): each symbolic
helper has a lemma, and each instruction is an assembly of them.

Unsupported instructions make `symExec` return `none`: `adc`/`sbb`, `alu16R`,
`Ext9.testI8` and `Ext9.bt`. Division, wide products and bit scans go through the operator
constructors `E.xop`, `F.xop` and `Stmt.chk`.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## Scoping -/

/-- Every `E.v i` in the expression has `i < n`. -/
def E.wf (n : Nat) : E → Prop
  | .reg _ | .rip | .fs | .imm _ | .xmm _ _ => True
  | .v i => i < n
  | .add a b | .sub a b | .alu _ _ a b | .mul _ a b | .shift _ _ a b | .merge _ a b =>
    a.wf n ∧ b.wf n
  | .shl a _ | .zext _ a | .sext _ a | .neg _ a | .not _ a | .bswap _ a | .bitcount _ _ a
  | .signmask _ a => a.wf n
  | .sel b x y | .xop _ b x y => b.wf n ∧ x.wf n ∧ y.wf n

def F.wf (n : Nat) : F → Prop
  | .entry | .undef => True
  | .alu _ _ a b | .imul _ a b | .test _ a b => a.wf n ∧ b.wf n
  | .logic _ a | .neg _ a | .bitcount _ _ a => a.wf n
  | .inc _ a o | .dec _ a o => a.wf n ∧ o.wf n
  | .shift _ _ a c o | .bt a c o => a.wf n ∧ c.wf n ∧ o.wf n
  | .xop _ a b c => a.wf n ∧ b.wf n ∧ c.wf n

theorem E.wf_mono {n m : Nat} (h : n ≤ m) : ∀ {e : E}, e.wf n → e.wf m := by
  intro e
  induction e <;> simp only [E.wf] <;> first | omega | (intros; trivial) | aesop

theorem F.wf_mono {n m : Nat} (h : n ≤ m) : ∀ {f : F}, f.wf n → f.wf m := by
  intro f
  induction f <;> simp only [F.wf] <;>
    first | (intros; trivial) | (intro h'; exact E.wf_mono h h') |
      (rintro ⟨a, b⟩; exact ⟨E.wf_mono h a, E.wf_mono h b⟩) | aesop (add safe E.wf_mono)

/-- `env'` extends `env`: same entry state, values a prefix. -/
def Env.Ext (env env' : Env) : Prop := env'.s0 = env.s0 ∧ env'.x0 = env.x0 ∧ env.vals <+: env'.vals

theorem Env.Ext.refl (env : Env) : env.Ext env := ⟨rfl, rfl, List.prefix_refl _⟩

theorem Env.Ext.trans {a b c : Env} (h₁ : a.Ext b) (h₂ : b.Ext c) : a.Ext c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₁.2.2.trans h₂.2.2⟩

theorem E.den_ext {env env' : Env} (hx : env.Ext env') :
    ∀ {e : E}, e.wf env.vals.length → e.den env' = e.den env := by
  intro e
  induction e with
  | reg r => intro _; simp [E.den, hx.1]
  | rip => intro _; simp [E.den, hx.1]
  | fs => intro _; simp [E.den, hx.1]
  | v i =>
    intro h
    simp only [E.wf] at h
    obtain ⟨t, ht⟩ := hx.2.2
    simp only [E.den, ← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  | imm w => intro _; rfl
  | add a b iha ihb => intro h; simp only [E.den, iha h.1, ihb h.2]
  | sub a b iha ihb => intro h; simp only [E.den, iha h.1, ihb h.2]
  | shl a k ih => intro h; simp only [E.den, ih h]
  | zext w a ih => intro h; simp only [E.den, ih h]
  | sext w a ih => intro h; simp only [E.den, ih h]
  | alu w op a b iha ihb => intro h; simp only [E.den, iha h.1, ihb h.2]
  | neg w a ih => intro h; simp only [E.den, ih h]
  | not w a ih => intro h; simp only [E.den, ih h]
  | mul w a b iha ihb => intro h; simp only [E.den, iha h.1, ihb h.2]
  | shift w op a c iha ihc => intro h; simp only [E.den, iha h.1, ihc h.2]
  | merge n a b iha ihb => intro h; simp only [E.den, iha h.1, ihb h.2]
  | sel b x y ihb ihx ihy => intro h; simp only [E.den, ihb h.1, ihx h.2.1, ihy h.2.2]
  | bswap sz a ih => intro h; simp only [E.den, ih h]
  | bitcount op w a ih => intro h; simp only [E.den, ih h]
  | signmask w a ih => intro h; simp only [E.den, ih h]
  | xmm i hi => intro _; simp [E.den, hx.2.1]
  | xop o a b c iha ihb ihc => intro h; simp only [E.den, iha h.1, ihb h.2.1, ihc h.2.2]

theorem F.den_ext {env env' : Env} (hx : env.Ext env') :
    ∀ {f : F}, f.wf env.vals.length → f.den env' = f.den env := by
  intro f
  induction f with
  | entry => intro _; simp [F.den, hx.1]
  | undef => intro _; rfl
  | alu w op a b => intro h; simp only [F.den, E.den_ext hx h.1, E.den_ext hx h.2]
  | test w a b => intro h; simp only [F.den, E.den_ext hx h.1, E.den_ext hx h.2]
  | imul w a b => intro h; simp only [F.den, E.den_ext hx h.1, E.den_ext hx h.2]
  | logic w a => intro h; simp only [F.den, E.den_ext hx h]
  | neg w a => intro h; simp only [F.den, E.den_ext hx h]
  | bitcount op w a => intro h; simp only [F.den, E.den_ext hx h]
  | inc w a o ih => intro h; simp only [F.den, E.den_ext hx h.1, ih h.2]
  | dec w a o ih => intro h; simp only [F.den, E.den_ext hx h.1, ih h.2]
  | shift w op a c o ih =>
    intro h; simp only [F.den, E.den_ext hx h.1, E.den_ext hx h.2.1, ih h.2.2]
  | bt a c o ih => intro h; simp only [F.den, E.den_ext hx h.1, E.den_ext hx h.2.1, ih h.2.2]
  | xop o a b c =>
    intro h; simp only [F.den, E.den_ext hx h.1, E.den_ext hx h.2.1, E.den_ext hx h.2.2]

theorem Stmt.run_ext {st : Stmt} {env env' : Env} (h : st.run env = .ok env') : env.Ext env' := by
  cases st <;> simp only [Stmt.run] at h <;> (try split at h) <;>
    first
    | (cases h; exact ⟨rfl, rfl, List.prefix_append _ _⟩)
    | (cases h; exact ⟨rfl, rfl, List.prefix_refl _⟩)
    | cases h

theorem runStmts_ext : ∀ {sts : List Stmt} {env env' : Env}, runStmts sts env = .ok env' → env.Ext env'
  | [], env, env', h => by cases h; exact Env.Ext.refl _
  | st :: rest, env, env', h => by
    simp only [runStmts] at h
    split at h
    · cases h
    · rename_i e he
      exact (Stmt.run_ext he).trans (runStmts_ext h)

/-! ## Symbolic states and the simulation relation -/

def SState.WF (σ : SState) : Prop := (∀ r, (σ.regs r).wf σ.n) ∧ σ.flags.wf σ.n ∧ σ.rip.wf σ.n

/-- `σ` describes the concrete `s` and `mem` in `env`. -/
structure Rel (σ : SState) (env : Env) (s : State) (mem : Memory) : Prop where
  mem : env.mem = mem
  len : env.vals.length = σ.n
  regs : ∀ r, s.read r = (σ.regs r).den env
  flags : s.flags = σ.flags.den env
  rip : s.rip = σ.rip.den env
  fs : s.fsBase = env.s0.fsBase
  wf : σ.WF

/-- How a symbolic computation of an `Option (State × Memory)` relates. -/
def ORel (env : Env) (o : Option (State × Memory)) (sts : List Stmt) (σ' : SState) : Prop :=
  match o with
  | none => runStmts sts env = .error .data
  | some (s', m') => ∃ env', runStmts sts env = .ok env' ∧ Rel σ' env' s' m'

/-- How a symbolic instruction relates to the machine's result. -/
def StepRel (r : Result) (x : Except Fault Env) (σ' : SState) : Prop :=
  match r, x with
  | .ok s' m', .ok env' => Rel σ' env' s' m'
  | r, .error f => r = f.toResult
  | _, _ => False

/-! ## Effective addresses -/

theorem addImm_den (env : Env) (e : E) (k : Word) : (addImm e k).den env = e.den env + k := by
  unfold addImm
  split <;> simp [E.den, BitVec.add_assoc]

theorem addImm_wf {n : Nat} {e : E} (h : e.wf n) (k : Word) : (addImm e k).wf n := by
  unfold addImm
  split
  · simp_all [E.wf]
  · simp_all [E.wf]

theorem sAddr_den {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {nx : E} {next : Word} (hnx : nx.den env = next) (m : Mem) :
    (sAddr σ nx m).den env = m.addr s next := by
  obtain ⟨base, index, disp, _⟩ := m
  simp only [sAddr, Mem.addr, E.den]
  congr 2
  · cases base <;> simp [E.den, Base.value, h.regs, hnx, h.fs]
  · cases index <;> simp [E.den, Index.value, h.regs]

theorem sAddr_wf {σ : SState} {nx : E} (hσ : σ.WF) (hnx : nx.wf σ.n) (m : Mem) :
    (sAddr σ nx m).wf σ.n := by
  obtain ⟨base, index, disp, _⟩ := m
  simp only [sAddr, E.wf]
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · cases base <;> simp [E.wf, hσ.1, hnx]
  · cases index <;> simp [E.wf, hσ.1]

/-! ## Relation lemmas -/

theorem Rel.ext {σ : SState} {env env' : Env} {s : State} {mem : Memory}
    (h : Rel σ env s mem) (hx : env.Ext env') (hlen : env'.vals.length = σ.n) (hm : env'.mem = mem) :
    Rel σ env' s mem where
  mem := hm
  len := hlen
  regs r := by rw [h.regs r, E.den_ext hx (h.len ▸ h.wf.1 r)]
  flags := by rw [h.flags, F.den_ext hx (h.len ▸ h.wf.2.1)]
  rip := by rw [h.rip, E.den_ext hx (h.len ▸ h.wf.2.2)]
  fs := by rw [h.fs, hx.1]
  wf := h.wf

theorem SState.WF.fresh {σ : SState} (h : σ.WF) : σ.fresh.WF :=
  ⟨fun r => E.wf_mono (Nat.le_succ _) (h.1 r), F.wf_mono (Nat.le_succ _) h.2.1,
    E.wf_mono (Nat.le_succ _) h.2.2⟩

theorem Env.ext_push (env : Env) (w : Word) : env.Ext (env.push w) := ⟨rfl, rfl, List.prefix_append _ _⟩

theorem Rel.push {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (w : Word) : Rel σ.fresh (env.push w) s mem where
  mem := h.mem
  len := by simp [Env.push, h.len, SState.fresh]
  regs r := by rw [h.regs r]; exact (E.den_ext (env.ext_push w) (h.len ▸ h.wf.1 r)).symm
  flags := by rw [h.flags]; exact (F.den_ext (env.ext_push w) (h.len ▸ h.wf.2.1)).symm
  rip := by rw [h.rip]; exact (E.den_ext (env.ext_push w) (h.len ▸ h.wf.2.2)).symm
  fs := h.fs
  wf := h.wf.fresh

theorem Rel.store {σ : SState} {env : Env} {s : State} {mem m' : Memory} (h : Rel σ env s mem) :
    Rel σ { env with mem := m' } s m' where
  mem := rfl
  len := h.len
  regs r := by rw [h.regs r]; exact (E.den_ext (env := env) (env' := { env with mem := m' }) ⟨rfl, rfl, List.prefix_refl _⟩ (by rw [h.len]; exact h.wf.1 r)).symm
  flags := by rw [h.flags]; exact (F.den_ext (env := env) (env' := { env with mem := m' }) ⟨rfl, rfl, List.prefix_refl _⟩ (by rw [h.len]; exact h.wf.2.1)).symm
  rip := by rw [h.rip]; exact (E.den_ext (env := env) (env' := { env with mem := m' }) ⟨rfl, rfl, List.prefix_refl _⟩ (by rw [h.len]; exact h.wf.2.2)).symm
  fs := h.fs
  wf := h.wf

theorem Rel.setReg {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (r : Reg) (e : E) (he : e.wf σ.n) :
    Rel (σ.setReg r e) env (s.write r (e.den env)) mem where
  mem := h.mem
  len := h.len
  regs q := by
    by_cases hq : q = r
    · subst hq; simp [SState.setReg]
    · simp [SState.setReg, hq, h.regs q]
  flags := h.flags
  rip := h.rip
  fs := h.fs
  wf := ⟨fun q => by by_cases hq : q = r <;> simp [SState.setReg, hq, he, h.wf.1 q], h.wf.2⟩

theorem Rel.setFlags {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (f : F) (hf : f.wf σ.n) :
    Rel { σ with flags := f } env { s with flags := f.den env } mem :=
  { h with flags := rfl, wf := ⟨h.wf.1, hf, h.wf.2.2⟩ }

theorem Rel.setRip {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    (e : E) (he : e.wf σ.n) :
    Rel { σ with rip := e } env { s with rip := e.den env } mem :=
  { h with rip := rfl, wf := ⟨h.wf.1, h.wf.2.1, he⟩ }

/-! ## Symbolic helpers mirroring `Silmaril.X86.Ext.exec`'s -/

/-- The raw word an `r/m` read of `k` bytes sees, before truncation. -/
def rawRead (op : RM) (s : State) (mem : Memory) (next : Word) (k : Nat) : Option Word :=
  match op with
  | .reg r => some (s.read r)
  | .mem m => loadN mem (m.addr s next) k

theorem readRM_eq (sz : Sz) (op : RM) (s : State) (mem : Memory) (next : Word) :
    readRM sz op s mem next = (rawRead op s mem next sz.bytes).map (·.setWidth sz.bits) := by
  cases op <;> rfl

theorem readNarrow_eq (n : Narrow) (op : RM) (s : State) (mem : Memory) (next : Word) :
    readNarrow n op s mem next = (rawRead op s mem next n.bytes).map (·.setWidth n.bits) := by
  cases op <;> rfl

theorem writeRM8_eq (op : RM) (v : BitVec 8) (s : State) (mem : Memory) (next : Word) :
    writeRM8 op v s mem next = writeNarrow .b op v s mem next := by
  cases op <;> rfl

/-- What a successful symbolic read gives. -/
structure ReadOK (σ σ' : SState) (env env' : Env) (s : State) (mem : Memory) (e : E) : Prop where
  rel : Rel σ' env' s mem
  ext : env.Ext env'
  wf : e.wf σ'.n
  len : env.vals.length ≤ env'.vals.length
  regs : σ'.regs = σ.regs
  flags : σ'.flags = σ.flags
  rip : σ'.rip = σ.rip

theorem sRead_none {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {nx : E} {next : Word} (hnx : nx.den env = next) {op : RM} {k : Nat}
    (hr : rawRead op s mem next k = none) : runStmts (sRead σ nx k op).1 env = .error .data := by
  cases op with
  | reg r => cases hr
  | mem m =>
    simp only [rawRead] at hr
    simp [sRead, runStmts, Stmt.run, sAddr_den h hnx m, h.mem, hr]

theorem sRead_some {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {nx : E} {next : Word} (hnx : nx.den env = next) {op : RM} {k : Nat} {x : Word}
    (hr : rawRead op s mem next k = some x) :
    ∃ env', runStmts (sRead σ nx k op).1 env = .ok env' ∧
      ReadOK σ (sRead σ nx k op).2.2 env env' s mem (sRead σ nx k op).2.1 ∧
      x = (sRead σ nx k op).2.1.den env' := by
  cases op with
  | reg r =>
    cases hr
    exact ⟨env, rfl, ⟨h, Env.Ext.refl _, h.wf.1 r, le_refl _, rfl, rfl, rfl⟩, h.regs r⟩
  | mem m =>
    simp only [rawRead] at hr
    refine ⟨env.push x, by simp [sRead, runStmts, Stmt.run, sAddr_den h hnx m, h.mem, hr],
      ⟨h.push x, env.ext_push x, ?_, by simp [Env.push], rfl, rfl, rfl⟩, ?_⟩
    · simp [sRead, E.wf, SState.fresh]
    · simp [sRead, E.den, Env.push, h.len]

/-! ## Composition lemmas -/

theorem Env.Ext.len {env env' : Env} (h : env.Ext env') : env.vals.length ≤ env'.vals.length :=
  h.2.2.length_le

theorem ORel.pure {env : Env} {σ' : SState} {s' : State} {m' : Memory} (h : Rel σ' env s' m') :
    ORel env (some (s', m')) [] σ' := ⟨env, rfl, h⟩

theorem ORel.prepend {env env1 : Env} {s1 s2 : List Stmt} {o : Option (State × Memory)}
    {σ' : SState} (h1 : runStmts s1 env = .ok env1) (h : ORel env1 o s2 σ') :
    ORel env o (s1 ++ s2) σ' := by
  cases o with
  | none => simp only [ORel, runStmts_append, h1] at h ⊢; exact h
  | some p =>
    obtain ⟨env', h2, hr⟩ := h
    exact ⟨env', by rw [runStmts_append, h1]; exact h2, hr⟩

theorem StepRel.prepend {env env1 : Env} {s1 s2 : List Stmt} {r : Result} {σ' : SState}
    (h1 : runStmts s1 env = .ok env1) (h : StepRel r (runStmts s2 env1) σ') :
    StepRel r (runStmts (s1 ++ s2) env) σ' := by
  rw [runStmts_append, h1]; exact h

theorem StepRel.fault {env : Env} {sts : List Stmt} {σ' : SState} {f : Fault}
    (h : runStmts sts env = .error f) : StepRel f.toResult (runStmts sts env) σ' := by
  rw [h]; cases f <;> rfl

theorem ORel.flags {env : Env} {o : Option (State × Memory)} {sts : List Stmt} {σ' : SState}
    (h : ORel env o sts σ') (f : F) (hf : f.wf env.vals.length) :
    ORel env (o.map fun r => ({ r.1 with flags := f.den env }, r.2)) sts { σ' with flags := f } := by
  cases o with
  | none => exact h
  | some p =>
    obtain ⟨s', m'⟩ := p
    obtain ⟨env', h2, hr⟩ := h
    have hx := runStmts_ext h2
    refine ⟨env', h2, ?_⟩
    have := hr.setFlags f (hr.len ▸ F.wf_mono hx.len hf)
    rwa [F.den_ext hx hf] at this

theorem ORel.retire {env : Env} {o : Option (State × Memory)} {sts : List Stmt} {σ' : SState}
    (h : ORel env o sts σ') {nx : E} {next : Word} (hnx : nx.den env = next)
    (hw : nx.wf env.vals.length) :
    StepRel (retire next o) (runStmts sts env) { σ' with rip := nx } := by
  cases o with
  | none => exact StepRel.fault h
  | some p =>
    obtain ⟨s', m'⟩ := p
    obtain ⟨env', h2, hr⟩ := h
    have hx := runStmts_ext h2
    simp only [StepRel, h2]
    have := hr.setRip nx (hr.len ▸ E.wf_mono hx.len hw)
    rwa [E.den_ext hx hw, hnx] at this

@[simp] theorem sWriteRM_flags (σ : SState) (nx : E) (sz : Sz) (op : RM) (e : E) :
    (sWriteRM σ nx sz op e).2.flags = σ.flags := by cases op <;> rfl
@[simp] theorem sWriteRM_rip (σ : SState) (nx : E) (sz : Sz) (op : RM) (e : E) :
    (sWriteRM σ nx sz op e).2.rip = σ.rip := by cases op <;> rfl
@[simp] theorem sWriteRM_n (σ : SState) (nx : E) (sz : Sz) (op : RM) (e : E) :
    (sWriteRM σ nx sz op e).2.n = σ.n := by cases op <;> rfl
@[simp] theorem sWriteN_flags (σ : SState) (nx : E) (n : Narrow) (op : RM) (e : E) :
    (sWriteN σ nx n op e).2.flags = σ.flags := by cases op <;> rfl
@[simp] theorem sWriteN_rip (σ : SState) (nx : E) (n : Narrow) (op : RM) (e : E) :
    (sWriteN σ nx n op e).2.rip = σ.rip := by cases op <;> rfl
@[simp] theorem sWriteN_n (σ : SState) (nx : E) (n : Narrow) (op : RM) (e : E) :
    (sWriteN σ nx n op e).2.n = σ.n := by cases op <;> rfl

theorem sWriteRM_sound {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {nx : E} {next : Word} (hnx : nx.den env = next) (_hnxw : nx.wf σ.n) (sz : Sz) (op : RM)
    {e : E} (he : e.wf σ.n) :
    ORel env (writeRM sz op ((e.den env).setWidth sz.bits) s mem next)
      (sWriteRM σ nx sz op e).1 (sWriteRM σ nx sz op e).2 := by
  cases op with
  | reg r =>
    exact ORel.pure (h.setReg r _ (by simpa [E.wf] using he))
  | mem m =>
    simp only [writeRM, sWriteRM, ORel]
    cases hs : storeN mem (m.addr s next) sz.bytes (((e.den env).setWidth sz.bits).setWidth 64) with
    | none =>
      simp [runStmts, Stmt.run, sAddr_den h hnx m, h.mem, E.den, hs]
    | some m' =>
      exact ⟨{ env with mem := m' }, by simp [runStmts, Stmt.run, sAddr_den h hnx m, h.mem, E.den, hs],
        h.store⟩

theorem sWriteN_sound {σ : SState} {env : Env} {s : State} {mem : Memory} (h : Rel σ env s mem)
    {nx : E} {next : Word} (hnx : nx.den env = next) (_hnxw : nx.wf σ.n) (n : Narrow) (op : RM)
    {e : E} (he : e.wf σ.n) :
    ORel env (writeNarrow n op ((e.den env).setWidth n.bits) s mem next)
      (sWriteN σ nx n op e).1 (sWriteN σ nx n op e).2 := by
  cases op with
  | reg r =>
    have := h.setReg r (.merge n (σ.regs r) e) (by simp [E.wf, he, h.wf.1 r])
    simp only [E.den, ← h.regs r] at this
    exact ORel.pure this
  | mem m =>
    simp only [writeNarrow, sWriteN, ORel]
    cases hs : storeN mem (m.addr s next) n.bytes (((e.den env).setWidth n.bits).setWidth 64) with
    | none =>
      simp [runStmts, Stmt.run, sAddr_den h hnx m, h.mem, E.den, hs]
    | some m' =>
      exact ⟨{ env with mem := m' }, by simp [runStmts, Stmt.run, sAddr_den h hnx m, h.mem, E.den, hs],
        h.store⟩

end Silmaril.X86.Bir9
