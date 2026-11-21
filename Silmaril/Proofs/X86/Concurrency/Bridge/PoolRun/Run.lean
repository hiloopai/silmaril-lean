module

public import Silmaril.X86.Concurrency.Bridge.PoolRun.Defs
public import Silmaril.X86.Pool.Thms

/-!
# The recorded TSO pool run is a run of the store-buffer machine

Every instruction step of a recorded pool run (`StepA`) is, on the store-buffer projection
`TPool.toX`, a sequence of store-buffer steps of its thread's events (`Exe`): a fence is
`XStep.fence`
on an empty buffer, a load reads the thread's view (`overlay` is the store-buffer machine
`viewMem`), a buffered
store enqueues exactly the pool's buffer entry, and a synchronising store or locked
read-modify-write updates memory as the pool does (a store by an enqueue and an immediate
flush). Pool flushes are store-buffer flushes (`tsoFlush_toX`). So a recorded run is a store-buffer
run of the
threads' events (`runA_steps`, `opRun_of_runA`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep Act Answers applyWrites)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace actX traceX AStep ACfg)
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush entryByte writeMem readMem readView
  viewMem readBufByte enqueue)
open Silmaril.X86.Pool (TPool TsoFlush TsoStep TsoReach overlay syncs storeEntries atomic9Ev
  readSpan Drained)
open Silmaril.X86.Concurrency.Bridge (ActsOk)
open Silmaril.X86.Concurrency.Bridge.PoolRun

/-! ## Memory -/

theorem install_get (b : Silmaril.Process.ByteMemory) (a : Nat) (bs : List Silmaril.X86.Byte)
    (x : Nat) : (Memory.install b a bs)[x]? = (entryByte a bs x).or b[x]? := by
  induction bs generalizing a with
  | nil => simp [Memory.install, entryByte]
  | cons y ys ih =>
    simp only [Memory.install, Std.ExtHashMap.getElem?_insert, ih]
    by_cases h : a = x
    · subst h; simp [entryByte]
    · have hb : (a == x) = false := by simpa using h
      rw [hb]
      simp only [Bool.false_eq_true, ite_false, entryByte]
      by_cases hx : a + 1 ≤ x
      · have : a ≤ x := by omega
        simp only [hx, this, ite_true]
        rw [show x - a = (x - (a + 1)) + 1 by omega]
        simp
      · have : ¬ a ≤ x := by omega
        simp [hx, this]

theorem readBacking_readMem (b : Silmaril.Process.ByteMemory) :
    ∀ (n a : Nat) (bs : List Silmaril.X86.Byte), Memory.readBacking b a n = some bs →
      readMem (fun x => b[x]?) a n = some bs
  | 0, a, bs, h => by simp [Memory.readBacking] at h; subst h; rfl
  | n + 1, a, bs, h => by
    simp only [Memory.readBacking, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    have := readBacking_readMem b n (a + 1) ys hys
    simp only [readMem, ← Std.ExtHashMap.get?_eq_getElem?, hy]
    simp only [Std.ExtHashMap.get?_eq_getElem?] at this ⊢
    rw [this]

theorem readBacking_length (b : Silmaril.Process.ByteMemory) :
    ∀ (n a : Nat) (bs : List Silmaril.X86.Byte), Memory.readBacking b a n = some bs →
      bs.length = n
  | 0, a, bs, h => by simp [Memory.readBacking] at h; subst h; rfl
  | n + 1, a, bs, h => by
    simp only [Memory.readBacking, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [readBacking_length b n (a + 1) ys hys]

theorem readBytes_readMem {m : Memory} {a n : Nat} {bs : List Silmaril.X86.Byte}
    (h : m.readBytes a n = some bs) : readMem (fun x => m.bytes[x]?) a n = some bs ∧ bs.length = n := by
  simp only [Memory.readBytes, Memory.readWith] at h
  split at h
  · exact ⟨readBacking_readMem _ n a bs h, readBacking_length _ n a bs h⟩
  · cases h

theorem writeBytes_get {m m' : Memory} {a : Nat} {bs : List Silmaril.X86.Byte}
    (h : m.writeBytes a bs = some m') : ∀ x, m'.bytes[x]? = (entryByte a bs x).or m.bytes[x]? := by
  simp only [Memory.writeBytes] at h
  split at h
  · cases h; intro x; exact install_get _ _ _ _
  · cases h

/-- Fences do not write. -/
theorem applyWrites_fences {m m' : Memory} :
    ∀ {acts : List XAct}, (∀ a ∈ acts, ∃ k, a.ev.kind = .fence k) → applyWrites m acts = some m' →
      m' = m
  | [], _, h => by simp [applyWrites] at h; exact h.symm
  | a :: as, hf, h => by
    obtain ⟨k, hk⟩ := hf a (List.mem_cons_self ..)
    simp only [applyWrites, hk, MemEvent.Kind.writes, Bool.false_eq_true, ite_false] at h
    exact applyWrites_fences (fun b hb => hf b (List.mem_cons_of_mem _ hb)) h

theorem applyWrites_one {m m' : Memory} {a : XAct} (h : applyWrites m [a] = some m') :
    (a.ev.kind.writes = true → m.writeBytes a.ev.addr a.wr = some m') ∧
      (a.ev.kind.writes = false → m' = m) := by
  simp only [applyWrites] at h
  constructor
  · intro hw
    simp only [hw, ite_true, Option.bind_eq_some_iff] at h
    obtain ⟨m₁, h1, h2⟩ := h
    cases h2; exact h1
  · intro hw
    simp only [hw, Bool.false_eq_true, ite_false, Option.some.injEq] at h
    exact h.symm

theorem readSpan_write {v v' : Memory} {a : Nat} {bs : List Silmaril.X86.Byte}
    (h : v.writeBytes a bs = some v') : readSpan v' a bs.length = bs := by
  apply List.ext_getElem (by simp [readSpan])
  intro i h1 h2
  simp only [readSpan, List.getElem_map, List.getElem_range, Std.ExtHashMap.get?_eq_getElem?,
    writeBytes_get h, entryByte]
  simp [show a ≤ a + i by omega, h2]

/-! ## Store-buffer runs of one thread's events -/

/-- Store-buffer steps of thread `t`'s events `es`, in order, with flushes of any thread in between.
-/
inductive Exe : XState Nat → List (XEvent Nat) → XState Nat → Prop
  | nil (s : XState Nat) : Exe s [] s
  | ev {s s' : XState Nat} {e : XEvent Nat} {es : List (XEvent Nat)} {s'' : XState Nat}
      (h : XStep s e s') (tl : Exe s' es s'') : Exe s (e :: es) s''
  | flush {s s' : XState Nat} {es : List (XEvent Nat)} {s'' : XState Nat} (h : XFlush s s')
      (tl : Exe s' es s'') : Exe s es s''

theorem Exe.append {s s' s'' : XState Nat} {es es' : List (XEvent Nat)} (h : Exe s es s')
    (h' : Exe s' es' s'') : Exe s (es ++ es') s'' := by
  induction h with
  | nil => exact h'
  | ev h _ ih => exact .ev h (ih h')
  | flush h _ ih => exact .flush h (ih h')

/-- **The events of thread `t` run by `Exe` are `AStep`s** of the composed machine. -/
theorem Exe.astep {s s' : XState Nat} {es : List (XEvent Nat)} (h : Exe s es s') :
    ∀ {t : Nat} {rest : List (List (XEvent Nat))} {tl : List (XEvent Nat)},
      rest[t]? = some (es ++ tl) →
      Relation.ReflTransGen AStep ⟨rest, s⟩ ⟨rest.set t tl, s'⟩ := by
  induction h with
  | nil s =>
    intro t rest tl ht
    have hlen : t < rest.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at ht; cases ht
    have : rest.set t tl = rest := by
      apply List.ext_getElem?
      intro i
      by_cases hi : t = i
      · subst hi; rw [List.getElem?_set_self hlen, ht]; rfl
      · rw [List.getElem?_set_ne hi]
    rw [this]
  | @ev s₁ s₂ e es₁ s₃ hs _ ih =>
    intro t rest tl ht
    have hlen : t < rest.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at ht; cases ht
    have h1 : AStep ⟨rest, s₁⟩ ⟨rest.set t (es₁ ++ tl), s₂⟩ :=
      AStep.ev rest s₁ s₂ t e (es₁ ++ tl) (by simpa using ht) hs
    have h2 := ih (t := t) (rest := rest.set t (es₁ ++ tl)) (tl := tl)
      (by rw [List.getElem?_set_self hlen])
    rw [List.set_set] at h2
    exact Relation.ReflTransGen.head h1 h2
  | @flush s₁ s₂ es₁ s₃ hf _ ih =>
    intro t rest tl ht
    exact Relation.ReflTransGen.head (AStep.flush rest s₁ s₂ hf) (ih ht)

/-- Fences that need no empty buffer (none, as `lfence`/`sfence` give no store-buffer event) or on
an
empty buffer. -/
theorem exe_fences (t : Nat) (s : XState Nat) (hb : s.buffer t = []) :
    ∀ (acts : List XAct), (∀ a ∈ acts, ∃ k, a.ev.kind = .fence k) →
      Exe s (acts.flatMap (actX t)) s
  | [], _ => .nil s
  | a :: as, hf => by
    obtain ⟨k, hk⟩ := hf a (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    have hr := exe_fences t s hb as (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    simp only [actX, hk]
    split
    · exact .ev (XStep.fence s t hb) hr
    · exact hr

/-- In a non-synchronising step there is no `mfence`, so fences give no store-buffer event. -/
theorem exe_fences_nosync (t : Nat) (s : XState Nat) :
    ∀ (acts : List XAct), (∀ a ∈ acts, ∃ k, a.ev.kind = .fence k ∧ k ≠ .mfence) →
      Exe s (acts.flatMap (actX t)) s
  | [], _ => .nil s
  | a :: as, hf => by
    obtain ⟨k, hk, hm⟩ := hf a (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    have hr := exe_fences_nosync t s as (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    simp only [actX, hk, hm, ite_false, List.nil_append]
    exact hr

/-! ## One recorded step -/

theorem view_eq (p : TPool Nat) (t : Nat) :
    viewMem p.toX t = fun x => (overlay p.memory (p.buffer t)).bytes[x]? := by
  funext x; rw [Silmaril.X86.Pool.overlay_getElem?]

theorem toX_mem (p : TPool Nat) : p.toX.memory = fun x => p.memory.bytes[x]? := by
  funext x; simp [TPool.toX]

theorem toX_buffer (p : TPool Nat) : p.toX.buffer = p.buffer := rfl

theorem xstate_ext {s s' : XState Nat} (h1 : s.memory = s'.memory) (h2 : s.buffer = s'.buffer) :
    s = s' := by
  cases s; cases s'; simp_all

theorem syncs_one (e : MemEvent.Event) : syncs [e] = (e.locked || decide (e.kind = .fence .mfence)) := by
  simp [syncs]

theorem syncs_false {es : List MemEvent.Event} (h : syncs es = false) :
    ∀ e ∈ es, e.locked = false ∧ e.kind ≠ .fence .mfence := by
  intro e he
  simp only [syncs, List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq, not_or] at h
  have := h e he
  exact ⟨by simpa using this.1, this.2⟩

theorem storeEntries_fences {es : List MemEvent.Event} (h : ∀ e ∈ es, ∃ k, e.kind = .fence k)
    (v : Memory) : storeEntries es v = [] := by
  simp only [storeEntries, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro e he
  obtain ⟨k, hk⟩ := h e he
  simp [hk, MemEvent.Kind.writes]

theorem Exe.cast {s s' s'' : XState Nat} {es : List (XEvent Nat)} (h : Exe s es s')
    (he : s' = s'') : Exe s es s'' := he ▸ h

/-- A load of thread `t` reading memory `m`'s bytes through its view. -/
theorem load_step (s : XState Nat) (t a : Nat) (m : Memory) (hv : viewMem s t = fun x => m.bytes[x]?)
    {n : Nat} {bs : List Silmaril.X86.Byte} (h : m.readBytes a n = some bs) :
    XStep s (.load t a bs) s := by
  obtain ⟨h1, h2⟩ := readBytes_readMem h
  refine XStep.load s t a bs ?_
  rw [readView, hv, h2]; exact h1

/-- **A recorded step is a store-buffer run of its thread's events.** -/
theorem stepA_exe {Fin : Nat → State → Prop} {p : TPool Nat} {t : Nat} {o : Obs} {p' : TPool Nat}
    (h : StepA Fin p t o p') : Exe p.toX (o.acts.flatMap (actX t)) p'.toX := by
  cases h with
  | @sync c c' i n mem' acts ht hnf hf hs he hx ha =>
    obtain ⟨hsh, hev, hans, hap⟩ := ha
    simp only at hans hap ⊢
    have hev' : MemEvent.atomic9Accesses i c n = acts.map Act.ev := hev.symm
    change syncs (MemEvent.atomic9Accesses i c n) = true at hs
    have hv : viewMem p.toX t = fun x => p.memory.bytes[x]? := by
      rw [view_eq, he]; rfl
    rcases hsh with hf' | ⟨a, rfl, hnf', hl, hst, -, hrd, hwr⟩
    · have hm := applyWrites_fences (fun a ha => (hf' a ha).1) hap
      subst hm
      exact exe_fences t _ he acts (fun a ha => (hf' a ha).1)
    · rw [hev'] at hs
      simp only [List.map_cons, List.map_nil, syncs_one, Bool.or_eq_true, decide_eq_true_eq] at hs
      have hlk : a.ev.locked = true := hs.resolve_right (hnf' _)
      obtain ⟨hw1, hw2⟩ := applyWrites_one hap
      have hans' := hans a (List.mem_singleton_self _)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      cases hk : a.ev.kind with
      | fence k => exact absurd hk (hnf' k)
      | load => rw [hk] at hl; rw [hl rfl] at hlk; cases hlk
      | store => rw [hk] at hst; rw [hst rfl] at hlk; cases hlk
      | rmw =>
        simp only [actX, hk, hlk, ite_true]
        have hR : a.ev.kind.reads = true := by simp [hk, MemEvent.Kind.reads]
        have hW : a.ev.kind.writes = true := by simp [hk, MemEvent.Kind.writes]
        obtain ⟨hm, hlen⟩ := readBytes_readMem (hans' hR)
        have hwb := hw1 hW
        refine .ev (XStep.rmw p.toX t a.ev.addr a.rd a.wr he ?_ ?_) (Exe.nil _ |>.cast ?_)
        · rw [toX_mem, hlen]; exact hm
        · rw [hwr hW, hrd hR]
        · apply xstate_ext
          · funext x
            simp only [writeMem, TPool.toX, Std.ExtHashMap.get?_eq_getElem?]
            rw [writeBytes_get hwb]
          · rfl
  | @buffered c c' i n view' acts ht hnf hf hs hx ha =>
    obtain ⟨hsh, hev, hans, hap⟩ := ha
    simp only at hans hap ⊢
    have hev' : MemEvent.atomic9Accesses i c n = acts.map Act.ev := hev.symm
    change syncs (MemEvent.atomic9Accesses i c n) = false at hs
    have hns := syncs_false hs
    have hv := view_eq p t
    rcases hsh with hf' | ⟨a, rfl, hnf', hl, hst, -, hrd, hwr⟩
    · have hse : storeEntries (atomic9Ev.accesses i c n) view' = [] := by
        change storeEntries (MemEvent.atomic9Accesses i c n) view' = []
        rw [hev']
        exact storeEntries_fences (by
          intro e he; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he; exact (hf' b hb).1) _
      rw [hse, List.append_nil, Function.update_eq_self]
      refine exe_fences_nosync t _ acts ?_
      intro b hb
      obtain ⟨k, hk⟩ := (hf' b hb).1
      refine ⟨k, hk, ?_⟩
      have := (hns b.ev (by rw [hev']; exact List.mem_map_of_mem hb)).2
      rw [hk] at this
      exact fun h => this (h ▸ rfl)
    · have hnl := (hns a.ev (by rw [hev']; exact List.mem_singleton_self _)).1
      have hans' := hans a (List.mem_singleton_self _)
      obtain ⟨hw1, hw2⟩ := applyWrites_one hap
      have hse : storeEntries (atomic9Ev.accesses i c n) view' =
          if a.ev.kind.writes then [(a.ev.addr, a.wr)] else [] := by
        change storeEntries (MemEvent.atomic9Accesses i c n) view' = _
        rw [hev']
        simp only [storeEntries, List.map_cons, List.map_nil]
        cases hwr' : a.ev.kind.writes
        · simp [hwr']
        · simp only [List.filter_cons, hwr', ite_true, List.filter_nil, List.map_cons,
            List.map_nil]
          rw [← hwr hwr', readSpan_write (hw1 hwr')]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      cases hk : a.ev.kind with
      | fence k => exact absurd hk (hnf' k)
      | load =>
        have hW : a.ev.kind.writes = false := by simp [hk, MemEvent.Kind.writes]
        rw [hse, hW]
        simp only [Bool.false_eq_true, ite_false, List.append_nil, Function.update_eq_self]
        simp only [actX, hk]
        exact .ev (load_step _ t _ _ hv (hans' (by simp [hk, MemEvent.Kind.reads]))) (.nil _)
      | store =>
        have hW : a.ev.kind.writes = true := by simp [hk, MemEvent.Kind.writes]
        rw [hse, hW]
        simp only [ite_true, actX, hk]
        exact .ev (XStep.store _ t _ _) (.nil _)
      | rmw =>
        have hW : a.ev.kind.writes = true := by simp [hk, MemEvent.Kind.writes]
        rw [hse, hW]
        simp only [ite_true, actX, hk, hnl, Bool.false_eq_true, ite_false]
        exact .ev (load_step _ t _ _ hv (hans' (by simp [hk, MemEvent.Kind.reads])))
          (.ev (XStep.store _ t _ _) (.nil _))

/-! ## Recorded runs -/

/-- Per-thread lists of threads `0, …, N - 1`. -/
def cfgOf (N : Nat) (G : Nat → List (XEvent Nat)) : List (List (XEvent Nat)) := (List.range N).map G

theorem cfgOf_get {N t : Nat} (h : t < N) (G : Nat → List (XEvent Nat)) :
    (cfgOf N G)[t]? = some (G t) := by
  simp [cfgOf, List.getElem?_range h]

theorem cfgOf_set {N t : Nat} (h : t < N) (G : Nat → List (XEvent Nat)) (v : List (XEvent Nat)) :
    (cfgOf N G).set t v = cfgOf N (Function.update G t v) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : t = i
  · subst hi
    rw [List.getElem?_set_self (by simp [cfgOf, h]), cfgOf_get h]
    simp
  · rw [List.getElem?_set_ne hi]
    simp only [cfgOf, List.getElem?_map]
    rcases Nat.lt_or_ge i N with hiN | hiN
    · rw [List.getElem?_range hiN]
      simp [Function.update_of_ne (Ne.symm hi)]
    · rw [List.getElem?_eq_none (by simpa using hiN)]; rfl

theorem stepA_threads {Fin : Nat → State → Prop} {p : TPool Nat} {t : Nat} {o : Obs}
    {p' : TPool Nat} (h : StepA Fin p t o p') :
    (∃ c, p.threads t = some c) ∧ ∀ t', t' ≠ t → p'.threads t' = p.threads t' := by
  cases h with
  | sync ht => exact ⟨⟨_, ht⟩, fun t' h => Function.update_of_ne h _ _⟩
  | buffered ht => exact ⟨⟨_, ht⟩, fun t' h => Function.update_of_ne h _ _⟩

theorem tsoFlush_threads {p p' : TPool Nat} (h : TsoFlush p p') : p'.threads = p.threads := by
  cases h; rfl

/-- **A recorded run is a store-buffer run of the threads' events**, with any future events `F`. -/
theorem runA_steps {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (hN : ∀ t, N ≤ t → p₀.threads t = none) :
    (∀ t, N ≤ t → p.threads t = none ∧ H t = []) ∧
    ∀ F : Nat → List XAct,
      Relation.ReflTransGen AStep
        ⟨cfgOf N fun k => ((H k).flatMap Obs.acts ++ F k).flatMap (actX k), p₀.toX⟩
        ⟨cfgOf N fun k => (F k).flatMap (actX k), p.toX⟩ := by
  induction h with
  | refl =>
    refine ⟨fun t ht => ⟨hN t ht, rfl⟩, fun F => ?_⟩
    dsimp only
    simp only [List.flatMap_nil, List.nil_append]
    exact .refl
  | @step H p₁ t o p₂ _ hs ih =>
    obtain ⟨⟨c, hc⟩, hth⟩ := stepA_threads hs
    have htN : t < N := by
      by_contra hlt
      rw [(ih.1 t (by omega)).1] at hc; cases hc
    refine ⟨fun t' ht' => ⟨?_, ?_⟩, fun F => ?_⟩
    · rw [hth t' (by omega)]; exact (ih.1 t' ht').1
    · rw [Function.update_of_ne (by omega)]; exact (ih.1 t' ht').2
    · have h1 := ih.2 (Function.update F t (o.acts ++ F t))
      have e1 : (cfgOf N fun k => ((H k).flatMap Obs.acts ++
            Function.update F t (o.acts ++ F t) k).flatMap (actX k)) =
          cfgOf N fun k => ((Function.update H t (H t ++ [o]) k).flatMap Obs.acts ++
            F k).flatMap (actX k) := by
        congr 1; funext k
        by_cases hk : k = t
        · subst hk; simp [List.flatMap_append]
        · simp [Function.update_of_ne hk]
      rw [e1] at h1
      have h2 := (stepA_exe hs).astep (t := t)
        (rest := cfgOf N fun k => (Function.update F t (o.acts ++ F t) k).flatMap (actX k))
        (tl := (F t).flatMap (actX t)) (by rw [cfgOf_get htN]; simp [List.flatMap_append])
      rw [cfgOf_set htN] at h2
      have e2 : Function.update (fun k => (Function.update F t (o.acts ++ F t) k).flatMap (actX k))
          t ((F t).flatMap (actX t)) = fun k => (F k).flatMap (actX k) := by
        funext k
        by_cases hk : k = t
        · subst hk; simp
        · simp [Function.update_of_ne hk]
      rw [e2] at h2
      exact h1.trans h2
  | @flush H p₁ p₂ _ hf ih =>
    refine ⟨fun t ht => ⟨?_, (ih.1 t ht).2⟩, fun F => ?_⟩
    · rw [tsoFlush_threads hf]; exact (ih.1 t ht).1
    · exact (ih.2 F).tail (AStep.flush _ _ _ (Silmaril.X86.Pool.tsoFlush_toX hf))

/-- **(4) The recorded pool run is a complete store-buffer run** of the program of the threads'
events, from the initial memory, ending in the pool's final (drained) state. -/
theorem opRun_of_runA {Fin : Nat → State → Prop} {N : Nat} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) (hb : ∀ t, p₀.buffer t = [])
    (hN : ∀ t, N ≤ t → p₀.threads t = none) (hd : Drained p) :
    Silmaril.X86.MemoryModel.OpAx.Run (poolProg N H) (fun a => p₀.memory.bytes[a]?) p.toX := by
  refine ⟨?_, hd⟩
  have h1 := (runA_steps h hN).2 (fun _ => [])
  have e0 : p₀.toX = ⟨fun a => p₀.memory.bytes[a]?, fun _ => []⟩ := by
    apply xstate_ext
    · exact toX_mem p₀
    · funext t; exact hb t
  have e1 : (cfgOf N fun k => ((H k).flatMap Obs.acts ++ []).flatMap (actX k)) = poolProg N H := by
    simp [cfgOf, poolProg, histX]
  have e2 : (cfgOf N fun k => ([] : List XAct).flatMap (actX k)) =
      (poolProg N H).map fun _ => [] := by
    simp [cfgOf, poolProg, Function.comp_def]
  rw [e0, e1, e2] at h1
  exact h1

/-! ## From `TsoReach` -/

/-- A recorded run is a run. -/
theorem runA_reach {Fin : Nat → State → Prop} {p₀ : TPool Nat} {H : Nat → List Obs}
    {p : TPool Nat} (h : RunA Fin p₀ H p) : TsoReach atomic9Ev Fin p₀ p := by
  induction h with
  | refl => exact .refl
  | @step H₁ p₁ t o p₂ _ hs ih =>
    refine ih.tail (.inl ⟨t, ?_⟩)
    cases hs with
    | sync ht hnf hf hs he hx => exact TsoStep.sync ht hnf hf hs he hx
    | buffered ht hnf hf hs hx => exact TsoStep.buffered ht hnf hf hs hx
  | flush _ hf ih => exact ih.tail (.inr hf)

/-- **Every run can be recorded** when every step it can take has actions (`StepActs` on the
thread's view; for a synchronising step the buffer is empty, so the view is memory). -/
theorem runA_of_reach {Fin : Nat → State → Prop} {p₀ p : TPool Nat}
    (h : TsoReach atomic9Ev Fin p₀ p)
    (hA : ∀ (p₁ : TPool Nat) (t : Nat) (c : State) (i : Atomic9.Instr) (n : Nat) (c' : State)
      (m' : Memory), TsoReach atomic9Ev Fin p₀ p₁ → p₁.threads t = some c → ¬ Fin t c →
      atomic9Ev.fetch (overlay p₁.memory (p₁.buffer t)) c.rip.toNat = some (i, n) →
      atomic9Ev.exec i c (overlay p₁.memory (p₁.buffer t)) n = .ok c' m' →
      ∃ acts, StepActs acts i c n ⟨overlay p₁.memory (p₁.buffer t), c', m'⟩) :
    ∃ H, RunA Fin p₀ H p := by
  induction h with
  | refl => exact ⟨_, .refl⟩
  | @tail p₁ p₂ hr hs ih =>
    obtain ⟨H, hH⟩ := ih
    rcases hs with ⟨t, hs⟩ | hf
    · cases hs with
      | @sync c c' i n mem' ht hnf hf hs he hx =>
        have hx' : atomic9Ev.exec i c (overlay p₁.memory (p₁.buffer t)) n = .ok c' mem' := by
          rw [he]; exact hx
        obtain ⟨acts, ha⟩ := hA p₁ t c i n c' mem' hr ht hnf hf hx'
        rw [he] at ha
        exact ⟨_, .step hH (StepA.sync (acts := acts) ht hnf hf hs he hx ha)⟩
      | @buffered c c' i n view' ht hnf hf hs hx =>
        obtain ⟨acts, ha⟩ := hA p₁ t c i n c' view' hr ht hnf hf hx
        exact ⟨_, .step hH (StepA.buffered (acts := acts) ht hnf hf hs hx ha)⟩
    · exact ⟨H, .flush hH hf⟩

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun
