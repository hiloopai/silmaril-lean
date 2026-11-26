module

public import Silmaril.Proofs.X86.Pool.Par
public import Silmaril.Proofs.X86.Pool.Tso

/-!
# Proofs: DRF for footprint-ownership-safe TSO pools (`Task.drfTso`)

A footprint-ownership-safe pool (`OwnershipSafeEv`) reaches, under the byte-granular TSO pool
(`TsoReach`), only drained states the SC pool reaches (`drfTso`).

**The simulation.** Every TSO state `p` is matched by an SC state `q` (`Sim`): the same
threads and mapping list; every buffered byte of thread `t` is a cell `t` owns; on a cell `t`
owns, `q` holds what `t` sees (its buffer over memory); on a cell nobody owns, `q` holds the
memory's byte. The fragments `σ` of the ownership certificate are carried along the SC run
(`OwnW`, the conjuncts of `OwnershipSafeEv` for a fixed witness).

* A thread's view and the SC memory agree on the cells of `σ t ∪ r` (`view_agree`): its own
  cells by `Sim`, the read-only ones because nobody owns them, so nobody buffers them.
* So the fetch is the same (`FetchStable`, the fetched bytes are in `σ t ∪ r`), and by
  locality (`EvMachine.isLocal`, the read set is in `σ t ∪ r`) the executor returns the same
  core and writes the same bytes on the write set, which `σ t` owns.
* A buffered step is matched by the SC step: the new buffer entries install exactly the bytes
  the SC step wrote (`overlay_storeEntries`). A synchronising step is matched by the SC step
  on memory. A flush is matched by no step: it moves a byte `t` owns from the buffer to memory,
  which `t`'s view, and so `q`, already had.
* At a drained state, `Sim` says `q` and `p` have the same bytes everywhere, so `forget p = q`.

The SC side is `OwnershipSafe.step` (`Par.lean`) for `LSafeEv` (`ownW_step`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool

open Silmaril.X86 (State MState Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin Agree Patched readSet writeSet)
open Silmaril.X86.Pool
open Silmaril.X86.MemoryModel.Tso (entryByte readBufByte)

variable {Tid : Type}

namespace Drf

/-! ## Buffers, bytes and overlays -/

theorem overlay_get (mem : Memory) (buf : List Entry) (x : Nat) :
    (overlay mem buf).bytes[x]? = (readBufByte x buf).or mem.bytes[x]? := by
  simp [overlay, foldl_install_getElem?]

theorem overlay_append (mem : Memory) (b₁ b₂ : List Entry) :
    overlay mem (b₁ ++ b₂) = overlay (overlay mem b₁) b₂ := by
  simp [overlay, List.foldl_append]

/-- The buffer covers byte `x`. -/
def Covers (buf : List Entry) (x : Nat) : Prop := ∃ e ∈ buf, e.1 ≤ x ∧ x < e.1 + e.2.length

theorem entryByte_eq_none {a x : Nat} {bs : List Byte} (h : ¬ (a ≤ x ∧ x < a + bs.length)) :
    entryByte a bs x = none := by
  unfold entryByte
  split
  · rename_i ha
    apply List.getElem?_eq_none
    omega
  · rfl

theorem readBufByte_none {buf : List Entry} {x : Nat} (h : ¬ Covers buf x) :
    readBufByte x buf = none := by
  induction buf with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, bs⟩ := e
    simp only [readBufByte]
    rw [ih (fun ⟨e', he', hc⟩ => h ⟨e', List.mem_cons_of_mem _ he', hc⟩),
      entryByte_eq_none (fun hc => h ⟨(a, bs), List.mem_cons_self, hc⟩)]
    rfl

theorem overlay_get_of_not_covers {mem : Memory} {buf : List Entry} {x : Nat}
    (h : ¬ Covers buf x) : (overlay mem buf).bytes[x]? = mem.bytes[x]? := by
  rw [overlay_get, readBufByte_none h]; rfl

theorem overlay_congr {m₁ m₂ : Memory} (buf : List Entry) {x : Nat}
    (h : m₁.bytes[x]? = m₂.bytes[x]?) :
    (overlay m₁ buf).bytes[x]? = (overlay m₂ buf).bytes[x]? := by
  rw [overlay_get, overlay_get, h]

theorem install_get_of_not_covers {b : Silmaril.Process.ByteMemory} {a x : Nat}
    {bs : List Byte} (h : ¬ (a ≤ x ∧ x < a + bs.length)) :
    (Memory.install b a bs)[x]? = b[x]? := by
  rw [install_getElem?, entryByte_eq_none h]; rfl

/-- A buffer whose every covering entry reads `v` at `x`. -/
theorem readBufByte_of_all {buf : List Entry} {x : Nat} {v : Byte}
    (h : ∀ e ∈ buf, entryByte e.1 e.2 x = none ∨ entryByte e.1 e.2 x = some v) :
    readBufByte x buf = none ∨ readBufByte x buf = some v := by
  induction buf with
  | nil => exact .inl rfl
  | cons e rest ih =>
    obtain ⟨a, bs⟩ := e
    simp only [readBufByte]
    rcases ih (fun e he => h e (List.mem_cons_of_mem _ he)) with e1 | e1 <;> rw [e1]
    · rcases h (a, bs) List.mem_cons_self with e2 | e2 <;> rw [e2] <;> simp
    · simp

theorem readBufByte_some_of_mem {buf : List Entry} {x : Nat} {e : Entry} (he : e ∈ buf)
    (hx : (entryByte e.1 e.2 x).isSome) : (readBufByte x buf).isSome := by
  induction buf with
  | nil => cases he
  | cons e' rest ih =>
    obtain ⟨a, bs⟩ := e'
    simp only [readBufByte]
    rcases List.mem_cons.mp he with rfl | he'
    · cases readBufByte x rest <;> simp_all
    · have := ih he'
      cases e3 : readBufByte x rest
      · rw [e3] at this; cases this
      · simp

theorem entryByte_readSpan_of_covers {V' : Memory} {a n x : Nat} (h1 : a ≤ x) (h2 : x < a + n)
    (hs : (V'.bytes[x]?).isSome) : entryByte a (readSpan V' a n) x = V'.bytes[x]? := by
  unfold entryByte readSpan
  simp only [h1, ↓reduceIte]
  rw [List.getElem?_map, List.getElem?_range (by omega : x - a < n)]
  simp only [Option.map_some]
  rw [show a + (x - a) = x by omega, Std.ExtHashMap.get?_eq_getElem?]
  cases e : V'.bytes[x]? with
  | none => rw [e] at hs; cases hs
  | some b => rfl

theorem entryByte_readSpan_of_not_covers {V' : Memory} {a n x : Nat}
    (h : ¬ (a ≤ x ∧ x < a + n)) : entryByte a (readSpan V' a n) x = none := by
  apply entryByte_eq_none
  simpa [readSpan] using h

/-- **The entries of a buffered step install the executor's bytes**: overlaid on the view,
they give the view after the instruction, byte for byte. -/
theorem overlay_storeEntries {es : List Silmaril.X86.MemEvent.Event} {V V' : Memory}
    (hw : ∀ x, writeSet es x → (V'.bytes[x]?).isSome)
    (ho : ∀ x, ¬ writeSet es x → V'.bytes[x]? = V.bytes[x]?) (x : Nat) :
    (overlay V (storeEntries es V')).bytes[x]? = V'.bytes[x]? := by
  rw [overlay_get]
  by_cases hW : writeSet es x
  · obtain ⟨ev, hev, hwr, hc⟩ := hW
    have hs := hw x ⟨ev, hev, hwr, hc⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    have hall : ∀ e ∈ storeEntries es V', entryByte e.1 e.2 x = none ∨
        entryByte e.1 e.2 x = some v := by
      intro e he
      simp only [storeEntries, List.mem_map, List.mem_filter] at he
      obtain ⟨ev', ⟨hev', hwr'⟩, rfl⟩ := he
      by_cases hc' : ev'.addr ≤ x ∧ x < ev'.addr + ev'.size
      · right
        rw [entryByte_readSpan_of_covers hc'.1 hc'.2 (hw x ⟨ev', hev', hwr', hc'⟩), hv]
      · left; exact entryByte_readSpan_of_not_covers hc'
    have hsome : (readBufByte x (storeEntries es V')).isSome := by
      refine readBufByte_some_of_mem (e := (ev.addr, readSpan V' ev.addr ev.size)) ?_ ?_
      · simp only [storeEntries, List.mem_map, List.mem_filter]
        exact ⟨ev, ⟨hev, hwr⟩, rfl⟩
      · show (entryByte ev.addr (readSpan V' ev.addr ev.size) x).isSome
        rw [entryByte_readSpan_of_covers hc.1 hc.2 hs]; exact hs
    rcases readBufByte_of_all hall with e | e
    · rw [e] at hsome; cases hsome
    · rw [e, hv]; rfl
  · have : ¬ Covers (storeEntries es V') x := by
      rintro ⟨e, he, h1, h2⟩
      simp only [storeEntries, List.mem_map, List.mem_filter] at he
      obtain ⟨ev, ⟨hev, hwr⟩, rfl⟩ := he
      simp only [readSpan, List.length_map, List.length_range] at h2
      exact hW ⟨ev, hev, hwr, h1, h2⟩
    rw [readBufByte_none this, ho x hW]; rfl


/-! ## The certificate along the SC run -/

section Own
variable [DecidableEq Tid]

/-- `OwnershipSafeEv` for a fixed witness. -/
def OwnW (M : EvMachine) (Fin : Tid → State → Prop) (σ : Tid → Frag) (r : Frag)
    (Q : Tid → SProp) (q : Pool Tid) : Prop :=
  SharedOnly r ∧
  (∀ t, q.threads t = none → σ t = Frag.empty) ∧
  (∀ t t', t ≠ t' → PFrag.Disjoint (embed t (σ t)) (embed t' (σ t'))) ∧
  (∀ t, PFrag.Disjoint (embed t (σ t)) (embedS r)) ∧
  (∀ t, PFrag.Le (embed t (σ t)) (poolFrag q)) ∧
  PFrag.Le (embedS r) (poolFrag q) ∧
  ∀ t c, q.threads t = some c → ∀ n, LSafeEv M (Fin t) (Q t) r n c (σ t)

variable {M : EvMachine} {Fin : Tid → State → Prop} {σ : Tid → Frag} {r : Frag}
  {Q : Tid → SProp} {q : Pool Tid}

theorem OwnW.le (h : OwnW M Fin σ r Q q) {t : Tid} {c : State} (ht : q.threads t = some c) :
    Le (union (σ t) r) (toFrag ⟨c, q.memory⟩) := by
  obtain ⟨hrS, -, -, -, hleσ, hler, -⟩ := h
  rw [← proj_poolFrag ht]
  refine le_union (le_embed_iff (hleσ t)) ?_
  rw [← proj_embedS t hrS]; exact proj_le hler

theorem OwnW.cell (h : OwnW M Fin σ r Q q) {t t' : Tid} (htt : t ≠ t') (x : Nat) :
    σ t (.mem x) = none ∨ σ t' (.mem x) = none := by
  have := h.2.2.1 t t' htt (.shared (.mem x))
  rwa [embed_shared _ rfl, embed_shared _ rfl] at this

theorem OwnW.cell_r (h : OwnW M Fin σ r Q q) (t : Tid) (x : Nat) :
    σ t (.mem x) = none ∨ r (.mem x) = none := by
  have := h.2.2.2.1 t (.shared (.mem x))
  rwa [embed_shared _ rfl, embedS_shared _ rfl] at this

/-- **The certificate is preserved by an SC step** of an unfinished thread (as
`OwnershipSafe.step`), with the stepping thread's fragment re-valued. -/
theorem ownW_step (hown : OwnW M Fin σ r Q q) {t : Tid} {c : State} {m₀ : MState}
    (ht : q.threads t = some c) (hnf : ¬ Fin t c) (hs' : M.step ⟨c, q.memory⟩ = some m₀) :
    ChangesWithin (σ t) ⟨c, q.memory⟩ m₀ ∧
    OwnW M Fin (Function.update σ t (reval (σ t) (toFrag m₀))) r Q
      ⟨Function.update q.threads t (some m₀.core), m₀.memory⟩ := by
  have hle := hown.le ht
  obtain ⟨hrS, hnone, hdσ, hdr, hleσ, hler, hsafe⟩ := hown
  have hcw : ChangesWithin (σ t) ⟨c, q.memory⟩ m₀ := by
    rcases hsafe t c ht 1 q.memory hle with ⟨hf, -⟩ | ⟨-, -, -, m', -, -, -, e, hcw, -⟩
    · exact absurd hf hnf
    · rw [hs'] at e; cases e; exact hcw
  refine ⟨hcw, ?_⟩
  set σ' : Tid → Frag := Function.update σ t (reval (σ t) (toFrag m₀)) with hσ'def
  have hσt : σ' t = reval (σ t) (toFrag m₀) := by simp [σ']
  have hσo : ∀ u, u ≠ t → σ' u = σ u := fun u hu => by simp [σ', hu]
  refine ⟨hrS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    by_cases e : u = t
    · subst e; simp at hu
    · simp only [Function.update_of_ne e] at hu; rw [hσo u e]; exact hnone u hu
  · intro u u' huu
    by_cases e : u = t
    · subst e
      rw [hσt, hσo u' (Ne.symm huu)]
      exact disjoint_embed_reval (hdσ u u' huu)
    · by_cases e' : u' = t
      · subst e'
        rw [hσt, hσo u e]
        exact PF.disjoint_symm (disjoint_embed_reval (PF.disjoint_symm (hdσ u u' huu)))
      · rw [hσo u e, hσo u' e']; exact hdσ u u' huu
  · intro u
    by_cases e : u = t
    · subst e; rw [hσt]; exact disjoint_embed_reval (hdr u)
    · rw [hσo u e]; exact hdr u
  · intro u
    by_cases e : u = t
    · subst e
      rw [hσt]
      intro L v eL
      have hs : (embed u (σ u) L).isSome := by
        cases e2 : embed u (σ u) L with
        | none => rw [embed_reval_none.mpr e2] at eL; cases eL
        | some _ => rfl
      rw [poolFrag_step_inside hs, eL]
    · rw [hσo u e]
      exact le_poolFrag_step_of_disjoint ht hcw (hleσ u) (hdσ t u (Ne.symm e))
  · exact le_poolFrag_step_of_disjoint ht hcw hler (hdr t)
  · intro u c' hu n
    by_cases e : u = t
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hu
      subst hu
      rw [hσt]
      rcases hsafe u c ht (n + 1) q.memory hle with ⟨hf, -⟩ | ⟨-, -, -, m', -, -, -, e2, -, hs⟩
      · exact absurd hf hnf
      · rw [hs'] at e2; cases e2; exact hs
    · simp only [Function.update_of_ne e] at hu
      rw [hσo u e]
      exact hsafe u c' hu n

end Own

/-! ## The simulation -/

/-- **The TSO pool `p` is simulated by the SC pool `q`** under the fragments `σ`. -/
def Sim (σ : Tid → Frag) (p : TPool Tid) (q : Pool Tid) : Prop :=
  q.threads = p.threads ∧ q.memory.regions = p.memory.regions ∧
  (∀ t x, Covers (p.buffer t) x → (σ t (.mem x)).isSome) ∧
  (∀ t x, (σ t (.mem x)).isSome →
    q.memory.bytes[x]? = (overlay p.memory (p.buffer t)).bytes[x]?) ∧
  (∀ x, (∀ t, σ t (.mem x) = none) → q.memory.bytes[x]? = p.memory.bytes[x]?)

theorem reval_cell_isSome {h : Frag} {m : MState} {x : Nat} :
    (reval h (toFrag m) (.mem x)).isSome = (h (.mem x)).isSome := by
  unfold reval
  cases e : h (.mem x) <;> simp [toFrag]

section Step
variable [DecidableEq Tid]
variable {M : EvMachine} {Fin : Tid → State → Prop} {σ : Tid → Frag} {r : Frag}
  {Q : Tid → SProp} {q : Pool Tid} {p : TPool Tid}

/-- **A thread's view agrees with the SC memory on its footprint** `σ t ∪ r`. -/
theorem view_agree (hown : OwnW M Fin σ r Q q) (hsim : Sim σ p q) (t : Tid) :
    Agree (fun x => (union (σ t) r (.mem x)).isSome) q.memory
      (overlay p.memory (p.buffer t)) := by
  obtain ⟨-, hreg, hcov, howned, hfree⟩ := hsim
  refine ⟨hreg, fun x hx => ?_⟩
  by_cases hσ : (σ t (.mem x)).isSome
  · exact howned t x hσ
  · have hσn : σ t (.mem x) = none := by simpa using hσ
    have hr : (r (.mem x)).isSome := by
      have hx' : (union (σ t) r (.mem x)).isSome := hx
      rw [union_of_none hσn] at hx'; exact hx'
    have hall : ∀ u, σ u (.mem x) = none := by
      intro u
      rcases hown.cell_r u x with e | e
      · exact e
      · rw [e] at hr; cases hr
    rw [hfree x hall, overlay_get_of_not_covers (fun hc => hσ (hcov t x hc))]

/-- The SC step of the thread from the facts of its `LSafeEv` at index one. -/
theorem sc_facts (hown : OwnW M Fin σ r Q q) {t : Tid} {c : State} (ht : q.threads t = some c)
    (hnf : ¬ Fin t c) :
    ∃ i k m', M.fetch q.memory c.rip.toNat = some (i, k) ∧
      FetchStable M q.memory c.rip.toNat i k ∧
      InFootprint (σ t) r c.rip.toNat k (M.accesses i c k) ∧
      M.step ⟨c, q.memory⟩ = some m' := by
  rcases hown.2.2.2.2.2.2 t c ht 1 q.memory (hown.le ht) with ⟨hf, -⟩ |
    ⟨-, i, k, m', hf, hst, hfoot, e, -, -⟩
  · exact absurd hf hnf
  · exact ⟨i, k, m', hf, hst, hfoot, e⟩

omit [DecidableEq Tid] in
/-- The executor on the view, matched with the executor on the SC memory. -/
theorem exec_match {c : State} {i : M.Instr} {k : Nat} {mem V : Memory}
    {m' : MState} {c' : State} {V' : Memory}
    (hag : Agree (readSet (M.accesses i c k)) mem V)
    (hstep : M.step ⟨c, mem⟩ = some m') (hfq : M.fetch mem c.rip.toNat = some (i, k))
    (hx : M.exec i c V k = .ok c' V') :
    m'.core = c' ∧ Patched (writeSet (M.accesses i c k)) mem m'.memory V V' := by
  have hrel := (M.isLocal i c k).congr mem V hag
  simp only [EvMachine.step, hfq, Option.bind_some] at hstep
  cases hq : M.exec i c mem k with
  | ok c₁ mem₁ =>
    rw [hq] at hstep hrel
    simp only [Silmaril.X86.Open.ofResult, Option.some.injEq] at hstep
    subst hstep
    rw [hx] at hrel
    simpa [Silmaril.X86.MemEvent.extView, Silmaril.X86.MemEvent.Rel] using hrel
  | _ => rw [hq] at hstep; simp [Silmaril.X86.Open.ofResult] at hstep

/-- **One TSO instruction step is simulated by one SC step.** -/
theorem sim_tsoStep (hown : OwnW M Fin σ r Q q) (hsim : Sim σ p q) {t : Tid} {p' : TPool Tid}
    (hst : TsoStep M Fin p t p') :
    ∃ σ' q', SCStepF M.step Fin q t q' ∧ OwnW M Fin σ' r Q q' ∧ Sim σ' p' q' := by
  have hag := view_agree hown hsim t
  obtain ⟨hth, hreg, hcov, howned, hfree⟩ := hsim
  cases hst with
  | sync ht hnf hf hs he hx =>
    rename_i c c' i n mem'
    have hq : q.threads t = some c := by rw [hth]; exact ht
    obtain ⟨i₀, k, m', hfq, hstab, hfoot, hstep⟩ := sc_facts hown hq hnf
    have hfV := hstab _ (Silmaril.X86.MemEvent.Agree.mono hag (fun x hx => hfoot.1 (x - c.rip.toNat)
      (by omega) |> fun h => by rwa [show c.rip.toNat + (x - c.rip.toNat) = x by omega] at h))
    rw [hf] at hfV
    simp only [Option.some.injEq, Prod.mk.injEq] at hfV
    obtain ⟨rfl, rfl⟩ := hfV
    rw [he, overlay_nil] at hag
    obtain ⟨hcore, hP⟩ := exec_match (Silmaril.X86.MemEvent.Agree.mono hag hfoot.2.1) hstep hfq hx
    obtain ⟨hcw, hown'⟩ := ownW_step hown hq hnf hstep
    refine ⟨_, _, ⟨⟨c, hq, hnf⟩, SCStep.go hq hstep⟩, hown', ?_⟩
    have hWσ : ∀ x, writeSet (M.accesses i c n) x → (σ t (.mem x)).isSome := hfoot.2.2
    have hσ' : ∀ u x, ((Function.update σ t (reval (σ t) (toFrag m'))) u (.mem x)).isSome =
        (σ u (.mem x)).isSome := by
      intro u x
      by_cases e : u = t
      · subst e; simp [reval_cell_isSome]
      · simp [Function.update_of_ne e]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hth, hcore]
    · exact hP.regions.trans (hreg.trans hP.regions'.symm)
    · intro u x hc; rw [hσ']; exact hcov u x hc
    · intro u x hxs
      rw [hσ'] at hxs
      show m'.memory.bytes[x]? = (overlay mem' (p.buffer u)).bytes[x]?
      by_cases e : u = t
      · subst e
        rw [he, overlay_nil]
        by_cases hW : writeSet (M.accesses i c n) x
        · exact (hP.inside x hW).symm
        · rw [hP.outside x hW, hP.outside' x hW, howned u x hxs, he, overlay_nil]
      · have hW : ¬ writeSet (M.accesses i c n) x := fun hW => by
          rcases hown.cell e x with e1 | e1
          · rw [e1] at hxs; cases hxs
          · have := hWσ x hW; rw [e1] at this; cases this
        rw [hP.outside x hW, howned u x hxs]
        exact overlay_congr _ (hP.outside' x hW).symm
    · intro x hxs
      have hx' : ∀ u, σ u (.mem x) = none := fun u => by
        have := hσ' u x; rw [hxs u] at this; simpa using this.symm
      have hW : ¬ writeSet (M.accesses i c n) x := fun hW => by
        have := hWσ x hW; rw [hx' t] at this; cases this
      show m'.memory.bytes[x]? = mem'.bytes[x]?
      rw [hP.outside x hW, hP.outside' x hW, hfree x hx']
  | buffered ht hnf hf hs hx =>
    rename_i c c' i n V'
    have hq : q.threads t = some c := by rw [hth]; exact ht
    obtain ⟨i₀, k, m', hfq, hstab, hfoot, hstep⟩ := sc_facts hown hq hnf
    have hfV := hstab _ (Silmaril.X86.MemEvent.Agree.mono hag (fun x hx => hfoot.1 (x - c.rip.toNat)
      (by omega) |> fun h => by rwa [show c.rip.toNat + (x - c.rip.toNat) = x by omega] at h))
    rw [hf] at hfV
    simp only [Option.some.injEq, Prod.mk.injEq] at hfV
    obtain ⟨rfl, rfl⟩ := hfV
    obtain ⟨hcore, hP⟩ := exec_match (Silmaril.X86.MemEvent.Agree.mono hag hfoot.2.1) hstep hfq hx
    obtain ⟨hcw, hown'⟩ := ownW_step hown hq hnf hstep
    refine ⟨_, _, ⟨⟨c, hq, hnf⟩, SCStep.go hq hstep⟩, hown', ?_⟩
    have hWσ : ∀ x, writeSet (M.accesses i c n) x → (σ t (.mem x)).isSome := hfoot.2.2
    have hσ' : ∀ u x, ((Function.update σ t (reval (σ t) (toFrag m'))) u (.mem x)).isSome =
        (σ u (.mem x)).isSome := by
      intro u x
      by_cases e : u = t
      · subst e; simp [reval_cell_isSome]
      · simp [Function.update_of_ne e]
    have hV'w : ∀ x, writeSet (M.accesses i c n) x → (V'.bytes[x]?).isSome := by
      intro x hW
      rw [hP.inside x hW]; exact (hP.wrote x hW).2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hth, hcore]
    · exact hP.regions.trans hreg
    · intro u x hc
      rw [hσ']
      by_cases e : u = t
      · subst e
        simp only [Function.update_self] at hc
        obtain ⟨en, hen, h1, h2⟩ := hc
        rcases List.mem_append.mp hen with hen | hen
        · exact hcov u x ⟨en, hen, h1, h2⟩
        · simp only [storeEntries, List.mem_map, List.mem_filter] at hen
          obtain ⟨ev, ⟨hev, hwr⟩, rfl⟩ := hen
          simp only [readSpan, List.length_map, List.length_range] at h2
          exact hWσ x ⟨ev, hev, hwr, h1, h2⟩
      · simp only [Function.update_of_ne e] at hc
        exact hcov u x hc
    · intro u x hxs
      rw [hσ'] at hxs
      show m'.memory.bytes[x]? = (overlay p.memory (Function.update p.buffer t _ u)).bytes[x]?
      by_cases e : u = t
      · subst e
        simp only [Function.update_self]
        rw [overlay_append, overlay_storeEntries hV'w (fun x hW => hP.outside' x hW)]
        by_cases hW : writeSet (M.accesses i c n) x
        · exact (hP.inside x hW).symm
        · rw [hP.outside x hW, hP.outside' x hW, howned u x hxs]
      · simp only [Function.update_of_ne e]
        have hW : ¬ writeSet (M.accesses i c n) x := fun hW => by
          rcases hown.cell e x with e1 | e1
          · rw [e1] at hxs; cases hxs
          · have := hWσ x hW; rw [e1] at this; cases this
        rw [hP.outside x hW, howned u x hxs]
    · intro x hxs
      have hx' : ∀ u, σ u (.mem x) = none := fun u => by
        have := hσ' u x; rw [hxs u] at this; simpa using this.symm
      have hW : ¬ writeSet (M.accesses i c n) x := fun hW => by
        have := hWσ x hW; rw [hx' t] at this; cases this
      show m'.memory.bytes[x]? = p.memory.bytes[x]?
      rw [hP.outside x hW, hfree x hx']

/-- **A flush is simulated by no step.** -/
theorem sim_flush (hown : OwnW M Fin σ r Q q) (hsim : Sim σ p q) {p' : TPool Tid}
    (hfl : TsoFlush p p') : Sim σ p' q := by
  obtain ⟨hth, hreg, hcov, howned, hfree⟩ := hsim
  cases hfl with
  | head hb =>
    rename_i t a bs rest
    have hnc : ∀ x, a ≤ x ∧ x < a + bs.length → (σ t (.mem x)).isSome :=
      fun x hx => hcov t x ⟨(a, bs), by rw [hb]; exact List.mem_cons_self, hx⟩
    refine ⟨hth, hreg, ?_, ?_, ?_⟩
    · intro u x hc
      by_cases e : u = t
      · subst e
        simp only [Function.update_self] at hc
        obtain ⟨en, hen, h⟩ := hc
        exact hcov u x ⟨en, by rw [hb]; exact List.mem_cons_of_mem _ hen, h⟩
      · simp only [Function.update_of_ne e] at hc
        exact hcov u x hc
    · intro u x hx
      by_cases e : u = t
      · subst e
        simp only [Function.update_self]
        rw [howned u x hx, hb]
        rfl
      · simp only [Function.update_of_ne e]
        rw [howned u x hx]
        refine overlay_congr _ ?_
        show p.memory.bytes[x]? = (Memory.install p.memory.bytes a bs)[x]?
        rw [install_get_of_not_covers]
        intro hc
        rcases hown.cell e x with e1 | e1
        · rw [e1] at hx; cases hx
        · have := hnc x hc; rw [e1] at this; cases this
    · intro x hx
      rw [hfree x hx]
      show p.memory.bytes[x]? = (Memory.install p.memory.bytes a bs)[x]?
      rw [install_get_of_not_covers]
      intro hc
      have := hnc x hc; rw [hx t] at this; cases this

/-- **Every TSO-reachable pool is simulated by an SC-reachable one.** -/
theorem sim_reach {p₀ : Pool Tid} (hown : OwnW M Fin σ r Q p₀) {p : TPool Tid}
    (hr : TsoReach M Fin (TPool.ofPool p₀) p) :
    ∃ σ' q, SCReach M.step Fin p₀ q ∧ OwnW M Fin σ' r Q q ∧ Sim σ' p q := by
  induction hr with
  | refl =>
    refine ⟨σ, p₀, .refl, hown, rfl, rfl, ?_, ?_, ?_⟩
    · rintro t x ⟨e, he, -⟩; cases he
    · intro t x _; rfl
    · intro x _; rfl
  | tail _ hst ih =>
    obtain ⟨σ', q, hrq, hown', hsim⟩ := ih
    rcases hst with ⟨t, hst⟩ | hfl
    · obtain ⟨σ'', q', hsc, hown'', hsim'⟩ := sim_tsoStep hown' hsim hst
      exact ⟨σ'', q', .tail hrq ⟨t, hsc⟩, hown'', hsim'⟩
    · exact ⟨σ', q, hrq, hown', sim_flush hown' hsim hfl⟩

end Step

end Drf

open Drf in
/-- **DRF for footprint-ownership-safe TSO pools.** Every drained state that the TSO pool of
a footprint-ownership-safe pool reaches is reached by the SC pool. -/
theorem drfTso : Task.drfTso := by
  intro Tid _ M Fin p₀ hown p hr hd
  obtain ⟨σ, r, Q, hw⟩ := hown
  obtain ⟨σ', q, hrq, -, hth, hreg, -, howned, hfree⟩ := sim_reach (σ := σ) (r := r) (Q := Q) hw hr
  have hmem : q.memory = p.memory := by
    have hb : q.memory.bytes = p.memory.bytes := by
      apply Std.ExtHashMap.ext_getElem?
      intro x
      by_cases h : ∃ t, (σ' t (.mem x)).isSome
      · obtain ⟨t, ht⟩ := h
        rw [howned t x ht, hd t, overlay_nil]
      · refine hfree x (fun t => ?_)
        cases e : σ' t (.mem x) with
        | none => rfl
        | some _ => exact absurd ⟨t, by rw [e]; rfl⟩ h
    cases hq : q.memory
    cases hp : p.memory
    rw [hq, hp] at hreg hb
    simp_all
  have : forget p = q := by
    cases q; simp only [forget] at *; rw [hth, hmem]
  rw [this]; exact hrq

end Silmaril.Proofs.X86.Pool
