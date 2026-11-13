module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp.Read

/-!
# The XL bridge: machine steps between closed-form configurations

Proofs for `Csl.Task.cirXlOpAx`: silent steps, one label step of a thread (buffered
or drained), flushes, the tick invariant `Inv`, and catching a thread up over labels that have
no trigger (`H.catchup`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte Loc)
open Silmaril.Proofs.X86.Concurrency.Cir.Domain (covers_iff cellsOf LocsFacts)

/-! ## Generic machine facts -/

theorem star_trans {α : Type} {r : α → α → Prop} {a b c : α} (h₁ : Star r a b) (h₂ : Star r b c) :
    Star r a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem star_one {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b := .step h .refl

@[simp] theorem upd_same {α : Type} (f : Nat → α) (i : Nat) (v : α) : upd f i v i = v := by simp [upd]
theorem upd_ne {α : Type} (f : Nat → α) {i j : Nat} (v : α) (h : j ≠ i) : upd f i v j = f j := by
  simp [upd, h]
theorem upd_self {α : Type} (f : Nat → α) (i : Nat) : upd f i (f i) = f := by
  funext j; by_cases h : j = i <;> simp [upd, h]
theorem upd_upd {α : Type} (f : Nat → α) (i : Nat) (v w : α) : upd (upd f i v) i w = upd f i w := by
  funext j; by_cases h : j = i <;> simp [upd, h]

theorem reach_taus {M : OModel} {N i : Nat} (hi : i < N) :
    ∀ {a b : Stmt × Regs}, Star TauR a b → ∀ C : OCfg, C.ts i = a →
      OReach M N C { C with ts := upd C.ts i b } := by
  intro a b hab
  induction hab with
  | refl =>
    intro C hC
    rw [← hC, upd_self]; exact Star.refl
  | @step a a' b hst _ ih =>
    intro C hC
    have h1 : OStep M N C { C with ts := upd C.ts i a' } := .tau hi (by rw [hC]; exact hst)
    have h2 := ih { C with ts := upd C.ts i a' } (by simp)
    simp only [upd_upd] at h2
    exact .step h1 h2

theorem reach_bars {N i : Nat} (hi : i < N) :
    ∀ (l : List Ent) (C : OCfg), C.buf i = l →
      OReach .xl N C { C with buf := upd C.buf i (l.dropWhile (· == .bar)) }
  | [], C, hC => by simp only [List.dropWhile_nil]; rw [← hC, upd_self]; exact Star.refl
  | e :: l, C, hC => by
    simp only [List.dropWhile_cons]
    split
    · rename_i he
      simp only [beq_iff_eq] at he; subst he
      have h1 : OStep .xl N C { C with mem := Ent.bar.apply C.mem, buf := upd C.buf i ([] ++ l) } :=
        .flush hi (pre := []) (by rw [hC]; rfl) (by simp [Ent.passes]) (.inr rfl)
      have h2 := reach_bars hi l { C with mem := Ent.bar.apply C.mem, buf := upd C.buf i ([] ++ l) }
        (by simp)
      simp only [Ent.apply, List.nil_append, upd_upd] at h1 h2
      exact .step h1 h2
    · rw [← hC, upd_self]; exact Star.refl

theorem dropWhile_dropWhile_append (l m : List Ent) :
    ((l.dropWhile (· == .bar)) ++ m).dropWhile (· == .bar) = (l ++ m).dropWhile (· == .bar) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases he : (e == Ent.bar) = true
    · simp only [List.dropWhile_cons, he, ↓reduceIte, List.cons_append]; exact ih
    · simp [he]

/-! ## The runs, cut -/

/-- Each thread's run, cut at its labels. -/
structure Runs (P : Prog) (L : Nat → List Lab) (R : Nat → Regs) (S Pre : Nat → Nat → Stmt × Regs) :
    Prop where
  cut : ∀ i (hi : i < P.threads.length),
    Cut P.threads[i].body Regs.zero (L i) (.skip, R i) (S i) (Pre i)
  out : ∀ i, P.threads.length ≤ i → ∀ c, S i c = (.skip, Regs.zero)

/-! ## The tick invariant -/

/-- What has been executed at tick `T`: every executed label's trigger is before `T`, and every
label with a trigger or a native store before `T` is executed. -/
structure Inv (L : Nat → List Lab) (x : Exec) (T : Nat) (cnt : Nat → Nat) : Prop where
  le : ∀ i, cnt i ≤ (L i).length
  past : ∀ i c (hc : c < (L i).length) k, c < cnt i → trig (L i)[c] = some k →
    κ x (pidx x i (base L i c + k)) < T
  trigDone : ∀ i c (hc : c < (L i).length) k, trig (L i)[c] = some k →
    κ x (pidx x i (base L i c + k)) < T → c < cnt i
  stDone : ∀ i c (hc : c < (L i).length), ∀ e ∈ nsts (L i)[c],
    κ x (pidx x i (base L i c + e.1)) < T → c < cnt i

/-! ## Labels: memory effects -/

theorem cellLast_some : ∀ {cs : List (Nat × Nat × Nat)} {a : Nat}, (cellLast cs a).isSome →
    ∃ c ∈ cs, c.1 = a
  | [], _, h => by simp [cellLast] at h
  | c :: cs, a, h => by
    simp only [cellLast, Option.isSome_or] at h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨c', hc', he⟩ := cellLast_some h
      exact ⟨c', List.mem_cons_of_mem _ hc', he⟩
    · split at h
      · exact ⟨c, List.mem_cons_self, by assumption⟩
      · simp at h

/-- A cell a label touches is a location's. -/
theorem touch_loc {cs : List (Nat × Nat)} {bs : List Block} {l : Lab}
    (hl : Silmaril.Proofs.X86.Concurrency.Cir.Domain.LabOk cs bs l) {a : Nat} (ht : l.Touches a) :
    ∃ sz, (a, sz) ∈ cs := by
  rcases ht with ⟨v, hv⟩ | hw
  · cases l with
    | rd => simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hv; obtain ⟨rfl, -⟩ := hv; exact ⟨_, hl.1⟩
    | rmw => simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hv; obtain ⟨rfl, -⟩ := hv; exact ⟨_, hl.1⟩
    | fwait => simp only [Lab.reads, List.mem_singleton, Prod.mk.injEq] at hv; obtain ⟨rfl, -⟩ := hv; exact ⟨_, hl.1⟩
    | fblock => exact (hl : False).elim
    | blk nm ins outs rvs =>
      simp only [Lab.reads, List.mem_map, Prod.mk.injEq] at hv
      obtain ⟨c, hc, rfl, -⟩ := hv
      exact ⟨_, (hl.1 c (List.mem_append_left _ hc)).1⟩
    | _ => simp [Lab.reads] at hv
  · cases l with
    | wr => simp only [Lab.wval] at hw; split at hw <;> simp_all; exact ⟨_, hl.1⟩
    | rmw => simp only [Lab.wval] at hw; split at hw <;> simp_all; exact ⟨_, hl.1⟩
    | blk nm ins outs rvs =>
      simp only [Lab.wval] at hw
      obtain ⟨c, hc, rfl⟩ := cellLast_some hw
      exact ⟨_, (hl.1 c (List.mem_append_right _ hc)).1⟩
    | _ => simp [Lab.wval] at hw

theorem nMem_some {P : Prog} {x : Exec} {T a sz : Nat} (hl : LocsFacts P.locs)
    (h : (a, sz) ∈ cellsOf P.locs) : (nMem P x T a).isSome := by
  obtain ⟨l, hlm, rfl, -⟩ := loc_of_cell hl h
  rw [nMem_loc hl hlm]; rfl

theorem idxd_map (k : Nat) : ∀ (cs : List (Nat × Nat × Nat)),
    (idxd k cs).map (fun e => Ent.st e.2.1 e.2.2 false) = cs.map fun c => .st c.1 c.2.2 false
  | [] => rfl
  | c :: cs => by simp [idxd, idxd_map (k + 1) cs]

/-- The buffer entries of a label are its native stores (or the `sfence` barrier). -/
theorem ents_eq {l : Lab} (hl : LabG l) (hs : l ≠ .fence .sfence) :
    l.ents = (nsts l).map fun e => .st e.2.1 e.2.2 false := by
  cases l with
  | wr m fl a sz v => simp only [LabG] at hl; subst hl; simp [Lab.ents, nsts]
  | blk nm ins outs rvs => simp [Lab.ents, nsts, idxd_map]
  | fence k => cases k <;> simp_all [Lab.ents, nsts]
  | _ => simp [Lab.ents, nsts]

theorem labEnts_get {L : Nat → List Lab} {x : Exec} {T i c : Nat} (hc : c < (L i).length) :
    labEnts L x T i c = if (L i)[c] = .fence .sfence then [(base L i c, .bar)] else
      ((nsts (L i)[c]).filter fun e => decide (T ≤ κ x (pidx x i (base L i c + e.1)))).map
        fun e => (base L i c + e.1, .st e.2.1 e.2.2 false) := by
  simp [labEnts, List.getElem?_eq_getElem hc]

/-- When all its native stores are at or after `T`, a label's tagged entries are its buffer
entries. -/
theorem labEnts_ents {L : Nat → List Lab} {x : Exec} {T i c : Nat} (hc : c < (L i).length)
    (hl : LabG (L i)[c])
    (hst : ∀ e ∈ nsts (L i)[c], T ≤ κ x (pidx x i (base L i c + e.1))) :
    (labEnts L x T i c).map Prod.snd = (L i)[c].ents := by
  rw [labEnts_get hc]
  split
  · rename_i hs; rw [hs]; rfl
  · rename_i hs
    rw [ents_eq hl hs, List.filter_eq_self.mpr (fun e he => by simpa using hst e he)]
    simp

theorem rawP_succ {L : Nat → List Lab} {x : Exec} {T : Nat} {cnt : Nat → Nat} {i : Nat} :
    rawP L x T (upd cnt i (cnt i + 1)) i = rawP L x T cnt i ++ labEnts L x T i (cnt i) := by
  simp [rawP, upd, List.range_succ, List.flatMap_append]

theorem rawP_ne {L : Nat → List Lab} {x : Exec} {T : Nat} {cnt : Nat → Nat} {i j : Nat} (v : Nat)
    (h : j ≠ i) : rawP L x T (upd cnt i v) j = rawP L x T cnt j := by
  simp [rawP, upd, h]

theorem nBuf_ne {L : Nat → List Lab} {x : Exec} {T : Nat} {cnt : Nat → Nat} {i j : Nat} (v : Nat)
    (h : j ≠ i) : nBuf L x T (upd cnt i v) j = nBuf L x T cnt j := by
  simp [nBuf, rawP_ne v h]

theorem nBuf_succ {L : Nat → List Lab} {x : Exec} {T : Nat} {cnt : Nat → Nat} {i : Nat} :
    nBuf L x T (upd cnt i (cnt i + 1)) i =
      (nBuf L x T cnt i ++ (labEnts L x T i (cnt i)).map Prod.snd).dropWhile (· == .bar) := by
  simp only [nBuf, rawP_succ, List.map_append, dropWhile_dropWhile_append]

/-- Thread `i`'s buffer is empty when every native store of its executed labels is before `T`. -/
theorem nBuf_nil {L : Nat → List Lab} {x : Exec} {T : Nat} {cnt : Nat → Nat} {i : Nat}
    (h : ∀ c (hc : c < (L i).length), c < cnt i → ∀ e ∈ nsts (L i)[c],
      κ x (pidx x i (base L i c + e.1)) < T) : nBuf L x T cnt i = [] := by
  apply dropWhile_nil_of
  intro e he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  obtain ⟨c, hcn, hq⟩ := mem_rawP.mp hq
  obtain ⟨hc, ⟨-, rfl⟩ | ⟨-, e', he', hT, rfl⟩⟩ := mem_labEnts hq
  · rfl
  · have := h c hc hcn e' he'; omega


/-! ## Steps between closed forms -/

theorem reach_flush {N i : Nat} (hi : i < N) (C : OCfg) {a v : Nat} {rest : List Ent}
    (hb : C.buf i = .st a v false :: rest) :
    OReach .xl N C ⟨C.ts, fun y => if y = a then some v else C.mem y,
      upd C.buf i (rest.dropWhile (· == .bar))⟩ := by
  have h1 : OStep .xl N C ⟨C.ts, Ent.apply C.mem (Ent.st a v false), upd C.buf i ([] ++ rest)⟩ :=
    .flush hi (pre := []) (by rw [hb]; rfl) (by simp [Ent.passes]) (.inr rfl)
  have h2 := reach_bars hi rest ⟨C.ts, Ent.apply C.mem (Ent.st a v false), upd C.buf i ([] ++ rest)⟩
    (by simp)
  simp only [List.nil_append, upd_upd] at h1 h2
  exact .step h1 h2

theorem cfg_ts {S : Nat → Nat → Stmt × Regs} {cnt : Nat → Nat} {i : Nat} (v : Nat) (s : Stmt × Regs)
    (hs : s = S i v) : upd (fun j => S j (cnt j)) i s = fun j => S j (upd cnt i v j) := by
  funext j; by_cases hj : j = i
  · subst hj; simp [hs]
  · simp [upd, hj]

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)} {R : Nat → Regs}
  {S Pre : Nat → Nat → Stmt × Regs}

/-- **A buffered label step**, then the barriers at the front are flushed. -/
theorem Runs.step_buf (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i : Nat}
    (hi : i < P.threads.length) (hc : cnt i < (L i).length)
    (hm : (L i)[cnt i].isMem = true) (hd : (L i)[cnt i].drains = false)
    (htouch : ∀ a, (L i)[cnt i].Touches a → (nMem P x T a).isSome)
    (hok : (L i)[cnt i].okH (view (nMem P x T) (nBuf L x T cnt i)))
    (hents : (labEnts L x T i (cnt i)).map Prod.snd = (L i)[cnt i].ents) :
    OReach .xl P.threads.length (cfg P L x S T cnt) (cfg P L x S T (upd cnt i (cnt i + 1))) := by
  have hcut := hr.cut i hi
  have r1 := reach_taus (M := .xl) hi (hcut.taus (cnt i) hc) (cfg P L x S T cnt) rfl
  have st : OStep .xl P.threads.length
      ⟨upd (fun j => S j (cnt j)) i (Pre i (cnt i)), nMem P x T, nBuf L x T cnt⟩
      ⟨upd (upd (fun j => S j (cnt j)) i (Pre i (cnt i))) i
          ((S i (cnt i + 1)).1, (S i (cnt i + 1)).2), nMem P x T,
        upd (nBuf L x T cnt) i (nBuf L x T cnt i ++ (L i)[cnt i].ents)⟩ :=
    .buffered hi (by simpa using hcut.step (cnt i) hc) hm hd htouch hok
  have r3 := reach_bars (N := P.threads.length) hi _
    ⟨upd (upd (fun j => S j (cnt j)) i (Pre i (cnt i))) i
          ((S i (cnt i + 1)).1, (S i (cnt i + 1)).2), nMem P x T,
        upd (nBuf L x T cnt) i (nBuf L x T cnt i ++ (L i)[cnt i].ents)⟩ rfl
  have heq : (⟨upd (upd (fun j => S j (cnt j)) i (Pre i (cnt i))) i
          ((S i (cnt i + 1)).1, (S i (cnt i + 1)).2), nMem P x T,
        upd (upd (nBuf L x T cnt) i (nBuf L x T cnt i ++ (L i)[cnt i].ents)) i
          ((upd (nBuf L x T cnt) i (nBuf L x T cnt i ++ (L i)[cnt i].ents) i).dropWhile
            (· == .bar))⟩ : OCfg) = cfg P L x S T (upd cnt i (cnt i + 1)) := by
    simp only [cfg, upd_upd, upd_same, OCfg.mk.injEq, true_and]
    refine ⟨cfg_ts (cnt i + 1) _ (by simp), ?_⟩
    funext j; by_cases hj : j = i
    · subst hj; simp [nBuf_succ, hents]
    · simp [upd, hj, nBuf_ne _ hj]
  rw [← heq]
  exact star_trans r1 (.step st r3)

/-- **A draining label step** (the buffer is empty). -/
theorem Runs.step_drain (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i : Nat}
    (hi : i < P.threads.length) (hc : cnt i < (L i).length)
    (hm : (L i)[cnt i].isMem = true) (hd : (L i)[cnt i].drains = true)
    (he : nBuf L x T cnt i = [])
    (htouch : ∀ a, (L i)[cnt i].Touches a → (nMem P x T a).isSome)
    (hok : (L i)[cnt i].okH (nMem P x T)) (hnil : labEnts L x T i (cnt i) = []) :
    OReach .xl P.threads.length (cfg P L x S T cnt)
      ⟨fun j => S j (upd cnt i (cnt i + 1) j), (L i)[cnt i].updH (nMem P x T),
        nBuf L x T (upd cnt i (cnt i + 1))⟩ := by
  have hcut := hr.cut i hi
  have r1 := reach_taus (M := .xl) hi (hcut.taus (cnt i) hc) (cfg P L x S T cnt) rfl
  have st : OStep .xl P.threads.length
      ⟨upd (fun j => S j (cnt j)) i (Pre i (cnt i)), nMem P x T, nBuf L x T cnt⟩
      ⟨upd (upd (fun j => S j (cnt j)) i (Pre i (cnt i))) i
          ((S i (cnt i + 1)).1, (S i (cnt i + 1)).2), (L i)[cnt i].updH (nMem P x T),
        nBuf L x T cnt⟩ :=
    .drained hi (by simpa using hcut.step (cnt i) hc) hm hd he htouch hok
  have heq : (⟨upd (upd (fun j => S j (cnt j)) i (Pre i (cnt i))) i
          ((S i (cnt i + 1)).1, (S i (cnt i + 1)).2), (L i)[cnt i].updH (nMem P x T),
        nBuf L x T cnt⟩ : OCfg) = ⟨fun j => S j (upd cnt i (cnt i + 1) j),
          (L i)[cnt i].updH (nMem P x T), nBuf L x T (upd cnt i (cnt i + 1))⟩ := by
    simp only [upd_upd, OCfg.mk.injEq, true_and]
    refine ⟨cfg_ts (cnt i + 1) _ (by simp), ?_⟩
    funext j; by_cases hj : j = i
    · subst hj; simp [nBuf_succ, hnil, he]
    · simp [nBuf_ne _ hj]
  rw [← heq]
  exact star_trans r1 (star_one st)

end

/-! ## Labels without a trigger -/

theorem lazy_cases {l : Lab} (hl : LabG l) (ht : trig l = none) :
    (∃ m a sz v, l = .wr m .wb a sz v) ∨ (∃ k, l = .fence k) ∨
      ∃ nm outs rvs, l = .blk nm [] outs rvs := by
  cases l with
  | wr m fl a sz v => simp only [LabG] at hl; subst hl; exact .inl ⟨m, a, sz, v, rfl⟩
  | fence k => exact .inr (.inl ⟨k, rfl⟩)
  | blk nm ins outs rvs =>
    simp only [trig] at ht
    split at ht
    · rename_i hn; subst hn; exact .inr (.inr ⟨nm, outs, rvs, rfl⟩)
    · cases ht
  | rd => simp [trig] at ht
  | rmw => simp [trig] at ht
  | fwait => simp only [trig] at ht; split at ht <;> cases ht
  | fwake => simp [trig] at ht
  | _ => simp [LabG] at hl

theorem updH_fence (k : Silmaril.X86.Atomic9.FenceKind) (M : Heap) : (Lab.fence k).updH M = M := by
  funext a; simp [Lab.updH, Lab.wval]


/-! ## Catching up -/

/-- Reachable from the start. -/
def Reach (P : Prog) (L : Nat → List Lab) (x : Exec) (S : Nat → Nat → Stmt × Regs) (T : Nat)
    (cnt : Nat → Nat) : Prop :=
  OReach .xl P.threads.length (progInit P).toO (cfg P L x S T cnt)

section
variable {P : Prog} {L : Nat → List Lab} {x : Exec} {U : List (Ev × List Byte)} {R : Nat → Regs}
  {S Pre : Nat → Nat → Stmt × Regs}

theorem Inv.upd_mono {T : Nat} {cnt : Nat → Nat} (hI : Inv L x T cnt) {i v : Nat}
    (hv : cnt i ≤ v) (hvL : v ≤ (L i).length)
    (hnt : ∀ c (hc : c < (L i).length), cnt i ≤ c → c < v → trig (L i)[c] = none) :
    Inv L x T (upd cnt i v) := by
  refine ⟨fun j => ?_, fun j c hc k hcj ht => ?_, fun j c hc k ht hk => ?_, fun j c hc e he hk => ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using hvL
    · rw [upd_ne _ _ hj]; exact hI.le j
  · by_cases hj : j = i
    · subst hj
      rw [upd_same] at hcj
      by_cases hcc : c < cnt j
      · exact hI.past j c hc k hcc ht
      · rw [hnt c hc (by omega) hcj] at ht; cases ht
    · rw [upd_ne _ _ hj] at hcj; exact hI.past j c hc k hcj ht
  · have := hI.trigDone j c hc k ht hk
    by_cases hj : j = i
    · subst hj; rw [upd_same]; omega
    · rw [upd_ne _ _ hj]; exact this
  · have := hI.stDone j c hc e he hk
    by_cases hj : j = i
    · subst hj; rw [upd_same]; omega
    · rw [upd_ne _ _ hj]; exact this

/-- **One label without a trigger.** -/
theorem Runs.lazyStep (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {cnt : Nat → Nat} {i : Nat}
    (hi : i < P.threads.length) (hc : cnt i < (L i).length)
    (hlazy : trig (L i)[cnt i] = none)
    (hst : ∀ e ∈ nsts (L i)[cnt i], T ≤ κ x (pidx x i (base L i (cnt i) + e.1)))
    (hmf : (L i)[cnt i] = .fence .mfence → ∀ c (hc : c < (L i).length), c < cnt i →
      ∀ e ∈ nsts (L i)[c], κ x (pidx x i (base L i c + e.1)) < T) :
    OReach .xl P.threads.length (cfg P L x S T cnt) (cfg P L x S T (upd cnt i (cnt i + 1))) := by
  obtain ⟨hG, bs, hok⟩ := h.lab i _ (List.getElem_mem hc)
  have htouch : ∀ a, (L i)[cnt i].Touches a → (nMem P x T a).isSome := fun a ha => by
    obtain ⟨sz, hsz⟩ := touch_loc hok ha
    exact nMem_some h.lf hsz
  have hents := labEnts_ents (x := x) hc hG hst
  rcases lazy_cases hG hlazy with ⟨m, a, sz, v, he⟩ | ⟨k, he⟩ | ⟨nm, outs, rvs, he⟩
  · exact hr.step_buf hi hc (by rw [he]; rfl) (by rw [he]; rfl) htouch
      (by rw [he]; intro p hp; simp [Lab.reads] at hp) hents
  · by_cases hk : k = .mfence
    · subst hk
      have hd := hr.step_drain (x := x) (T := T) (cnt := cnt) hi hc (by rw [he]; rfl)
        (by rw [he]; rfl) (nBuf_nil fun c hc' hcn e he' => hmf he c hc' hcn e he') htouch
        (by rw [he]; intro p hp; simp [Lab.reads] at hp)
        (by rw [labEnts_get hc, he]; simp [nsts])
      rw [he, updH_fence] at hd
      exact hd
    · exact hr.step_buf hi hc (by rw [he]; rfl) (by rw [he]; cases k <;> simp_all [Lab.drains])
        htouch (by rw [he]; intro p hp; simp [Lab.reads] at hp) hents
  · exact hr.step_buf hi hc (by rw [he]; rfl) (by rw [he]; rfl) htouch
      (by rw [he]; intro p hp; simp [Lab.reads] at hp) hents

/-- **Catching a thread up** over labels without a trigger. -/
theorem Runs.catchup (h : H P L x U) (hr : Runs P L R S Pre) {T : Nat} {i : Nat}
    (hi : i < P.threads.length) : ∀ (d : Nat) {cnt : Nat → Nat}, cnt i + d ≤ (L i).length →
    Inv L x T cnt →
    (∀ c (hc : c < (L i).length), cnt i ≤ c → c < cnt i + d → trig (L i)[c] = none) →
    (∀ c (hc : c < (L i).length), cnt i ≤ c → c < cnt i + d → ∀ e ∈ nsts (L i)[c],
      T ≤ κ x (pidx x i (base L i c + e.1))) →
    (∀ c (hc : c < (L i).length), cnt i ≤ c → c < cnt i + d → (L i)[c] = .fence .mfence →
      ∀ c' (hc' : c' < (L i).length), c' < c → ∀ e ∈ nsts (L i)[c'],
        κ x (pidx x i (base L i c' + e.1)) < T) →
    Reach P L x S T cnt → Inv L x T (upd cnt i (cnt i + d)) ∧ Reach P L x S T (upd cnt i (cnt i + d))
  | 0, cnt, _, hI, _, _, _, hR => by simp only [Nat.add_zero, upd_self]; exact ⟨hI, hR⟩
  | d + 1, cnt, hd, hI, hl, hs, hm, hR => by
    have hc : cnt i < (L i).length := by omega
    have s1 := hr.lazyStep h hi hc (hl _ hc le_rfl (by omega)) (hs _ hc le_rfl (by omega))
      (fun he => hm _ hc le_rfl (by omega) he)
    have hI1 : Inv L x T (upd cnt i (cnt i + 1)) :=
      hI.upd_mono (by omega) (by omega) fun c hc' h1 h2 => hl c hc' h1 (by omega)
    have := hr.catchup h hi d (cnt := upd cnt i (cnt i + 1)) (by simp; omega) hI1
      (fun c hc' h1 h2 => hl c hc' (by simp at h1; omega) (by simp at h2; omega))
      (fun c hc' h1 h2 => hs c hc' (by simp at h1; omega) (by simp at h2; omega))
      (fun c hc' h1 h2 => hm c hc' (by simp at h1; omega) (by simp at h2; omega))
      (star_trans hR s1)
    simp only [upd_same, upd_upd] at this
    rw [show cnt i + 1 + d = cnt i + (d + 1) by omega] at this
    exact this

end

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.XlOp
