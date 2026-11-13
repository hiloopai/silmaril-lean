module

public import Silmaril.X86.MemoryModel.Litmus.Closure.Defs
public import Silmaril.X86.Litmus.Domain.Thms
public import Silmaril.X86.MemoryModel.Xl.Thms
public import Silmaril.Proofs.X86.MemoryModel.Litmus.Closure.Units
public import Silmaril.Proofs.X86.MemoryModel.Litmus.Closure.Rank
import Silmaril.X86.Ext.Store

/-!
# Domain closure: the theorem

Proof of `closure_of_cert` for `Silmaril/X86/MemoryModel/Litmus/Closure/Thms.lean`. The steps:

1. **Skeleton.** The certificate's `straight` check gives each thread a skeleton with at most
   one event per step; every trace of the thread over every domain has it (`extract_skel`), so
   every choice of traces has the units of `Test.reps` up to bytes (`accUnits_shape`). Hence
   no unit tears (`units = accUnits`), every pair of units is in one cell or disjoint, and the
   number of read units is the certificate's `R`.
2. **Rank.** `reads_in_level` with level `k` meaning "a value of `Test.chain k`": initial bytes
   are in `chain 0` (certificate), and a write whose earlier reads are in `chain k` writes a
   value of `chain (k + 1)`: the trace's prefix up to the write is, by `extract_prefix`, a
   prefix of a trace over `chain k`, whose written values `domStep` adds.
3. **Restriction.** Every read is in `chain R ⊆ Test.domain`, so by `extract_restrict` each
   chosen trace is one of `Test.traces`, and the same candidate execution witnesses `AxReach`.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Closure

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)
open Silmaril.X86.Litmus (Act Trace StepRec InDom)

/-! ## Lists -/

theorem mapM_spec {α β : Type} (f : α → Option β) :
    ∀ {L : List α} {T : List β}, L.mapM f = some T →
      T.length = L.length ∧ ∀ (k : Nat) (h : k < L.length) (h' : k < T.length), f L[k] = some T[k]
  | [], T, h => by simp at h; subst h; exact ⟨rfl, fun k h => by simp at h⟩
  | a :: L, T, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapM_spec f hl
    refine ⟨by simp [h1], fun k hk hk' => ?_⟩
    cases k with
    | zero => simpa using hy
    | succ k => simpa using h2 k (by simpa using hk) (by simpa using hk')

theorem flatMap_single {α : Type} (g : α → List α) :
    ∀ (l : List α), (∀ u ∈ l, g u = [u]) → l.flatMap g = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, h a (by simp), flatMap_single g l (fun u hu => h u (by simp [hu]))]
    rfl

theorem take_flatten_boundary {α : Type} :
    ∀ (L : List (List α)), (∀ l ∈ L, l.length ≤ 1) → ∀ n, n ≤ L.flatten.length →
      ∃ m, (L.take m).flatten = L.flatten.take n
  | [], _, n, _ => ⟨0, by simp⟩
  | l :: L, hL, n, hn => by
    have hL' : ∀ l ∈ L, l.length ≤ 1 := fun l h => hL l (by simp [h])
    cases n with
    | zero => exact ⟨0, by simp⟩
    | succ n =>
      match l, hL (l) (by simp) with
      | [], _ =>
        obtain ⟨m, hm⟩ := take_flatten_boundary L hL' (n + 1) (by simpa using hn)
        exact ⟨m + 1, by simpa using hm⟩
      | [a], _ =>
        obtain ⟨m, hm⟩ := take_flatten_boundary L hL' n
          (by simp only [List.flatten_cons, List.length_append, List.length_singleton] at hn; omega)
        exact ⟨m + 1, by simp [hm]⟩
      | _ :: _ :: _, h => simp at h

/-! ## Units -/

theorem actUnits_acc {i p : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits i p a) :
    u.1.accSize = u.1.size := by
  unfold actUnits at h
  split at h <;> simp at h <;> (try rcases h with h | h) <;> (try subst h) <;> rfl

theorem accUnits_acc {trs : List XTrace} {u : Ev × List Byte} (h : u ∈ accUnits trs) :
    u.1.accSize = u.1.size := by
  obtain ⟨i, tr, -, hu⟩ := accUnits_mem.mp h
  obtain ⟨j, a, -, hu⟩ := threadUnits_mem.mp hu
  exact actUnits_acc hu

/-- A read action of a chosen trace has a read unit. -/
theorem read_unit_of_act {trs : List XTrace} {i : Nat} {tr : XTrace} (hi : trs[i]? = some tr)
    {j : Nat} {a : XAct} (hj : tr.acts[j]? = some a) (hr : a.ev.kind.reads = true) :
    ∃ (n : Nat) (hn : n < (accUnits trs).length), (accUnits trs)[n].1.isR = true ∧
      (accUnits trs)[n].1.tid = i ∧ (accUnits trs)[n].1.pos = posOff tr.acts j ∧
      (accUnits trs)[n].2 = a.rd := by
  obtain ⟨u, hu, hR, htid, hpos, hrd⟩ := actUnits_read_exists i (0 + posOff tr.acts j) a hr
  have hmem : u ∈ accUnits trs := accUnits_mem.mpr ⟨i, tr, hi, threadUnits_mem.mpr ⟨j, a, hj, hu⟩⟩
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hmem
  exact ⟨n, hn, hR, htid, by simpa using hpos, hrd⟩

/-- What a write unit of a choice of traces is. -/
theorem write_unit_info {trs : List XTrace} {n : Nat} (hn : n < (accUnits trs).length)
    (hw : (accUnits trs)[n].1.isW = true) :
    ∃ i tr j a, trs[i]? = some tr ∧ tr.acts[j]? = some a ∧ a.ev.kind.writes = true ∧
      (accUnits trs)[n].1.tid = i ∧ posOff tr.acts j ≤ (accUnits trs)[n].1.pos ∧
      (a.ev.kind.reads = true → posOff tr.acts j < (accUnits trs)[n].1.pos) ∧
      (accUnits trs)[n].1.data = a.wr := by
  obtain ⟨i, tr, hi, hu⟩ := accUnits_mem.mp (List.getElem_mem hn)
  obtain ⟨j, a, hj, hu⟩ := threadUnits_mem.mp hu
  obtain ⟨hW, hle, hlt, hd, -, -⟩ := actUnits_write hu hw
  exact ⟨i, tr, j, a, hi, hj, hW, actUnits_tid hu, by simpa using hle,
    fun h => by simpa using hlt h, hd⟩

theorem singleCopy_of_untorn {us : List (Ev × List Byte)} {u : Ev} (h : tearAcc us u = false)
    (hM : u.isM = true) : u.singleCopy = true := by
  simp only [tearAcc, hM, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
  exact h.1

theorem wf_data {x : Exec} (h : x.Wf = true) {e : Ev} (he : e ∈ x.evs) (hw : e.isW = true) :
    e.data.length = e.size := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 e he
  have hM : e.isM = true := isM_of_isW hw
  simp only [hM, ite_true, Bool.and_eq_true, decide_eq_true_eq, hw, Bool.not_true,
    Bool.false_or, beq_iff_eq] at this
  exact this.2

theorem bytes_map_byte {e : Ev} (h : e.data.length = e.size) : e.bytes.map e.byte = e.data := by
  apply List.ext_getElem (by simp [Ev.bytes, h])
  intro n h1 h2
  simp [Ev.bytes, Ev.byte, List.getElem_range']
  rw [List.getElem?_eq_getElem h2]
  rfl

theorem inDom_mono {D D' : List Nat} (h : ∀ v ∈ D, v ∈ D') {bs : List Byte} (hb : InDom D bs) :
    InDom D' bs := by
  obtain ⟨v, hv, he⟩ := hb
  exact ⟨v, h v hv, he⟩

/-! ## Threads -/

theorem straight_spec {t : Test} (h : t.straight = true) {k : Nat} (hk : k < t.threads.length) :
    ∃ S, (t.xthread k t.threads[k]).skel t.fuel = some S ∧ ∀ es ∈ S, es.length ≤ 1 := by
  unfold Test.straight at h
  rw [List.all_eq_true] at h
  have := h _ (List.mem_mapIdx.mpr ⟨k, hk, rfl⟩)
  revert this
  split
  · rename_i S hS
    intro h'
    exact ⟨S, hS, fun es hes => by simpa using (List.all_eq_true.mp h') es hes⟩
  · simp

theorem trace_skel {th : Silmaril.X86.Litmus.Thread} {D : List Nat} {fuel f : Nat}
    {trs : List XTrace} {S : List (List Silmaril.X86.MemEvent.Event)}
    (h : Silmaril.X86.Litmus.extract th D fuel = some trs) (hS : th.skel f = some S)
    (h1 : ∀ es ∈ S, es.length ≤ 1) {tr : XTrace} (htr : tr ∈ trs) :
    tr.acts.map Act.ev = S.flatten ∧ ∀ st ∈ tr.steps, st.acts.length ≤ 1 := by
  have e := Silmaril.X86.Litmus.extract_skel h hS tr htr
  refine ⟨?_, fun st hst => ?_⟩
  · rw [← e, Trace.acts, List.map_flatMap, List.flatMap_def]
  · have := h1 _ (e ▸ List.mem_map_of_mem hst)
    simpa using this

theorem choice_thread {t : Test} {D : List Nat} {T : List (List XTrace)}
    (hT : t.extractOver D = some T) {trs : List XTrace} (hF : List.Forall₂ (· ∈ ·) trs T)
    {i : Nat} (hi : i < trs.length) :
    ∃ (hk : i < t.threads.length) (trsI : List XTrace), T[i]? = some trsI ∧
      Silmaril.X86.Litmus.extract (t.xthread i t.threads[i]) D t.fuel = some trsI ∧
      trs[i] ∈ trsI := by
  have hlen := hF.length_eq
  have hlen' := extractOver_length hT
  have hk : i < t.threads.length := by omega
  obtain ⟨trsI, h1, h2⟩ := extractOver_thread hT (List.getElem?_eq_getElem hk)
  have hiT : i < T.length := by omega
  have hg := hF.get hi hiT
  have : T[i] = trsI := by
    rw [List.getElem?_eq_getElem hiT] at h1
    exact Option.some.inj h1
  exact ⟨hk, trsI, h1, h2, by simpa [this] using hg⟩

theorem countR (l : List (Ev × List Byte)) :
    ((l.map (shape ∘ Prod.fst)).filter Ev.isR).length = (l.filter fun u => u.1.isR).length := by
  rw [List.filter_map, List.length_map]
  rfl

theorem countR' (l : List (Ev × List Byte)) :
    ((l.map Prod.fst).filter Ev.isR).length = (l.filter fun u => u.1.isR).length := by
  rw [List.filter_map, List.length_map]
  rfl

/-! ## The theorem -/

theorem mem_acts_take {tr : XTrace} {n : Nat} {a : XAct} (h : a ∈ tr.acts.take n) :
    ∃ j : Nat, j < n ∧ tr.acts[j]? = some a := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp h
  refine ⟨j, by simp at hj; omega, ?_⟩
  rw [← he, List.getElem_take]
  simp

theorem mem_acts {tr : XTrace} {st : StepRec} (hst : st ∈ tr.steps) {a : XAct} (ha : a ∈ st.acts) :
    ∃ j : Nat, tr.acts[j]? = some a := by
  have : a ∈ tr.acts := List.mem_flatMap.mpr ⟨st, hst, ha⟩
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp this
  exact ⟨j, by rw [← he]; simp⟩

/-- **Domain closure from the certificate.** -/
theorem closure_of_cert {t : Test} (hc : t.closureCert = true) {M : Exec → Prop}
    (hM : ∀ x, M x → x.Xl) {f : Final} (h : AxReachAny t M f) :
    ∃ T, t.traces = some T ∧ AxReach t T M f := by
  obtain ⟨D, TD, hD, trs, hF, x, hevs, hrmw, hwf, hrok, hMx, hf⟩ := h
  unfold Test.closureCert at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hst, hm⟩ := hc
  cases hTT : t.traces with
  | none => rw [hTT] at hm; simp at hm
  | some TT =>
  cases hRp : t.reps with
  | none => rw [hTT, hRp] at hm; simp at hm
  | some reps =>
  rw [hTT, hRp] at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨hd0, htear⟩, hcells⟩, hinit⟩, hext⟩, hdom⟩ := hm
  have hTT' : t.extractOver t.domain = some TT := hTT
  -- the representatives
  have hreps : TT.mapM List.head? = some reps := by
    unfold Test.reps at hRp; rw [hTT] at hRp; exact hRp
  obtain ⟨hrl, hrk⟩ := mapM_spec _ hreps
  have hlenTrs : trs.length = t.threads.length := hF.length_eq.trans (extractOver_length hD)
  have hlenTT : TT.length = t.threads.length := extractOver_length hTT'
  -- step 1: skeletons
  have hsh : trs.map (fun tr => tr.acts.map Act.ev) = reps.map (fun tr => tr.acts.map Act.ev) := by
    apply List.ext_getElem (by simp; omega)
    intro n h1 h2
    simp only [List.getElem_map]
    have hn : n < trs.length := by simpa using h1
    obtain ⟨hk, trsI, -, hex, hmem⟩ := choice_thread hD hF hn
    obtain ⟨S, hS, hS1⟩ := straight_spec hst hk
    have hnT : n < TT.length := by omega
    obtain ⟨trsT, hT1, hT2⟩ := extractOver_thread hTT' (List.getElem?_eq_getElem hk)
    have hTn : TT[n] = trsT := by
      rw [List.getElem?_eq_getElem hnT] at hT1; exact Option.some.inj hT1
    have hrep : reps[n]'(by simpa using h2) ∈ trsT := by
      have := hrk n hnT (by simpa using h2)
      rw [hTn] at this
      exact List.mem_of_mem_head? this
    rw [(trace_skel hex hS hS1 hmem).1, (trace_skel hT2 hS hS1 hrep).1]
  have hS := accUnits_shape hsh
  have hlenU : (accUnits trs).length = (accUnits reps).length := by
    simpa using congrArg List.length hS
  have hshape : ∀ n (h1 : n < (accUnits trs).length),
      shape (accUnits trs)[n].1 = shape ((accUnits reps)[n]'(hlenU ▸ h1)).1 := by
    intro n h1
    have := congrArg (·[n]?) hS
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem (hlenU ▸ h1), Option.map_some, Option.some.injEq] at this
    exact this
  have huntorn : ∀ u ∈ accUnits trs, tearAcc (accUnits trs) u.1 = false := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hu
    rw [tearAcc_shape, hS, hshape n hn, ← tearAcc_shape]
    have := List.all_eq_true.mp htear _ (List.getElem_mem (hlenU ▸ hn))
    simpa using this
  have hunits : units trs = accUnits trs := by
    unfold units
    exact flatMap_single _ _ fun u hu => by simp [huntorn u hu]
  have heq : x.evs = (accUnits trs).map Prod.fst := by rw [hevs, hunits]
  have hxn : x.n = (accUnits trs).length := by simp [Exec.n, heq]
  have hxev : ∀ (n : Nat) (h : n < x.n), x.ev ⟨n, h⟩ = ((accUnits trs)[n]'(hxn ▸ h)).1 := by
    intro n h
    simp only [Exec.ev]
    simp [heq]
  have hcellsX : cellsOk x.evs = true := by
    rw [heq, cellsOk_shape, List.map_map, hS, ← List.map_map, ← cellsOk_shape]
    exact hcells
  have hcount : (x.evs.filter Ev.isR).length =
      ((accUnits reps).filter fun u => u.1.isR).length := by
    rw [heq, countR', ← countR, hS, countR]
  -- consistency
  have hxl := hM x hMx
  have hn2 := noTwo_of_xl hxl
  have hta : Silmaril.X86.MemoryModel.Axiomatic.BRel.Acyclic x.thinAir := hxl.2.2.1
  have hwfF := wfFacts hwf
  let E : Nat → List Byte := fun r => ((units trs).map Prod.snd).getD r []
  have hE : ∀ n (h : n < (accUnits trs).length), E n = (accUnits trs)[n].2 := by
    intro n h
    simp [E, hunits, List.getD_eq_getElem?_getD, h]
  have hreads : ∀ r : Fin x.n, (x.ev r).isR = true → x.readBytes t.initB r.val = E r.val := by
    intro r hr
    exact hrok r.val r.isLt (by rw [evN_eq x r.val r.isLt]; exact hr)
  have hd0' : t.dom0 ≠ [] := by simpa using hd0
  -- step 2: the rank argument
  have hall := reads_in_level hwfF hn2 hcellsX hta t.initB E hreads
    (fun k bs => InDom (t.chain k) bs)
    (fun k bs h => inDom_mono (fun v hv => chain_mono t hv) h)
    (by
      intro r hr
      have hrn : r.val < (accUnits trs).length := hxn ▸ r.isLt
      have h1 := hshape r.val hrn
      rw [show r = ⟨r.val, r.isLt⟩ from rfl, hxev] at hr ⊢
      have hR' : ((accUnits reps)[r.val]'(hlenU ▸ hrn)).1.isR = true := by
        have : (shape (accUnits trs)[r.val].1).isR = true := hr
        rwa [h1] at this
      have := List.all_eq_true.mp hinit _ (List.getElem_mem (hlenU ▸ hrn))
      simp only [hR', Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
      have hb : (accUnits trs)[r.val].1.bytes = ((accUnits reps)[r.val]'(hlenU ▸ hrn)).1.bytes :=
        by have := congrArg Ev.bytes h1; exact this
      rw [hb]
      exact this)
    (le_of_eq hcount)
    (by
      intro k w hk hW H
      have hwn : w.val < (accUnits trs).length := hxn ▸ w.isLt
      rw [show w = ⟨w.val, w.isLt⟩ from rfl, hxev] at hW ⊢
      obtain ⟨i, tr, j, a, hi, hj, hwr, htid, hle, hlt, hdata⟩ := write_unit_info hwn hW
      have hu := List.getElem_mem hwn
      have hsc := singleCopy_of_untorn (huntorn _ hu) (isM_of_isW hW)
      have hacc := accUnits_acc hu
      have hsz : (accUnits trs)[w.val].1.size ≤ 8 := by
        simp only [Ev.singleCopy, Bool.and_eq_true, decide_eq_true_eq] at hsc
        omega
      have hdl := wf_data hwf (by rw [heq]; exact List.mem_map_of_mem hu) hW
      show InDom (t.chain (k + 1)) _
      rw [bytes_map_byte hdl, hdata]
      rw [hdata] at hdl
      -- the thread and the traces over `chain k`
      have hit : i < trs.length := (List.getElem?_eq_some_iff.mp hi).1
      have htri : trs[i] = tr := (List.getElem?_eq_some_iff.mp hi).2
      obtain ⟨hk', trsD, -, hexD, htrD⟩ := choice_thread hD hF hit
      rw [htri] at htrD
      have hks : (t.extractOver (t.chain k)).isSome = true :=
        List.all_eq_true.mp hext k (List.mem_range.mpr (by rw [← hcount]; omega))
      obtain ⟨Tk, hTk⟩ := Option.isSome_iff_exists.mp hks
      obtain ⟨trsk, hTki, hexk⟩ := extractOver_thread hTk (List.getElem?_eq_getElem hk')
      obtain ⟨S, hSk, hS1⟩ := straight_spec hst hk'
      have hsteps := (trace_skel hexD hSk hS1 htrD).2
      have hjl : j < tr.acts.length := (List.getElem?_eq_some_iff.mp hj).1
      obtain ⟨m, hm⟩ := take_flatten_boundary (tr.steps.map StepRec.acts)
        (fun l hl => by
          obtain ⟨st, hst', rfl⟩ := List.mem_map.mp hl
          exact hsteps st hst')
        (j + 1) (by rw [← List.flatMap_def]; exact hjl)
      rw [← List.map_take, ← List.flatMap_def, ← List.flatMap_def] at hm
      have hm' : (tr.steps.take m).flatMap StepRec.acts = tr.acts.take (j + 1) := hm
      have hpre : ∀ st ∈ tr.steps.take m, st.ReadsIn (t.chain k) := by
        intro st hst' a' ha' hr'
        have : a' ∈ tr.acts.take (j + 1) := hm' ▸ List.mem_flatMap.mpr ⟨st, hst', ha'⟩
        obtain ⟨j', hj'lt, hj'⟩ := mem_acts_take this
        obtain ⟨nr, hnr, hR, htid', hpos, hrd⟩ := read_unit_of_act hi hj' hr'
        have hnrx : nr < x.n := hxn ▸ hnr
        have hpo : x.po ⟨nr, hnrx⟩ ⟨w.val, w.isLt⟩ = true := by
          simp only [Exec.po, hxev, htid', htid, beq_self_eq_true, Bool.true_and,
            decide_eq_true_eq, hpos]
          rcases Nat.lt_or_ge j' j with hlt' | hge
          · have := posOff_lt hj' hlt'
            have := actLen_pos a'
            omega
          · have hjj : j' = j := by omega
            subst hjj
            rw [hj] at hj'
            cases Option.some.inj hj'
            exact hlt hr'
        have := H ⟨nr, hnrx⟩ (by rw [hxev]; exact hR) hpo
        rw [show E nr = a'.rd by rw [hE nr hnr, hrd]] at this
        exact this
      obtain ⟨tr₂, htr₂, he₂⟩ := Silmaril.X86.Litmus.extract_prefix
        (chain_ne_nil t hd0' k) hexk hexD htrD m hpre
      have ha₂ : tr₂.acts[j]? = some a := by
        have hsplit : tr₂.acts = (tr₂.steps.take m).flatMap StepRec.acts ++
            (tr₂.steps.drop m).flatMap StepRec.acts := by
          rw [← List.flatMap_append, List.take_append_drop]; rfl
        rw [hsplit, he₂, hm', List.getElem?_append_left (by simp; omega)]
        simpa using hj
      have hwv : a.wval ∈ XTrace.written tr₂ := by
        unfold XTrace.written
        refine List.mem_filterMap.mpr ⟨a, List.mem_of_getElem? ha₂, ?_⟩
        simp [hwr]
      have hflat : tr₂ ∈ Tk.flatten := List.mem_flatten.mpr ⟨trsk, List.mem_of_getElem? hTki, htr₂⟩
      refine ⟨a.wval, domStep_written hTk hflat hwv, ?_⟩
      exact Silmaril.X86.Ext.leBytes_leValue a.wr (by omega))
  -- step 3: restriction to `Test.domain`
  have hindom : ∀ v ∈ t.chain ((accUnits reps).filter fun u => u.1.isR).length, v ∈ t.domain :=
    fun v hv => memB_iff.mp (List.all_eq_true.mp hdom v hv)
  have hF' : List.Forall₂ (· ∈ ·) trs TT := by
    refine List.forall₂_iff_get.mpr ⟨by omega, fun i h1 h2 => ?_⟩
    obtain ⟨hk, trsI, -, hex, hmem⟩ := choice_thread hD hF h1
    obtain ⟨trsT, hT1, hT2⟩ := extractOver_thread hTT' (List.getElem?_eq_getElem hk)
    have hTn : TT[i] = trsT := by
      rw [List.getElem?_eq_getElem h2] at hT1; exact Option.some.inj hT1
    show trs[i] ∈ TT[i]
    rw [hTn]
    refine Silmaril.X86.Litmus.extract_restrict hT2 hex hmem fun st hst a' ha' hr' => ?_
    obtain ⟨j', hj'⟩ := mem_acts hst ha'
    obtain ⟨nr, hnr, hR, -, -, hrd⟩ :=
      read_unit_of_act (List.getElem?_eq_getElem h1) hj' hr'
    have := hall ⟨nr, hxn ▸ hnr⟩ (by rw [hxev]; exact hR)
    rw [show E nr = a'.rd by rw [hE nr hnr, hrd]] at this
    exact inDom_mono hindom this
  exact ⟨TT, rfl, trs, hF', x, hevs, hrmw, hwf, hrok, hMx, hf⟩

end Silmaril.Proofs.X86.MemoryModel.Litmus.Closure
