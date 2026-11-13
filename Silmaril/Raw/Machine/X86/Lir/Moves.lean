module

public import Silmaril.Machine.X86.Lir.Stack.Defs

/-!
# The move sequences of calls, prologues and returns

Each lemma runs one of the sequences of `Code.lean` on a frame with body stack
pointer `B` (`Fits`: the frame lies in the stack and its displacements fit in
32 bits) and states its effect:

* `run_saveAll`, `run_reloadAll`: the nine allocatable registers to and from the
  save area;
* `run_argLoads`: the argument registers receive the values of the argument
  locations (from the save area or the slots);
* `run_stage`, `run_paramMoves`: the incoming argument registers are staged in
  the save area and then written to the parameter locations, as `writeAll`
  does (a later location overrides an earlier equal one);
* `run_retLoads`, `run_resStores`: returned values into `rax rdx`, and from
  there into the result locations of the caller.

Reading all sources from the save area or from the result registers, which are
never destinations, makes the parallel moves safe for any aliasing between
sources and destinations.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine
open Relation

set_option linter.unusedSectionVars false

/-- The frame of `ns` slots at body stack pointer `B` lies in the stack and its
displacements fit in a signed 32-bit displacement. -/
structure Fits (S : Space) (B ns : Nat) : Prop where
  lo : S.stackLo ≤ B
  hi : B + frameSize ns ≤ S.stackHi
  disp : need ns < 2 ^ 31

namespace Fits

variable {S : Space} {B ns : Nat} (h : Fits S B ns)
include h

theorem slot {k : Nat} (hk : k < ns) :
    8 * k < 2 ^ 31 ∧ S.stackLo ≤ B + 8 * k ∧ B + 8 * k + 8 ≤ S.stackHi := by
  have := h.lo; have := h.hi; have := h.disp; have := Env.frameSize_ge ns
  unfold need at *
  omega

theorem save {k : Nat} (hk : k < 9) :
    saveDisp ns k < 2 ^ 31 ∧ S.stackLo ≤ B + saveDisp ns k ∧ B + saveDisp ns k + 8 ≤ S.stackHi := by
  have := h.lo; have := h.hi; have := h.disp; have := save_lt_frame ns hk
  unfold need at *
  omega

end Fits

theorem argRegN_lt {j : Nat} (h : j < 6) : argRegN j = argReg ⟨j, h⟩ := by
  simp [argRegN, h]

theorem resRegN_lt {j : Nat} (h : j < 2) : resRegN j = resReg ⟨j, h⟩ := by
  simp [resRegN, h]

theorem argRegN_ne_rsp (j : Nat) : argRegN j ≠ .rsp := by
  unfold argRegN; split
  · exact argReg_ne_rsp _
  · decide

theorem resRegN_scratch (j : Nat) : Scratch (resRegN j) := by
  unfold resRegN; split
  · exact resReg_scratch _
  · decide

theorem resRegN_ne_alloc (j : Nat) (k : Fin 9) : resRegN j ≠ allocReg k := by
  unfold resRegN; split
  · exact resReg_ne_alloc _ _
  · revert k; decide

theorem resRegN_ne_rsp (j : Nat) : resRegN j ≠ .rsp := by
  unfold resRegN; split
  · rename_i h; revert h; generalize j = j; intro h
    have : ∀ i : Fin 2, resReg i ≠ .rsp := by decide
    exact this _
  · decide

theorem resRegN_inj {i j : Nat} (hi : i < 2) (hj : j < 2) (h : resRegN i = resRegN j) : i = j := by
  rw [resRegN_lt hi, resRegN_lt hj] at h
  exact congrArg Fin.val (resReg_injective h)

theorem argRegN_inj {i j : Nat} (hi : i < 6) (hj : j < 6) (h : argRegN i = argRegN j) : i = j := by
  rw [argRegN_lt hi, argRegN_lt hj] at h
  exact congrArg Fin.val (argReg_injective h)

theorem readAll_cons {R : Type} [DecidableEq R] (fr : Lir.Frame R) (l : Lir.Loc R)
    (ls : List (Lir.Loc R)) {vals : List Word} (h : fr.readAll (l :: ls) = some vals) :
    ∃ v vs, vals = v :: vs ∧ fr.read l = some v ∧ fr.readAll ls = some vs := by
  simp [Lir.Frame.readAll, List.mapM_cons] at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨v, hv, vs, hvs, rfl⟩ := h
  exact ⟨v, vs, rfl, hv, hvs⟩

theorem readAll_length {R : Type} [DecidableEq R] (fr : Lir.Frame R) :
    ∀ (ls : List (Lir.Loc R)) {vals : List Word}, fr.readAll ls = some vals →
      vals.length = ls.length
  | [], vals, h => by simp [Lir.Frame.readAll] at h; subst h; rfl
  | l :: ls, vals, h => by
    obtain ⟨v, vs, rfl, -, hvs⟩ := readAll_cons fr l ls h
    simp [readAll_length fr ls hvs]

theorem saveAll_eq (ns : Nat) :
    saveAll ns = ((List.finRange 9).map fun k => (allocReg k, saveDisp ns k.val)).map stQ := by
  simp [saveAll, stQ, List.map_map, Function.comp_def]

theorem reloadAll_eq (ns : Nat) :
    reloadAll ns = ((List.finRange 9).map fun k => (allocReg k, saveDisp ns k.val)).map ldQ := by
  simp [reloadAll, ldQ, List.map_map, Function.comp_def]

theorem stageSeq_eq {P : Type} (ns : Nat) :
    ∀ (j : Nat) (locs : List (Lir.Loc P)), stageSeq ns j locs =
      ((List.range' j locs.length).map fun i => (argRegN i, saveDisp ns i)).map stQ
  | _, [] => rfl
  | j, _ :: ls => by
    simp only [stageSeq, List.length_cons, List.range'_succ, List.map_cons, stageSeq_eq ns (j + 1) ls]
    rfl

section

variable {S : Space} {n : Nat} (hv : S.Valid n)
include hv

/-! ## Save area -/

theorem run_saveAll {B ns : Nat} (hfit : Fits S B ns) (c : State) (m : Memory)
    (hrsp : c.read .rsp = BitVec.ofNat 64 B) (hreg : m.regions = S.regions n) :
    ∃ c' m', runSeq (saveAll ns) c m = some (c', m') ∧ (∀ r, c'.read r = c.read r) ∧
      m'.regions = m.regions ∧
      (∀ k : Fin 9, WordAt m' (B + saveDisp ns k) (c.read (allocReg k))) ∧
      (∀ x, x < B + 8 * ns ∨ B + 8 * ns + 72 ≤ x → m'.bytes.get? x = m.bytes.get? x) := by
  rw [saveAll_eq]
  obtain ⟨c', m', hr, hk, hreg', hw, hout⟩ := run_stQs hv
    ((List.finRange 9).map fun k => (allocReg k, saveDisp ns k.val)) c m hrsp hreg
    (by
      intro x hx
      simp only [List.mem_map, List.mem_finRange, true_and] at hx
      obtain ⟨k, rfl⟩ := hx
      exact hfit.save k.isLt)
    (by
      rw [List.pairwise_map]
      refine (List.nodup_finRange 9).imp ?_
      intro a b hab
      have : a.val ≠ b.val := fun e => hab (Fin.ext e)
      unfold saveDisp; omega)
  refine ⟨c', m', hr, hk, hreg', fun k => hw (allocReg k, saveDisp ns k.val) (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩),
    fun x hx => hout x ?_⟩
  intro y hy
  simp only [List.mem_map, List.mem_finRange, true_and] at hy
  obtain ⟨k, rfl⟩ := hy
  have := k.isLt
  unfold saveDisp; omega

theorem run_reloadAll {B ns : Nat} (hfit : Fits S B ns) (c : State) (m : Memory)
    (hrsp : c.read .rsp = BitVec.ofNat 64 B) (hreg : m.regions = S.regions n)
    (hback : ∀ k : Fin 9, ∃ w, WordAt m (B + saveDisp ns k) w) :
    ∃ c', runSeq (reloadAll ns) c m = some (c', m) ∧
      (∀ k : Fin 9, ∀ w, WordAt m (B + saveDisp ns k) w → c'.read (allocReg k) = w) ∧
      (∀ r, (∀ k, r ≠ allocReg k) → c'.read r = c.read r) := by
  rw [reloadAll_eq]
  obtain ⟨c', hr, hvals, hkeep⟩ := run_ldQs hv
    ((List.finRange 9).map fun k => (allocReg k, saveDisp ns k.val)) c m hrsp hreg
    (by
      intro x hx
      simp only [List.mem_map, List.mem_finRange, true_and] at hx
      obtain ⟨k, rfl⟩ := hx
      exact ⟨allocReg_ne_rsp k, (hfit.save k.isLt).1, (hfit.save k.isLt).2.1,
        (hfit.save k.isLt).2.2, hback k⟩)
    (by
      rw [List.pairwise_map]
      exact (List.nodup_finRange 9).imp fun hab e => hab (allocReg_injective e))
  refine ⟨c', hr, fun k w hw => hvals (allocReg k, saveDisp ns k.val) (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) w hw,
    fun r hr' => hkeep r ?_⟩
  intro x hx
  simp only [List.mem_map, List.mem_finRange, true_and] at hx
  obtain ⟨k, rfl⟩ := hx
  exact hr' k

/-! ## Arguments of a call -/

theorem run_argLoads {P : Type} [DecidableEq P] (A : Assign P) {B ns : Nat} (hfit : Fits S B ns)
    {fr : Lir.Frame P} {m : Memory} (hreg : m.regions = S.regions n)
    (hsaved : ∀ q v, fr.regs q = some v → WordAt m (B + saveDisp ns (A.idx q)) v)
    (hslots : Env.SlotsAt fr ns B m) :
    ∀ (args : List (Lir.Loc P)) (j : Nat) (vals : List Word) (c : State),
    fr.readAll args = some vals → c.read .rsp = BitVec.ofNat 64 B → j + args.length ≤ 6 →
    (∀ k ∈ locSlots args, k < ns) →
    ∃ c', runSeq (argLoads A ns j args) c m = some (c', m) ∧
      (∀ i (h : i < vals.length), c'.read (argRegN (j + i)) = vals[i]) ∧
      (∀ r, (∀ i < args.length, r ≠ argRegN (j + i)) → c'.read r = c.read r)
  | [], j, vals, c, hr, _, _, _ => by
    simp [Lir.Frame.readAll] at hr; subst hr
    exact ⟨c, rfl, by simp, fun _ _ => rfl⟩
  | l :: ls, j, vals, c, hr, hrsp, hlen, hsl => by
    obtain ⟨v, vs, rfl, hl, hls⟩ := readAll_cons fr l ls hr
    simp only [List.length_cons] at hlen
    obtain ⟨c₁, hr₁, hv₁, hk₁⟩ : ∃ c₁, runSeq [argLoad A ns j l] c m = some (c₁, m) ∧
        c₁.read (argRegN j) = v ∧ ∀ r, r ≠ argRegN j → c₁.read r = c.read r := by
      cases l with
      | reg p =>
        have hw := hsaved p v hl
        have ex := stack_load hv hreg hrsp (hfit.save (A.idx p).isLt).1
          (hfit.save (A.idx p).isLt).2.1 (hfit.save (A.idx p).isLt).2.2 (argRegN j) hw
        exact ⟨_, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl, by simp,
          fun r hr => by simp [State.read_write_other _ _ _ _ hr]⟩
      | slot k =>
        have hk : k < ns := hsl k (by simp [locSlots])
        have hw := hslots k v hk hl
        have ex := stack_load hv hreg hrsp (hfit.slot hk).1 (hfit.slot hk).2.1 (hfit.slot hk).2.2
          (argRegN j) hw
        exact ⟨_, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl, by simp,
          fun r hr => by simp [State.read_write_other _ _ _ _ hr]⟩
    obtain ⟨c', hr', hv', hk'⟩ := run_argLoads A hfit hreg hsaved hslots ls (j + 1) vs c₁ hls
      (by rw [hk₁ _ (argRegN_ne_rsp j).symm, hrsp]) (by omega)
      (fun k hk => hsl k (by simp only [locSlots, List.filterMap_cons] at hk ⊢; split <;> simp_all))
    refine ⟨c', ?_, ?_, ?_⟩
    · show runSeq (argLoad A ns j l :: argLoads A ns (j + 1) ls) c m = _
      rw [show argLoad A ns j l :: argLoads A ns (j + 1) ls = [argLoad A ns j l] ++
        argLoads A ns (j + 1) ls from rfl, runSeq_append_of hr₁, hr']
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hk' _ (fun i hi' h => by
          have := argRegN_inj (by omega) (by omega) h; omega), hv₁]
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [← hv' i (by simpa using hi)]
        congr 2
        omega
    · intro r hr
      rw [hk' r (fun i hi => by
          have := hr (i + 1) (by simp; omega)
          rwa [show j + (i + 1) = j + 1 + i by omega] at this),
        hk₁ r (by have := hr 0 (by simp); simpa using this)]

/-! ## Parameters of a callee -/

theorem run_stage {P : Type} {B ns : Nat} (hfit : Fits S B ns) (locs : List (Lir.Loc P))
    (hlen : locs.length ≤ 9) (c : State) (m : Memory) (hrsp : c.read .rsp = BitVec.ofNat 64 B)
    (hreg : m.regions = S.regions n) :
    ∃ c' m', runSeq (stageSeq ns 0 locs) c m = some (c', m') ∧ (∀ r, c'.read r = c.read r) ∧
      m'.regions = m.regions ∧
      (∀ i < locs.length, WordAt m' (B + saveDisp ns i) (c.read (argRegN i))) ∧
      (∀ x, x < B + 8 * ns ∨ B + 8 * ns + 72 ≤ x → m'.bytes.get? x = m.bytes.get? x) := by
  rw [stageSeq_eq]
  obtain ⟨c', m', hr, hk, hreg', hw, hout⟩ := run_stQs hv
    ((List.range' 0 locs.length).map fun i => (argRegN i, saveDisp ns i)) c m hrsp hreg
    (by
      intro x hx
      simp only [List.mem_map, List.mem_range'_1] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hfit.save (by omega))
    (by
      rw [List.pairwise_map]
      refine (List.nodup_range' (s := 0) (n := locs.length)).imp ?_
      intro a b hab
      unfold saveDisp; omega)
  refine ⟨c', m', hr, hk, hreg', fun i hi => hw (argRegN i, saveDisp ns i)
    (List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩), fun x hx => hout x ?_⟩
  intro y hy
  simp only [List.mem_map, List.mem_range'_1] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  unfold saveDisp; omega

theorem run_paramMoves {P : Type} [DecidableEq P] (A : Assign P) {B ns : Nat}
    (hfit : Fits S B ns) :
    ∀ (locs : List (Lir.Loc P)) (j : Nat) (vals : List Word) (fr fr' : Lir.Frame P) (c : State)
      (m : Memory),
    fr.writeAll locs vals = some fr' →
    c.read .rsp = BitVec.ofNat 64 B → m.regions = S.regions n →
    j + locs.length ≤ 9 →
    (∀ i (h : i < vals.length), WordAt m (B + saveDisp ns (j + i)) vals[i]) →
    (∀ k ∈ locSlots locs, k < ns) →
    (∀ q v, fr.regs q = some v → c.read (A.reg q) = v) → Env.SlotsAt fr ns B m →
    ∃ c' m', runSeq (paramMoves A ns j locs) c m = some (c', m') ∧
      (∀ q v, fr'.regs q = some v → c'.read (A.reg q) = v) ∧ Env.SlotsAt fr' ns B m' ∧
      (∀ r, ¬ Scratch r → (∀ k, r ≠ allocReg k) → c'.read r = c.read r) ∧
      m'.regions = m.regions ∧
      (∀ x, x < B ∨ B + 8 * ns ≤ x → m'.bytes.get? x = m.bytes.get? x)
  | [], j, [], fr, fr', c, m, hw, _, _, _, _, _, hregs, hslots => by
    simp only [Lir.Frame.writeAll, Option.some.injEq] at hw
    subst hw
    exact ⟨c, m, rfl, hregs, hslots, fun _ _ _ => rfl, rfl, fun _ _ => rfl⟩
  | [], _, _ :: _, _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [Lir.Frame.writeAll] at hw
  | _ :: _, _, [], _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [Lir.Frame.writeAll] at hw
  | l :: ls, j, v :: vs, fr, fr', c, m, hw, hrsp, hreg, hlen, hstaged, hsl, hregs, hslots => by
    simp only [Lir.Frame.writeAll] at hw
    simp only [List.length_cons] at hlen
    have hsv : WordAt m (B + saveDisp ns j) v := by
      have := hstaged 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    obtain ⟨c₁, m₁, hr₁, hregs₁, hslots₁, hk₁, hreg₁, hout₁⟩ : ∃ c₁ m₁,
        runSeq (paramMove A ns j l) c m = some (c₁, m₁) ∧
        (∀ q v', (fr.write l v).regs q = some v' → c₁.read (A.reg q) = v') ∧
        Env.SlotsAt (fr.write l v) ns B m₁ ∧
        (∀ r, ¬ Scratch r → (∀ k, r ≠ allocReg k) → c₁.read r = c.read r) ∧
        m₁.regions = m.regions ∧ (∀ x, x < B ∨ B + 8 * ns ≤ x → m₁.bytes.get? x = m.bytes.get? x) := by
      cases l with
      | reg p =>
        have ex := stack_load hv hreg hrsp (hfit.save (by omega)).1 (hfit.save (by omega)).2.1
          (hfit.save (by omega)).2.2 (A.reg p) hsv
        refine ⟨_, _, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl, ?_, hslots,
          fun r _ hr => ?_, rfl, fun _ _ => rfl⟩
        · intro q v' hq
          simp only [Lir.Frame.write, Lir.Frame.regs_set] at hq
          by_cases h : q = p
          · subst h; simp at hq; subst hq; simp
          · rw [ite_eq_right h] at hq
            simp [State.read_write_other _ _ _ _ (fun e => h (A.reg_injective e)), hregs q v' hq]
        · show (c.write (A.reg p) v).read r = c.read r
          exact State.read_write_other _ _ _ _ (show r ≠ A.reg p from hr (A.idx p))
      | slot k =>
        have hk : k < ns := hsl k (by simp [locSlots])
        have ex₁ := stack_load hv hreg hrsp (hfit.save (by omega)).1 (hfit.save (by omega)).2.1
          (hfit.save (by omega)).2.2 .r11 hsv
        obtain ⟨m₁, ex₂, hw₁, hwo⟩ := stack_store hv hreg (s := { c.write .r11 v with rip := (c.rip +
          BitVec.ofNat 64 (Ext.encode (.load .q .r11 (spMem (saveDisp ns j)))).length) })
          (by simpa using hrsp) (hfit.slot hk).1 (hfit.slot hk).2.1 (hfit.slot hk).2.2 .r11
        refine ⟨_, m₁, (runSeq_cons_of ex₁ (by intro h; cases h) rfl).trans
          ((runSeq_cons_of ex₂ (by intro h; cases h) rfl).trans rfl), ?_, ?_, fun r hr _ => ?_,
          hwo.1, fun x hx => hwo.2 x (by omega)⟩
        · intro q v' hq
          simp only [Lir.Frame.write, Lir.Frame.regs_setSlot] at hq
          simp [State.read_write_other _ _ _ _ (A.reg_ne_r11 q), hregs q v' hq]
        · intro k' v' hk' hv'
          simp only [Lir.Frame.write, Lir.Frame.slots_setSlot] at hv'
          by_cases h : k' = k
          · subst h; simp at hv'; subst hv'; simpa using hw₁
          · rw [ite_eq_right h] at hv'
            exact (hslots k' v' hk' hv').of_writesOnly hwo (by omega)
        · have := (not_scratch_iff r).mp hr
          simp [State.read_write_other _ _ _ _ this.2.2.2]
    have hrsp₁ : c₁.read .rsp = BitVec.ofNat 64 B := by
      rw [hk₁ _ (by decide) (fun k => (allocReg_ne_rsp k).symm), hrsp]
    obtain ⟨c', m', hr', hregs', hslots', hk', hreg', hout'⟩ := run_paramMoves A hfit ls (j + 1) vs
      (fr.write l v) fr' c₁ m₁ hw hrsp₁ (hreg₁.trans hreg) (by omega)
      (fun i hi => by
        have := hstaged (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show j + (i + 1) = j + 1 + i by omega] at this
        refine this.congr fun x hx => hout₁ _ ?_
        unfold saveDisp; right; omega)
      (fun k hk => hsl k (by
        cases l <;> simp only [locSlots, List.filterMap_cons] at hk ⊢ <;> simp_all))
      hregs₁ hslots₁
    refine ⟨c', m', ?_, hregs', hslots', fun r hr hra => by rw [hk' r hr hra, hk₁ r hr hra],
      hreg'.trans hreg₁, fun x hx => by rw [hout' x hx, hout₁ x hx]⟩
    show runSeq (paramMove A ns j l ++ paramMoves A ns (j + 1) ls) c m = _
    rw [runSeq_append_of hr₁, hr']

/-! ## Returned values -/

theorem run_retLoads {P : Type} [DecidableEq P] (A : Assign P) {B ns : Nat} (hfit : Fits S B ns)
    {fr : Lir.Frame P} {m : Memory} (hreg : m.regions = S.regions n)
    (hslots : Env.SlotsAt fr ns B m) :
    ∀ (locs : List (Lir.Loc P)) (j : Nat) (vals : List Word) (c : State),
    fr.readAll locs = some vals → c.read .rsp = BitVec.ofNat 64 B →
    (∀ q v, fr.regs q = some v → c.read (A.reg q) = v) → j + locs.length ≤ 2 →
    (∀ k ∈ locSlots locs, k < ns) →
    ∃ c', runSeq (retLoads A j locs) c m = some (c', m) ∧
      (∀ i (h : i < vals.length), c'.read (resRegN (j + i)) = vals[i]) ∧
      (∀ r, (∀ i < locs.length, r ≠ resRegN (j + i)) → c'.read r = c.read r)
  | [], j, vals, c, hr, _, _, _, _ => by
    simp [Lir.Frame.readAll] at hr; subst hr
    exact ⟨c, rfl, by simp, fun _ _ => rfl⟩
  | l :: ls, j, vals, c, hr, hrsp, hregs, hlen, hsl => by
    obtain ⟨v, vs, rfl, hl, hls⟩ := readAll_cons fr l ls hr
    simp only [List.length_cons] at hlen
    obtain ⟨c₁, hr₁, hv₁, hk₁⟩ : ∃ c₁, runSeq [retLoad A j l] c m = some (c₁, m) ∧
        c₁.read (resRegN j) = v ∧ ∀ r, r ≠ resRegN j → c₁.read r = c.read r := by
      cases l with
      | reg p =>
        have ex := Ext.exec_mov_reg c m .q (resRegN j) (A.reg p)
        exact ⟨_, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl,
          by simp [hregs p v hl], fun r hr => by simp [State.read_write_other _ _ _ _ hr]⟩
      | slot k =>
        have hk : k < ns := hsl k (by simp [locSlots])
        have hw := hslots k v hk hl
        have ex := stack_load hv hreg hrsp (hfit.slot hk).1 (hfit.slot hk).2.1 (hfit.slot hk).2.2
          (resRegN j) hw
        exact ⟨_, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl, by simp,
          fun r hr => by simp [State.read_write_other _ _ _ _ hr]⟩
    obtain ⟨c', hr', hv', hk'⟩ := run_retLoads A hfit hreg hslots ls (j + 1) vs c₁ hls
      (by rw [hk₁ _ (resRegN_ne_rsp j).symm, hrsp])
      (fun q v' hq => by rw [hk₁ (A.reg q) (Ne.symm (resRegN_ne_alloc j (A.idx q))), hregs q v' hq])
      (by omega)
      (fun k hk => hsl k (by simp only [locSlots, List.filterMap_cons] at hk ⊢; split <;> simp_all))
    refine ⟨c', ?_, ?_, ?_⟩
    · show runSeq ([retLoad A j l] ++ retLoads A (j + 1) ls) c m = _
      rw [runSeq_append_of hr₁, hr']
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hk' _ (fun i hi' h => by
          have := resRegN_inj (by omega) (by omega) h; omega), hv₁]
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [← hv' i (by simpa using hi)]
        congr 2
        omega
    · intro r hr
      rw [hk' r (fun i hi => by
          have := hr (i + 1) (by simp; omega)
          rwa [show j + (i + 1) = j + 1 + i by omega] at this),
        hk₁ r (by have := hr 0 (by simp); simpa using this)]

/-! ## Results of a call -/

theorem run_resStores {P : Type} [DecidableEq P] (A : Assign P) {B ns : Nat}
    (hfit : Fits S B ns) :
    ∀ (locs : List (Lir.Loc P)) (j : Nat) (vals : List Word) (fr fr' : Lir.Frame P) (c : State)
      (m : Memory),
    fr.writeAll locs vals = some fr' →
    c.read .rsp = BitVec.ofNat 64 B → m.regions = S.regions n →
    j + locs.length ≤ 2 →
    (∀ i (h : i < vals.length), c.read (resRegN (j + i)) = vals[i]) →
    (∀ k ∈ locSlots locs, k < ns) →
    (∀ q v, fr.regs q = some v → c.read (A.reg q) = v) → Env.SlotsAt fr ns B m →
    ∃ c' m', runSeq (resStores A j locs) c m = some (c', m') ∧
      (∀ q v, fr'.regs q = some v → c'.read (A.reg q) = v) ∧ Env.SlotsAt fr' ns B m' ∧
      (∀ r, (∀ k, r ≠ allocReg k) → c'.read r = c.read r) ∧
      m'.regions = m.regions ∧
      (∀ x, x < B ∨ B + 8 * ns ≤ x → m'.bytes.get? x = m.bytes.get? x)
  | [], j, [], fr, fr', c, m, hw, _, _, _, _, _, hregs, hslots => by
    simp only [Lir.Frame.writeAll, Option.some.injEq] at hw
    subst hw
    exact ⟨c, m, rfl, hregs, hslots, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  | [], _, _ :: _, _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [Lir.Frame.writeAll] at hw
  | _ :: _, _, [], _, _, _, _, hw, _, _, _, _, _, _, _ => by simp [Lir.Frame.writeAll] at hw
  | l :: ls, j, v :: vs, fr, fr', c, m, hw, hrsp, hreg, hlen, hsrc, hsl, hregs, hslots => by
    simp only [Lir.Frame.writeAll] at hw
    simp only [List.length_cons] at hlen
    have hsv : c.read (resRegN j) = v := by
      have := hsrc 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    obtain ⟨c₁, m₁, hr₁, hregs₁, hslots₁, hk₁, hreg₁, hout₁⟩ : ∃ c₁ m₁,
        runSeq [resStore A j l] c m = some (c₁, m₁) ∧
        (∀ q v', (fr.write l v).regs q = some v' → c₁.read (A.reg q) = v') ∧
        Env.SlotsAt (fr.write l v) ns B m₁ ∧
        (∀ r, (∀ k, r ≠ allocReg k) → c₁.read r = c.read r) ∧
        m₁.regions = m.regions ∧ (∀ x, x < B ∨ B + 8 * ns ≤ x → m₁.bytes.get? x = m.bytes.get? x) := by
      cases l with
      | reg p =>
        have ex := Ext.exec_mov_reg c m .q (A.reg p) (resRegN j)
        refine ⟨_, _, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl, ?_, hslots,
          fun r hr => ?_, rfl, fun _ _ => rfl⟩
        · intro q v' hq
          simp only [Lir.Frame.write, Lir.Frame.regs_set] at hq
          by_cases h : q = p
          · subst h; simp at hq; subst hq; simp [hsv]
          · rw [ite_eq_right h] at hq
            simp [State.read_write_other _ _ _ _ (fun e => h (A.reg_injective e)), hregs q v' hq]
        · simp only [read_rip, Ext.Sz.write,
            State.read_write_other _ _ _ _ (show r ≠ A.reg p from hr (A.idx p))]
      | slot k =>
        have hk : k < ns := hsl k (by simp [locSlots])
        obtain ⟨m₁, ex, hw₁, hwo⟩ := stack_store hv hreg hrsp (hfit.slot hk).1 (hfit.slot hk).2.1
          (hfit.slot hk).2.2 (resRegN j)
        refine ⟨_, m₁, (runSeq_cons_of ex (by intro h; cases h) rfl).trans rfl, ?_, ?_,
          fun r _ => rfl, hwo.1, fun x hx => hwo.2 x (by omega)⟩
        · intro q v' hq
          simp only [Lir.Frame.write, Lir.Frame.regs_setSlot] at hq
          simpa using hregs q v' hq
        · intro k' v' hk' hv'
          simp only [Lir.Frame.write, Lir.Frame.slots_setSlot] at hv'
          by_cases h : k' = k
          · subst h; simp at hv'; subst hv'; rw [← hsv]; exact hw₁
          · rw [ite_eq_right h] at hv'
            exact (hslots k' v' hk' hv').of_writesOnly hwo (by omega)
    have hrsp₁ : c₁.read .rsp = BitVec.ofNat 64 B := by
      rw [hk₁ _ (fun k => (allocReg_ne_rsp k).symm), hrsp]
    obtain ⟨c', m', hr', hregs', hslots', hk', hreg', hout'⟩ := run_resStores A hfit ls (j + 1) vs
      (fr.write l v) fr' c₁ m₁ hw hrsp₁ (hreg₁.trans hreg) (by omega)
      (fun i hi => by
        have := hsrc (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [hk₁ _ (fun k => resRegN_ne_alloc _ k), ← this]
        congr 2; omega)
      (fun k hk => hsl k (by
        cases l <;> simp only [locSlots, List.filterMap_cons] at hk ⊢ <;> simp_all))
      hregs₁ hslots₁
    refine ⟨c', m', ?_, hregs', hslots', fun r hra => by rw [hk' r hra, hk₁ r hra],
      hreg'.trans hreg₁, fun x hx => by rw [hout' x hx, hout₁ x hx]⟩
    show runSeq ([resStore A j l] ++ resStores A (j + 1) ls) c m = _
    rw [runSeq_append_of hr₁, hr']

end

end Silmaril.X86.Backend
