module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XEngine

/-!
# Inverting `Step` at a `FlatK` redex, from the checks

At a code `l` that is `k` values followed by one injection named `t` (`FlatK k t l`):

* `blk_proper`: a row passing `chkProper k t` refutes every proper infix of `l`;
* `blk_full`: a row passing `chkFull k t` refutes `l` itself;
* `inert_of_flat`: so on `chkProper` for the three tables every proper infix is `Inert`;
* `spure_of_sstep_flat`, `sread_of_sstep_flat`: **on `pureOk k t` (`readOk k t`), at every
  evaluator with the wasm-3.0 tables, every `Step` fact from `z; l` is `Step/pure`
  (`Step/read`) at the whole of `l`.**
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)

variable {env : Env}

/-! ## Constructors of a `FlatK` code and its infixes -/

/-- `outside`, unfolded. -/
theorem outside_spec {S : List MixopS} {row : List MixopS × Option Nat}
    (h : outside S row = true) : ∃ op ∈ row.1, op ∉ S := by
  simp only [outside, List.any_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact h

/-- `TagsIn` passes to sublists. -/
theorem tagsIn_of_subset {S : List MixopS} {l M : List Value} (h : TagsIn S l)
    (hs : ∀ x ∈ M, x ∈ l) : TagsIn S M :=
  fun x hx => h x (hs x hx)

/-- The constructors of a `FlatK k t` code are `t` and value constructors. -/
theorem FlatK.tagsIn {k : Nat} {t : MixopS} {l : List Value} (hl : FlatK k t l) :
    TagsIn (t :: valTags) l := by
  obtain ⟨vs, x, rfl, -, hv, hx⟩ := hl
  intro y hy op w' hye
  rcases List.mem_append.1 hy with hy | hy
  · exact List.mem_cons_of_mem _ (hv y hy op w' hye)
  · rw [List.mem_singleton.1 (hx y hy op w' hye)]
    exact List.mem_cons_self

/-- A `FlatK k t` code has length `k + 1`. -/
theorem FlatK.length {k : Nat} {t : MixopS} {l : List Value} (hl : FlatK k t l) :
    l.length = k + 1 := by
  obtain ⟨vs, x, rfl, hk, -⟩ := hl
  simp [hk]

/-- **Proper infixes of a `FlatK k t` code**: at most `k` long, and made of values when they
leave out the last instruction. -/
theorem FlatK.infix {k : Nat} {t : MixopS} {l A M C : List Value} (hl : FlatK k t l)
    (h : A ++ M ++ C = l) (hne : A ≠ [] ∨ C ≠ []) :
    M.length ≤ k ∧ (C ≠ [] → TagsIn valTags M) := by
  have hlen := hl.length
  refine ⟨?_, fun hC => ?_⟩
  · have e : A.length + M.length + C.length = k + 1 := by
      rw [← hlen, ← h]; simp only [List.length_append]
    rcases hne with hA | hC
    · have := List.length_pos_iff.2 hA; omega
    · have := List.length_pos_iff.2 hC; omega
  · obtain ⟨vs, x, rfl, -, hv, -⟩ := hl
    obtain ⟨C', y, rfl⟩ := (List.eq_nil_or_concat C).resolve_left hC
    have e : (A ++ M ++ C') ++ [y] = vs ++ [x] := by rw [← h]; simp
    have e' : A ++ M ++ C' = vs := (List.append_inj' e rfl).1
    exact tagsIn_of_subset hv fun x hx => by rw [← e']; simp [hx]

/-- **A row passing `chkProper` refutes every proper infix.** -/
theorem blk_proper {k : Nat} {t : MixopS} {T : List (List MixopS × Option Nat)}
    {l A M C : List Value} (hl : FlatK k t l) (h : A ++ M ++ C = l) (hne : A ≠ [] ∨ C ≠ [])
    (hc : chkProper k t T = true) :
    ∀ row ∈ T, ∃ S, TagsIn S M ∧ Blk S M.length row := by
  intro row hrow
  have hr := List.all_eq_true.1 hc row hrow
  have hM : TagsIn (t :: valTags) M := tagsIn_of_subset hl.tagsIn fun x hx => by
    rw [← h]; simp [hx]
  obtain ⟨hlen, hval⟩ := hl.infix h hne
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hr
  rcases hr with ho | ⟨ho, hk⟩
  · exact ⟨_, hM, .inl (outside_spec ho)⟩
  · by_cases hC : C = []
    · obtain ⟨m, hm, hkm⟩ : ∃ m, row.2 = some m ∧ k < m := by
        cases e : row.2 with
        | none => rw [e] at hk; simp at hk
        | some m => rw [e] at hk; exact ⟨m, rfl, by simpa using hk⟩
      exact ⟨_, hM, .inr ⟨m, hm, by omega⟩⟩
    · exact ⟨_, hval hC, .inl (outside_spec ho)⟩

/-- **A row passing `chkFull` refutes the whole code.** -/
theorem blk_full {k : Nat} {t : MixopS} {T : List (List MixopS × Option Nat)} {l : List Value}
    (hl : FlatK k t l) (hc : chkFull k t T = true) :
    ∀ row ∈ T, Blk (t :: valTags) l.length row := by
  intro row hrow
  have hr := List.all_eq_true.1 hc row hrow
  simp only [Bool.or_eq_true] at hr
  rcases hr with ho | hk
  · exact .inl (outside_spec ho)
  · cases e : row.2 with
    | none => rw [e] at hk; simp at hk
    | some m =>
      rw [e] at hk
      refine .inr ⟨m, e, ?_⟩
      rw [hl.length]
      simpa using hk

/-! ## Inertness and the inversion -/

/-- **Proper infixes of a checked `FlatK` code are inert.** -/
theorem inert_of_flat (Tb : Tables env) {k : Nat} {t : MixopS} {l A M C : List Value}
    (hl : FlatK k t l) (hp : chkProper k t pureInfoT = true)
    (hr : chkProper k t readInfoT = true) (hs : chkProper k t stepRestT = true)
    (h : A ++ M ++ C = l) (hne : A ≠ [] ∨ C ≠ []) : Inert env M := by
  refine ⟨fun i v => ?_, fun i z v => ?_, fun i z v hi => ?_⟩
  · refine not_fires_of_blk Tb.pureT (Nat.zero_le i) fun row hrow => ?_
    obtain ⟨S, hS, hb⟩ := blk_proper hl h hne hp row hrow
    exact ⟨S, M.length, .inl ⟨M, rfl, hS, rfl⟩, hb⟩
  · refine not_fires_of_blk Tb.readT (Nat.zero_le i) fun row hrow => ?_
    obtain ⟨S, hS, hb⟩ := blk_proper hl h hne hr row hrow
    exact ⟨S, M.length, .inr ⟨z, M, rfl, hS, rfl⟩, hb⟩
  · refine not_fires_of_blk Tb.stepT hi fun row hrow => ?_
    obtain ⟨S, hS, hb⟩ := blk_proper hl h hne hs row hrow
    exact ⟨S, M.length, .inr ⟨z, M, rfl, hS, rfl⟩, hb⟩

/-- **Inversion at a checked `Step_pure` redex**: at every evaluator with the wasm-3.0 tables,
a `Step` fact from `z; l`, for `l` of shape `FlatK k t` with `pureOk k t`, is `Step/pure` at the
whole of `l`. -/
theorem spure_of_sstep_flat (Tb : Tables env) {k : Nat} {t : MixopS} {l : List Value}
    (hl : FlatK k t l) (hok : pureOk k t = true) {z w : Value} (hs : SStep env (cfgV z l) w) :
    ∃ js, w = cfgV z js ∧ SPure env l js := by
  simp only [pureOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hp, hr⟩, hst⟩, hfr⟩, hfs⟩ := hok
  refine spure_of_sstep Tb (fun A M C h hne => inert_of_flat Tb hl hp hr hst h hne)
    (fun i z' v => not_fires_of_blk Tb.readT (Nat.zero_le i) fun row hrow =>
      ⟨_, _, .inr ⟨z', l, rfl, hl.tagsIn, rfl⟩, blk_full hl hfr row hrow⟩)
    (fun i z' v hi => not_fires_of_blk Tb.stepT hi fun row hrow =>
      ⟨_, _, .inr ⟨z', l, rfl, hl.tagsIn, rfl⟩, blk_full hl hfs row hrow⟩) hs

/-- **Inversion at a checked `Step_read` redex**: at every evaluator with the wasm-3.0 tables,
a `Step` fact from `z; l`, for `l` of shape `FlatK k t` with `readOk k t`, is `Step/read` at the
whole of `l`. -/
theorem sread_of_sstep_flat (Tb : Tables env) {k : Nat} {t : MixopS} {l : List Value}
    (hl : FlatK k t l) (hok : readOk k t = true) {z w : Value} (hs : SStep env (cfgV z l) w) :
    ∃ js, w = cfgV z js ∧ SRead env (cfgV z l) js := by
  simp only [readOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hp, hr⟩, hst⟩, hfp⟩, hfs⟩ := hok
  refine sread_of_sstep Tb (fun A M C h hne => inert_of_flat Tb hl hp hr hst h hne)
    (fun i v => not_fires_of_blk Tb.pureT (Nat.zero_le i) fun row hrow =>
      ⟨_, _, .inl ⟨l, rfl, hl.tagsIn, rfl⟩, blk_full hl hfp row hrow⟩)
    (fun i z' v hi => not_fires_of_blk Tb.stepT hi fun row hrow =>
      ⟨_, _, .inr ⟨z', l, rfl, hl.tagsIn, rfl⟩, blk_full hl hfs row hrow⟩) hs

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
