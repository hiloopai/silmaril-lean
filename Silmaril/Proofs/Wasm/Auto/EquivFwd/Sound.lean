module

public import Silmaril.Wasm.Auto.EquivFwd.Defs

/-!
# Store-to-load forwarding: soundness

* `load_storeM_disjoint`, `loadV_storeM_same`: the two memory facts (a store leaves the bytes of a
  disjoint range unchanged; an in-bounds full-width load of the stored range reads the stored
  value back);
* `evX_fwd`, `evM_fwdM`: forwarding preserves values under guards that hold;
* `firstFail_fwdG_none`, `firstFail_fwdG_some`: dropping repeated guards keeps the first failing
  guard, with its trap state rewritten under the guards that held before it;
* `xout_fwdS`: the weakest precondition left by a symbolic run is that of the forwarded state;
* **`segEquivX_of_checkXF`**: the equivalence check with forwarding is sound.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivFwd

open Silmaril.Wasm.Auto.EquivFwd
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (Env)
open Silmaril.Wasm.Auto.Equiv

/-! ## Memory facts -/

/-- A load from a region disjoint from a store reads the same bytes, whether the store succeeds or
not. -/
theorem load_getD_store_disjoint (B : ByteArray) {a n b m : Nat} (w : BitVec (8 * n))
    (hd : Silmaril.Wasm.Logic.Core.Region.Disjoint ⟨a, n⟩ ⟨b, m⟩) :
    Memory.load ((Memory.store B a w).getD B) b m = Memory.load B b m := by
  cases h : Memory.store B a w with
  | none => rfl
  | some B' => exact Silmaril.Wasm.Logic.Core.load_store_disjoint h hd

theorem load_storeM_disjoint (B : ByteArray) (t' : IntType) (p' : Option PackSize) (x : BitVec 32)
    (arg' arg : MemArg) (w : BitVec t'.width) (k : Nat)
    (hd : arg'.offset.val + accBytes t' p' ≤ arg.offset.val ∨ arg.offset.val + k ≤ arg'.offset.val) :
    Memory.load (storeM B t' p' x arg' w) (effAddr x.toNat arg) k =
      Memory.load B (effAddr x.toNat arg) k := by
  have hdisj : ∀ n, n = accBytes t' p' → Silmaril.Wasm.Logic.Core.Region.Disjoint
      ⟨effAddr x.toNat arg', n⟩ ⟨effAddr x.toNat arg, k⟩ := fun n hn => by
    simp only [Silmaril.Wasm.Logic.Core.Region.Disjoint, Silmaril.Wasm.Logic.Core.Region.stop, effAddr,
      hn]
    omega
  cases p' with
  | none => exact load_getD_store_disjoint B _ (hdisj _ rfl)
  | some sz => exact load_getD_store_disjoint B _ (hdisj _ rfl)

theorem loadV_storeM_disjoint (B : ByteArray) (t' : IntType) (p' : Option PackSize) (x : BitVec 32)
    (arg' arg : MemArg) (w : BitVec t'.width) (t : IntType) (p : Option (PackSize × Signedness))
    (hd : arg'.offset.val + accBytes t' p' ≤ arg.offset.val ∨
      arg.offset.val + accBytes t (p.map Prod.fst) ≤ arg'.offset.val) :
    loadV (storeM B t' p' x arg' w) t p x arg = loadV B t p x arg := by
  unfold loadV
  cases p with
  | none =>
    simp only
    rw [load_storeM_disjoint B t' p' x arg' arg w _ (by simpa [accBytes] using hd)]
  | some q =>
    obtain ⟨sz, sx⟩ := q
    simp only
    rw [load_storeM_disjoint B t' p' x arg' arg w _ (by simpa [accBytes] using hd)]

theorem loadV_storeM_same (B : ByteArray) (t : IntType) (x : BitVec 32) (arg' arg : MemArg)
    (w : BitVec t.width) (ho : arg'.offset = arg.offset)
    (hb : effAddr x.toNat arg + t.width / 8 ≤ B.size) :
    loadV (storeM B t none x arg' w) t none x arg = w := by
  have he : effAddr x.toNat arg' = effAddr x.toNat arg := by simp [effAddr, ho]
  unfold storeM loadV
  simp only [he]
  rw [Silmaril.Wasm.Logic.Core.store_eq _ hb]
  simp only [Option.getD_some]
  rw [Silmaril.Wasm.Logic.Core.load_store_same (Silmaril.Wasm.Logic.Core.store_eq _ hb)]
  cases t <;> simp [IntType.width] <;> exact BitVec.setWidth_eq _

/-! ## Forwarding preserves values -/

section Values

variable {ρ : Env} {B0 : ByteArray}

theorem evX_fwdLoad {K : List Guard} (hK : ∀ g ∈ K, g.holds ρ B0 = true) (t : IntType)
    (p : Option (PackSize × Signedness)) (a : XT) (arg : MemArg) :
    ∀ M : XT, evX ρ B0 t (fwdLoad K t p a arg M) = evX ρ B0 t (.load M t p a arg)
  | .mstore m t' p' a' arg' v => by
    have ha : canon .i32 a' = canon .i32 a → evX ρ B0 .i32 a' = evX ρ B0 .i32 a := fun h => by
      rw [← evX_canon .i32 a', h, evX_canon]
    unfold fwdLoad
    split
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, hca, ho, hg⟩ := hc
      have hhold := hK _ hg
      simp only [Guard.holds, evX_canon, decide_eq_true_eq] at hhold
      have hsz : (evM ρ B0 m).size = B0.size := size_evM ρ B0 m
      show evX ρ B0 t' v =
        (loadV (storeM (evM ρ B0 m) t' none (evX ρ B0 .i32 a') arg' (evX ρ B0 t' v)) t' none
          (evX ρ B0 .i32 a) arg).setWidth t'.width
      have h₁ := loadV_storeM_same (evM ρ B0 m) t' (evX ρ B0 .i32 a) arg' arg (evX ρ B0 t' v) ho
        (by rw [hsz]; exact hhold)
      rw [ha hca, h₁]
      simp
    · split
      · rename_i _ hc
        obtain ⟨hca, hd⟩ := hc
        rw [evX_fwdLoad hK t p a arg m]
        show (loadV (evM ρ B0 m) t p (evX ρ B0 .i32 a) arg).setWidth t.width =
          (loadV (storeM (evM ρ B0 m) t' p' (evX ρ B0 .i32 a') arg' (evX ρ B0 t' v)) t p
            (evX ρ B0 .i32 a) arg).setWidth t.width
        have h₁ := loadV_storeM_disjoint (evM ρ B0 m) t' p' (evX ρ B0 .i32 a) arg' arg
          (evX ρ B0 t' v) t p hd
        rw [ha hca, h₁]
      · rfl
  | .var _ | .const _ | .un .. | .bin .. | .rel .. | .wrap _ | .ext .. | .sel .. | .load ..
  | .minit => by unfold fwdLoad; rfl

theorem evX_fwd_and {K : List Guard} (hK : ∀ g ∈ K, g.holds ρ B0 = true) : ∀ e : XT,
    (∀ t, evX ρ B0 t (fwd K t e) = evX ρ B0 t e) ∧ evM ρ B0 (fwdM K e) = evM ρ B0 e
  | .var n => ⟨fun t => by simp [fwd], by simp [fwdM]⟩
  | .const c => ⟨fun t => by simp [fwd], by simp [fwdM]⟩
  | .un op a => by
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    exact ⟨fun t => by simp [fwd, evX, iha], by simp [fwdM]⟩
  | .bin op a b => by
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    obtain ⟨ihb, -⟩ := evX_fwd_and hK b
    exact ⟨fun t => by simp [fwd, evX, iha, ihb], by simp [fwdM]⟩
  | .rel t' op a b => by
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    obtain ⟨ihb, -⟩ := evX_fwd_and hK b
    exact ⟨fun t => by simp [fwd, evX, iha, ihb], by simp [fwdM]⟩
  | .wrap a => by
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    exact ⟨fun t => by simp [fwd, evX, iha], by simp [fwdM]⟩
  | .ext sx a => by
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    exact ⟨fun t => by cases sx <;> simp [fwd, evX, iha], by simp [fwdM]⟩
  | .sel c a b => by
    obtain ⟨ihc, -⟩ := evX_fwd_and hK c
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    obtain ⟨ihb, -⟩ := evX_fwd_and hK b
    exact ⟨fun t => by simp [fwd, evX, ihc, iha, ihb], by simp [fwdM]⟩
  | .load m t' p a arg => by
    obtain ⟨-, ihm⟩ := evX_fwd_and hK m
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    refine ⟨fun t => ?_, by simp [fwdM]⟩
    by_cases ht : t = t'
    · subst ht
      simp only [fwd, ↓reduceIte]
      rw [evX_fwdLoad hK]
      simp [evX, ihm, iha]
    · simp [fwd, ht, evX, ihm, iha]
  | .minit => ⟨fun t => by simp [fwd], by simp [fwdM]⟩
  | .mstore m t' p a arg v => by
    obtain ⟨-, ihm⟩ := evX_fwd_and hK m
    obtain ⟨iha, -⟩ := evX_fwd_and hK a
    obtain ⟨ihv, -⟩ := evX_fwd_and hK v
    exact ⟨fun t => by simp [fwd], by simp [fwdM, evM, ihm, iha, ihv]⟩

theorem map_denX_fwdSlots {K : List Guard} (hK : ∀ g ∈ K, g.holds ρ B0 = true)
    (l : List (IntType × XT)) : (fwdSlots K l).map (denX ρ B0) = l.map (denX ρ B0) := by
  simp only [fwdSlots, List.map_map]
  apply List.map_congr_left
  intro p _
  simp [denX, (evX_fwd_and hK p.2).1 p.1]

end Values

/-! ## States -/

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem frameOf_fwdT {c : XCtx H} {K : List Guard} (hK : ∀ g ∈ K, g.holds c.ρ c.mi.bytes = true)
    (T : XState) : c.frameOf (fwdT K T) = c.frameOf T := by
  have h₁ := map_denX_fwdSlots hK T.locals
  have h₂ := congrArg (List.map some) h₁
  simp only [List.map_map, Function.comp_def] at h₂
  simp only [XCtx.frameOf, fwdT]
  rw [h₂]

theorem storeOf_fwdT {c : XCtx H} {mem : Bool} {K : List Guard}
    (hK : ∀ g ∈ K, g.holds c.ρ c.mi.bytes = true) (T : XState) :
    c.storeOf mem (fwdT K T) = c.storeOf mem T := by
  simp only [XCtx.storeOf, fwdT, map_denX_fwdSlots hK, (evX_fwd_and hK T.mem).2]

theorem stackOf_fwdT {c : XCtx H} {K : List Guard} (hK : ∀ g ∈ K, g.holds c.ρ c.mi.bytes = true)
    (T : XState) : c.stackOf (fwdT K T) = c.stackOf T := by
  simp only [XCtx.stackOf, fwdT, map_denX_fwdSlots hK]

theorem firstFail_fwdG_none {ρ : Env} {B0 : ByteArray} :
    ∀ (seen : List Guard) {G : List (Guard × XState)}, firstFail ρ B0 G = none →
      firstFail ρ B0 (fwdG seen G) = none
  | _, [], _ => rfl
  | seen, (g, T) :: G, h => by
    simp only [firstFail] at h
    split at h
    · rename_i hg
      unfold fwdG
      split
      · exact firstFail_fwdG_none seen h
      · simp only [firstFail, hg, ↓reduceIte]
        exact firstFail_fwdG_none _ h
    · cases h

theorem firstFail_fwdG_some {ρ : Env} {B0 : ByteArray} :
    ∀ (seen : List Guard) {G : List (Guard × XState)} {T : XState},
      (∀ g ∈ seen, g.holds ρ B0 = true) → firstFail ρ B0 G = some T →
      ∃ K, (∀ g ∈ K, g.holds ρ B0 = true) ∧ firstFail ρ B0 (fwdG seen G) = some (fwdT K T)
  | _, [], _, _, h => by cases h
  | seen, (g, T₀) :: G, T, hs, h => by
    simp only [firstFail] at h
    split at h
    · rename_i hg
      unfold fwdG
      split
      · exact firstFail_fwdG_some seen hs h
      · have hs' : ∀ g' ∈ g.canon :: seen, g'.holds ρ B0 = true := by
          intro g' hg'
          rcases List.mem_cons.mp hg' with rfl | hg'
          · rw [holds_canon]; exact hg
          · exact hs g' hg'
        obtain ⟨K, hK, hf⟩ := firstFail_fwdG_some _ hs' h
        refine ⟨K, hK, ?_⟩
        simp only [firstFail, hg, ↓reduceIte]
        exact hf
    · rename_i hg
      cases h
      unfold fwdG
      have hn : g.canon ∉ seen := fun hm => hg (by rw [← holds_canon]; exact hs _ hm)
      simp only [hn, ↓reduceIte, firstFail, hg, Bool.false_eq_true]
      exact ⟨seen, hs, rfl⟩

/-- The canonical guards of a state whose guards all hold hold too. -/
theorem holds_canon_of_firstFail_none {c : XCtx H} {S : XState}
    (hf : firstFail c.ρ c.mi.bytes S.guards = none) :
    ∀ g ∈ S.guards.map (fun g => g.1.canon), g.holds c.ρ c.mi.bytes = true := by
  intro g hg
  obtain ⟨⟨g', T⟩, hm, rfl⟩ := List.mem_map.mp hg
  rw [holds_canon]
  exact (firstFail_none_iff.mp hf) _ hm

/-- **The weakest precondition left by a run is that of the forwarded state.** -/
theorem xout_fwdS {m : Corr} {c : XCtx H} {mem : Bool} (S : XState) (us : List Val)
    (rest : List Admin) (Q : Post H) :
    XOut m P host c mem S us rest Q ↔ XOut m P host c mem (fwdS S) us rest Q := by
  unfold XOut
  cases hf : firstFail c.ρ c.mi.bytes S.guards with
  | none =>
    have hK := holds_canon_of_firstFail_none hf
    have hf' : firstFail c.ρ c.mi.bytes (fwdS S).guards = none := firstFail_fwdG_none [] hf
    rw [hf']
    have e₁ : c.storeOf mem (fwdS S) = c.storeOf mem S := storeOf_fwdT hK S
    have e₂ : c.frameOf (fwdS S) = c.frameOf S := frameOf_fwdT hK S
    have e₃ : c.stackOf (fwdS S) = c.stackOf S := stackOf_fwdT hK S
    rw [e₁, e₂, e₃]
  | some T =>
    obtain ⟨K, hK, hf'⟩ := firstFail_fwdG_some (ρ := c.ρ) (B0 := c.mi.bytes) [] (by simp) hf
    have hf'' : firstFail c.ρ c.mi.bytes (fwdS S).guards = some (fwdT K T) := hf'
    rw [hf'']
    simp only
    rw [storeOf_fwdT hK T, frameOf_fwdT hK T]

/-- **The equivalence check with forwarding is sound.** -/
theorem segEquivX_of_checkXF {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkXF lt st gt mem a b = true) : SegEquivX lt st gt mem a b := by
  intro m P H host c us rest Q hc
  unfold checkXF at h
  split at h
  · rename_i A B ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hgk, hk⟩, hs⟩ := h
    rw [wp_init_iff hc ha, wp_init_iff hc hb, xout_fwdS A, xout_fwdS B]
    obtain ⟨hl, hgl, hm⟩ := key_eq_parts hk
    unfold XOut
    rcases firstFail_of_keys (ρ := c.ρ) (B0 := c.mi.bytes) hgk with ⟨hA, hB⟩ | ⟨T, T', hA, hB, hT⟩
    · simp only [hA, hB]
      rw [frameOf_eq_of_key c hl, storeOf_eq_of_key c mem hgl hm, stackOf_eq c hs]
    · simp only [hA, hB]
      obtain ⟨hl', hgl', hm'⟩ := key_eq_parts hT
      rw [frameOf_eq_of_key c hl', storeOf_eq_of_key c mem hgl' hm']
  · cases h

end Silmaril.Proofs.Wasm.Auto.EquivFwd
