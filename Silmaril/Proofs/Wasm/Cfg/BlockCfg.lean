module

public import Silmaril.Wasm.Cfg.BlockCfg.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Thms

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.BlockCfg

open Silmaril.Wasm Silmaril.Wasm.Cfg

theorem blockAt_snoc (p : List SeqStep) (m a i : Nat) :
    ∀ (segs : List Segment) (k : Nat), blockAt segs k (p ++ [(m, a)]) i =
      (blockAt segs k p m).bind fun s => s.term.bind fun t => (armOf t a).bind fun c =>
        (segment c)[i]? := by
  induction p with
  | nil =>
    intro segs k
    simp only [List.nil_append, blockAt]
    split <;> simp
  | cons st p ih =>
    obtain ⟨m', a'⟩ := st
    intro segs k
    simp only [List.cons_append, blockAt]
    split
    · simp only [Option.bind_eq_bind, ih, Option.bind_assoc]
    · simp

theorem lookup_snoc (body : Expr) (p : List SeqStep) (m a i : Nat) :
    lookup body ⟨p ++ [(m, a)], i⟩ =
      (lookup body ⟨p, m⟩).bind fun s => s.term.bind fun t => (armOf t a).bind fun c =>
        (segment c)[i]? :=
  blockAt_snoc p m a i _ 0

theorem segmentAux_eq_nil : ∀ (acc is : List Instr), segmentAux acc is = [] ↔ acc = [] ∧ is = []
  | acc, [] => by unfold segmentAux; split <;> simp_all
  | acc, i :: is => by
    unfold segmentAux
    split
    · simp
    · rw [segmentAux_eq_nil]; simp

theorem segment_head_isSome (c : List Instr) : ((segment c)[0]?).isSome = !c.isEmpty := by
  cases h : segment c with
  | nil => rw [segment, segmentAux_eq_nil] at h; simp [h.2]
  | cons s ss =>
    cases c with
    | nil => simp [segment, segmentAux] at h
    | cons => simp

theorem cont_snoc (body : Expr) (p : List SeqStep) (m a : Nat) :
    cont body (p ++ [(m, a)]) = entry body p (m + 1) := by
  simp [cont, contRev, entry]

/-- The block's successor list, paired with it. -/
def F (body : Expr) (x : BlockId × Segment) : BlockId × List Target := (x.1, succOf body x.1 x.2)

theorem entry_arm (body : Expr) (path : List SeqStep) (k a : Nat) (x : List Instr) (i : Instr)
    (c : List Instr) (hk : lookup body ⟨path, k⟩ = some ⟨x, some i⟩) (hc : armOf i a = some c) :
    entry body (path ++ [(k, a)]) 0 = armEntry (path ++ [(k, a)]) c (entry body path (k + 1)) := by
  have hl : lookup body ⟨path ++ [(k, a)], 0⟩ = (segment c)[0]? := by
    rw [lookup_snoc, hk]; simp [hc]
  have hs := segment_head_isSome c
  rw [← cont_snoc body path k a]
  unfold armEntry
  conv => lhs; unfold entry
  rw [hl, hs]
  cases c <;> simp

theorem labels_snoc (body : Expr) (p : List SeqStep) (m a : Nat) :
    labels body (p ++ [(m, a)]) =
      (if isLoopAt body p m then entry body (p ++ [(m, a)]) 0 else cont body (p ++ [(m, a)])) ::
        labels body p := by
  simp [labels, labelsRev, cont]

theorem succE_eq (body : Expr) (path : List SeqStep) (k : Nat) (x : List Instr) (i : Instr)
    (hk : lookup body ⟨path, k⟩ = some ⟨x, some i⟩) :
    succE path k (entry body path (k + 1)) (labels body path) i =
      succOf body ⟨path, k⟩ ⟨x, some i⟩ := by
  cases i
  case block t b => simp [succE, succOf, entry_arm body path k 0 x _ b hk rfl]
  case loop t b => simp [succE, succOf, entry_arm body path k 0 x _ b hk rfl]
  case tryTable t cs b => simp [succE, succOf, entry_arm body path k 0 x _ b hk rfl]
  case if_ ty t e =>
    simp [succE, succOf, entry_arm body path k 0 x _ t hk rfl, entry_arm body path k 1 x _ e hk rfl]
  all_goals simp [succE, succOf]

theorem sub (body : Expr) (path : List SeqStep) (k a : Nat) (x : List Instr) (i : Instr)
    (c : List Instr) (hk : lookup body ⟨path, k⟩ = some ⟨x, some i⟩) (hc : armOf i a = some c) :
    ∀ j, lookup body ⟨path ++ [(k, a)], 0 + j⟩ = (segmentAux [] c)[j]? := by
  intro j; rw [Nat.zero_add, lookup_snoc, hk]; simp [hc, segment]

theorem armOf_size {i : Instr} {a : Nat} {c : List Instr} (h : armOf i a = some c) :
    sizeOf c < sizeOf i := by
  cases i <;> rcases a with _ | _ | a <;> simp [armOf] at h <;> subst h <;> simp <;> omega

/-- The statement the builder meets on one sequence. -/
def Realizes (body : Expr) (path : List SeqStep) (k : Nat) (acc is : List Instr) : Prop :=
  walkE path k acc (cont body path) (labels body path) is = (walk path k acc is).map (F body)

theorem nestedE_of (body : Expr) (path : List SeqStep) (k : Nat) (x : List Instr) (i : Instr)
    (hk : lookup body ⟨path, k⟩ = some ⟨x, some i⟩)
    (IH : ∀ a c, armOf i a = some c →
      (∀ j, lookup body ⟨path ++ [(k, a)], 0 + j⟩ = (segmentAux [] c)[j]?) →
        Realizes body (path ++ [(k, a)]) 0 [] c) :
    nestedE path k (entry body path (k + 1)) (labels body path) i =
      (nested path k i).map (F body) := by
  cases i
  case block t b =>
    have := IH 0 b rfl (sub body path k 0 x _ b hk rfl)
    rw [Realizes, labels_snoc, cont_snoc] at this
    simpa [nestedE, nested, isLoopAt, hk] using this
  case tryTable t cs b =>
    have := IH 0 b rfl (sub body path k 0 x _ b hk rfl)
    rw [Realizes, labels_snoc, cont_snoc] at this
    simpa [nestedE, nested, isLoopAt, hk] using this
  case loop t b =>
    have := IH 0 b rfl (sub body path k 0 x _ b hk rfl)
    rw [Realizes, labels_snoc, cont_snoc] at this
    simp only [isLoopAt, hk, ite_true] at this
    rw [entry_arm body path k 0 x _ b hk rfl] at this
    simpa [nestedE, nested] using this
  case if_ ty t e =>
    have h0 := IH 0 t rfl (sub body path k 0 x _ t hk rfl)
    have h1 := IH 1 e rfl (sub body path k 1 x _ e hk rfl)
    rw [Realizes, labels_snoc, cont_snoc] at h0 h1
    simp only [isLoopAt, hk, Bool.false_eq_true, ite_false] at h0 h1
    simp [nestedE, nested, h0, h1]
  all_goals simp [nestedE, nested]

theorem walkE_eq (body : Expr) (path : List SeqStep) (k : Nat) (acc : List Instr)
    (is : List Instr) (hL : ∀ j, lookup body ⟨path, k + j⟩ = (segmentAux acc is)[j]?) :
    Realizes body path k acc is := by
  unfold Realizes
  match is with
  | [] =>
    have h1 := hL 1
    have hn : entry body path (k + 1) = cont body path := by
      unfold entry; rw [h1]; unfold segmentAux; split <;> simp
    unfold walkE walk
    split <;> simp [F, succOf, hn]
  | i :: is =>
    unfold walkE walk
    by_cases hi : isTerminator i = true
    · have hseg : segmentAux acc (i :: is) = ⟨acc.reverse, some i⟩ :: segmentAux [] is := by
        rw [segmentAux]; simp [hi]
      have hk : lookup body ⟨path, k⟩ = some ⟨acc.reverse, some i⟩ := by
        simpa [hseg] using hL 0
      have hnext : (if is.isEmpty then cont body path else .block ⟨path, k + 1⟩) =
          entry body path (k + 1) := by
        have h1 := hL 1
        rw [hseg] at h1
        have hs := segment_head_isSome is
        unfold entry
        simp only [h1, List.getElem?_cons_succ, show segmentAux [] is = segment is from rfl, hs]
        cases is <;> simp
      have hn := nestedE_of body path k _ i hk (fun a c hc hL' =>
        have := armOf_size hc
        walkE_eq body (path ++ [(k, a)]) 0 [] c hL')
      have hw := walkE_eq body path (k + 1) [] is (fun j => by
        rw [show k + 1 + j = k + (j + 1) by omega, hL, hseg]; simp)
      rw [Realizes] at hw
      simp only [hi, ite_true]
      rw [hnext, succE_eq body path k _ i hk, hn, hw]
      simp [F]
    · have hseg : segmentAux acc (i :: is) = segmentAux (i :: acc) is := by
        rw [segmentAux]; simp [hi]
      have := walkE_eq body path k (i :: acc) is (fun j => by rw [hL, hseg])
      rw [Realizes] at this
      simpa [hi] using this
termination_by sizeOf is
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem blockCfg_eq (body : Expr) : blockCfg body = (blocks body).map (F body) := by
  have := walkE_eq body [] 0 [] body (fun j => by simp [lookup, blockAt, segment])
  simpa [Realizes, cont, contRev, labels, labelsRev, blocks, blockCfg] using this

end Silmaril.Wasm.Cfg.Proofs.BlockCfg
