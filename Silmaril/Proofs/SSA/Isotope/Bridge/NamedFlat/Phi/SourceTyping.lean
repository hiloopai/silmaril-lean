module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceTyping.Defs

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body Term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Row)

universe u v

/-! ## Types of the values on an edge -/

section Values

variable {Base V K : Type u}

/-- A lifted value has the type of the value. -/
theorem valueType_liftVal_proof (types : V → Ty Base) : (value : Val V) →
    valueType (lifted types) (Phi.liftVal value) = valueType types value
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    simp only [Phi.liftVal, valueType, valueType_liftVal_proof types a,
      valueType_liftVal_proof types b]

/-- A lifted value reads source registers only. -/
theorem liftVal_fv_proof : (value : Val V) → ∀ z ∈ (Phi.liftVal value).fvList, ∃ r, z = some r
  | .var x, z, member => ⟨x, by simpa [Phi.liftVal, Val.fvList] using member⟩
  | .unit, z, member => by simp [Phi.liftVal, Val.fvList] at member
  | .pair a b, z, member => by
    simp only [Phi.liftVal, Val.fvList, List.mem_append] at member
    rcases member with inLeft | inRight
    · exact liftVal_fv_proof a z inLeft
    · exact liftVal_fv_proof b z inRight

/-- The packed φ operands read source registers only. -/
theorem pack_fv_proof : (arguments : List (Val V)) →
    ∀ z ∈ (Phi.pack arguments).fvList, ∃ r, z = some r
  | [], z, member => by simp [Phi.pack, Val.fvList] at member
  | first :: rest, z, member => by
    simp only [Phi.pack, Val.fvList, List.mem_append] at member
    rcases member with inFirst | inRest
    · exact liftVal_fv_proof first z inFirst
    · exact pack_fv_proof rest z inRest

/-- A value read at current versions has the type of the value, when the
current version of each register it reads has the type of the register. -/
theorem valueType_rn_proof {W : Type u} (types : W → Ty Base) (versioned : W × Nat → Ty Base)
    (cur : W → Nat) : (value : Val W) →
    (∀ z ∈ value.fvList, versioned (z, cur z) = types z) →
    valueType versioned (Version.rn cur value) = valueType types value
  | .var x, current => current x (by simp [Val.fvList])
  | .unit, _ => rfl
  | .pair a b, current => by
    simp only [Version.rn, valueType]
    rw [valueType_rn_proof types versioned cur a fun z member =>
        current z (by simp [Val.fvList, member]),
      valueType_rn_proof types versioned cur b fun z member =>
        current z (by simp [Val.fvList, member])]

/-- The record of a list of registers, read at current versions, has the
record type of the list. -/
theorem valueType_record_proof {W : Type u} (types : W → Ty Base) (versioned : W × Nat → Ty Base)
    (cur : W → Nat) : (registers : List W) →
    (∀ y ∈ registers, versioned (y, cur y) = types y) →
    valueType versioned (Version.pack cur registers) = recordType types registers
  | [], _ => rfl
  | y :: rest, current => by
    simp only [Version.pack, valueType, recordType]
    rw [current y (by simp), valueType_record_proof types versioned cur rest fun z member =>
      current z (by simp [member])]

variable [DecidableEq K]

/-- The packed φ operands of an edge have the type of the rows, when each
operand has the type of its destination. -/
theorem valueType_args_proof (types : V → Ty Base) (pred : Option K) : (rows : List (Row V K)) →
    (∀ row ∈ rows, valueType types (row.operand pred) = types row.dst) →
    valueType (lifted types) (Phi.pack (Phi.arguments pred rows)) = argsType types rows
  | [], _ => rfl
  | row :: rest, operands => by
    have tail := valueType_args_proof types pred rest fun r member => operands r (by simp [member])
    simp only [Phi.arguments, List.map_cons, Phi.pack, valueType, argsType,
      valueType_liftVal_proof] at tail ⊢
    rw [operands row (by simp), tail]

end Values

/-! ## The record of an edge of the lowering -/

section Records

variable {V K : Type u} {F : Type v} [DecidableEq V] [DecidableEq K]

/-- The record that the versioning carries to a block of the lowering is
the layout of the lowered block. -/
theorem destinations_some_proof (graph : Graph V K F) (key : K) :
    Versioning.destinations (Phi.OrderedExits.lower graph) (some key) =
      (graph.blocks.lookup key).map fun block =>
        Versioning.slots (Phi.OrderedExits.lower graph)
          (Phi.OrderedExits.lowerBlock graph key block) := by
  have inner : ∀ blocks : List (K × Block V K F),
      @List.lookup _ _ instBEqOfDecidableEq (some key)
          (blocks.map fun item => (some item.1, Phi.OrderedExits.lowerBlock graph item.1 item.2)) =
        (blocks.lookup key).map (Phi.OrderedExits.lowerBlock graph key) := by
    intro blocks
    induction blocks with
    | nil => rfl
    | cons item rest ih =>
      rcases item with ⟨k, b⟩
      simp only [List.map_cons, List.lookup_cons]
      by_cases same : key = k
      · subst same
        simp
      · have lowered : (@BEq.beq (Option K) instBEqOfDecidableEq (some key) (some k)) = false := by
          show decide (some key = some k) = false
          simpa using same
        have source : (key == k) = false := by
          rw [beq_eq_false_iff_ne]
          exact same
        simp only [lowered, source, ih]
  unfold Versioning.destinations Versioning.destinationsWith
  rw [show (Phi.OrderedExits.lower graph).blocks = graph.blocks.map fun item =>
    (some item.1, Phi.OrderedExits.lowerBlock graph item.1 item.2) from rfl, inner]
  cases graph.blocks.lookup key <;> rfl

/-- The versioning carries no record to the return label. -/
theorem destinations_none_proof (graph : Graph V K F) :
    Versioning.destinations (Phi.OrderedExits.lower graph) none = none := by
  have inner : ∀ blocks : List (K × Block V K F),
      @List.lookup _ _ instBEqOfDecidableEq none
          (blocks.map fun item => (some item.1, Phi.OrderedExits.lowerBlock graph item.1 item.2)) =
        none := by
    intro blocks
    induction blocks with
    | nil => rfl
    | cons item rest ih =>
      have lowered : (@BEq.beq (Option K) instBEqOfDecidableEq none (some item.1)) = false := by
        show decide (none = some item.1) = false
        simp
      simp only [List.map_cons, List.lookup_cons, lowered, ih]
  unfold Versioning.destinations Versioning.destinationsWith
  rw [show (Phi.OrderedExits.lower graph).blocks = graph.blocks.map fun item =>
    (some item.1, Phi.OrderedExits.lowerBlock graph item.1 item.2) from rfl, inner]
  rfl

/-- The record of a lowered block holds source registers only: the packet
register is the parameter of the block and is left out. -/
theorem slots_some_proof (graph : Graph V K F) (key : K) (block : Block V K F) :
    ∀ y ∈ Versioning.slots (Phi.OrderedExits.lower graph)
      (Phi.OrderedExits.lowerBlock graph key block), ∃ r, y = some r := by
  intro y member
  have other : y ≠ none := of_decide_eq_true (List.mem_filter.mp member).2
  cases y with
  | none => exact absurd rfl other
  | some r => exact ⟨r, rfl⟩

end Records

/-! ## The typed edge -/

section Edge

variable {Base V K : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)] [DecidableEq V]
  [DecidableEq K]

/-- A certified jump to a block, lowered and versioned, carries a packet
of the computed packet type of the block, when the current version of
every source register has its declared type. -/
theorem edge_packet_proof (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (pred : Option K) (key : K) (block : Block V K F)
    (value : Val V) (found : graph.blocks.lookup key = some block)
    (typed : termTyped graph types exitType pred (.br (some key) value) = true)
    (live : List (Option V)) (cur : Option V → Nat) (depth : Nat)
    (versioned : Option V × Nat → Ty Base)
    (current : ∀ register, versioned (some register, cur (some register)) = types register) :
    ∃ payload, Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur
        depth (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred)
          (.br (some key) value : Term V (Option K) F)).toRegion = .br (some key) payload ∧
      valueType versioned payload = packetType graph types key block := by
  have looked : Phi.OrderedExits.lookup graph (some key) = some block := found
  simp only [termTyped, looked, List.all_eq_true, decide_eq_true_eq] at typed
  have records := destinations_some_proof graph key
  rw [found] at records
  refine ⟨.pair (Version.rn cur (Phi.pack (Phi.arguments pred block.rows)))
    (Version.pack cur (Versioning.slots (Phi.OrderedExits.lower graph)
      (Phi.OrderedExits.lowerBlock graph key block))), ?_, ?_⟩
  · simp only [Phi.liftTerm, Term.toRegion, Version.version, Phi.OrderedExits.branchValue, looked,
      Option.elim, records, Option.map_some]
  · simp only [valueType, packetType]
    rw [valueType_rn_proof (lifted types) versioned cur _ (fun z member => by
        obtain ⟨r, rfl⟩ := pack_fv_proof _ z member
        exact current r),
      valueType_args_proof types pred block.rows typed,
      valueType_record_proof (lifted types) versioned cur _ (fun y member => by
        obtain ⟨r, rfl⟩ := slots_some_proof graph key block y member
        exact current r)]

/-- A certified jump to a label that is not a block, lowered and
versioned, carries a payload of the declared type of the label, and no
record. -/
theorem exit_payload_proof (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (pred target : Option K) (value : Val V)
    (absent : Phi.OrderedExits.lookup graph target = none)
    (typed : termTyped graph types exitType pred (.br target value) = true)
    (live : List (Option V)) (cur : Option V → Nat) (depth : Nat)
    (versioned : Option V × Nat → Ty Base)
    (current : ∀ register, versioned (some register, cur (some register)) = types register) :
    ∃ payload, Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur
        depth (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred)
          (.br target value : Term V (Option K) F)).toRegion = .br target payload ∧
      valueType versioned payload = exitType target := by
  simp only [termTyped, absent, decide_eq_true_eq] at typed
  have records : Versioning.destinations (Phi.OrderedExits.lower graph) target = none := by
    cases target with
    | none => exact destinations_none_proof graph
    | some key =>
      have missing : graph.blocks.lookup key = none := absent
      rw [destinations_some_proof, missing]
      rfl
  refine ⟨Version.rn cur (Phi.liftVal value), ?_, ?_⟩
  · simp only [Phi.liftTerm, Term.toRegion, Version.version, Phi.OrderedExits.branchValue, absent,
      Option.elim, records]
  · rw [valueType_rn_proof (lifted types) versioned cur _ (fun z member => by
        obtain ⟨r, rfl⟩ := liftVal_fv_proof _ z member
        exact current r), valueType_liftVal_proof, typed]

end Edge

/-! ## The versioned body

A certified body, lowered and versioned, is typed under any typing of the
versioned names in which the current version of every source register
has its declared type and every later version has it too. -/

section VersionedBody

variable {Base V K : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)] [DecidableEq V]
  [DecidableEq K]

omit [DecidableEq V] in
/-- A lifted operand, read at current versions, has the type of the
operand. -/
theorem opType_version_proof (types : V → Ty Base) (versioned : Option V × Nat → Ty Base)
    (cur : Option V → Nat)
    (current : ∀ register, versioned (some register, cur (some register)) = types register)
    (operand : Op V F) :
    opType versioned (Version.rnOp cur (Phi.liftOp operand)) = opType types operand := by
  have value : ∀ a : Val V,
      valueType versioned (Version.rn cur (Phi.liftVal a)) = valueType types a := fun a => by
    rw [valueType_rn_proof (lifted types) versioned cur _ (fun z member => by
      obtain ⟨r, rfl⟩ := liftVal_fv_proof a z member
      exact current r), valueType_liftVal_proof]
  cases operand <;> simp only [Phi.liftOp, Version.rnOp, opType, value]

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- The current versions after a binder at a later version. -/
theorem current_bind_proof (types : V → Ty Base) (versioned : Option V × Nat → Ty Base)
    (cur : Option V → Nat) (depth : Nat) (x : V) (version : Nat) (later : depth < version)
    (current : ∀ register, versioned (some register, cur (some register)) = types register)
    (fresh : ∀ register v, depth < v → versioned (some register, v) = types register) :
    ∀ register, versioned (some register, Version.setv cur (some x) version (some register)) =
      types register := by
  intro register
  by_cases same : register = x
  · subst same
    simpa [Version.setv] using fresh register version later
  · simpa [Version.setv, same] using current register

/-- A certified terminator, lowered and versioned, is typed. -/
theorem version_term_typed_proof (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (pred : Option K) (live : List (Option V))
    (versioned : Option V × Nat → Ty Base) :
    (tail : Term V (Option K) F) → (cur : Option V → Nat) → (depth : Nat) →
    termTyped graph types exitType pred tail = true →
    (∀ register, versioned (some register, cur (some register)) = types register) →
    (∀ register v, depth < v → versioned (some register, v) = types register) →
    regionTyped versioned (targetType graph types exitType)
      (Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur depth
        (Phi.liftTerm (Phi.OrderedExits.branchValue graph pred) tail).toRegion) = true
  | .br target value, cur, depth, typed, current, _ => by
    cases looked : Phi.OrderedExits.lookup graph target with
    | some block =>
      cases target with
      | none => simp [Phi.OrderedExits.lookup] at looked
      | some key =>
        have found : graph.blocks.lookup key = some block := looked
        obtain ⟨payload, shape, carried⟩ := edge_packet_proof graph types exitType pred key block
          value found typed live cur depth versioned current
        rw [shape]
        simp only [regionTyped, targetType, found, Option.elim, carried, decide_eq_true_eq]
    | none =>
      obtain ⟨payload, shape, carried⟩ := exit_payload_proof graph types exitType pred target value
        looked typed live cur depth versioned current
      have label : targetType graph types exitType target = exitType target := by
        cases target with
        | none => rfl
        | some key =>
          have missing : graph.blocks.lookup key = none := looked
          simp only [targetType, missing, Option.elim]
      rw [shape]
      simp only [regionTyped, label, carried, decide_eq_true_eq]
  | .case operand x left y right, cur, depth, typed, current, fresh => by
    simp only [termTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    have inLeft := version_term_typed_proof graph types exitType pred live versioned left
      (Version.setv cur (some x) (depth + 1)) (depth + 1) typed.1.2
      (current_bind_proof types versioned cur depth x (depth + 1) (by omega) current fresh)
      (fun register v later => fresh register v (by omega))
    have inRight := version_term_typed_proof graph types exitType pred live versioned right
      (Version.setv cur (some y) (depth + 1)) (depth + 1) typed.2
      (current_bind_proof types versioned cur depth y (depth + 1) (by omega) current fresh)
      (fun register v later => fresh register v (by omega))
    simp only [Phi.liftTerm, Term.toRegion, Version.version, regionTyped, Bool.and_eq_true,
      decide_eq_true_eq, opType_version_proof types versioned cur current, typed.1.1,
      fresh x (depth + 1) (by omega), fresh y (depth + 1) (by omega)]
    exact ⟨⟨trivial, inLeft⟩, inRight⟩

/-- A certified body, lowered and versioned, is typed. -/
theorem version_body_typed_proof (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (pred : Option K) (live : List (Option V))
    (versioned : Option V × Nat → Ty Base) :
    (source : Body V (Option K) F) → (cur : Option V → Nat) → (depth : Nat) →
    bodyTyped graph types exitType pred source = true →
    (∀ register, versioned (some register, cur (some register)) = types register) →
    (∀ register v, depth < v → versioned (some register, v) = types register) →
    regionTyped versioned (targetType graph types exitType)
      (Version.version (Versioning.destinations (Phi.OrderedExits.lower graph)) live cur depth
        (Phi.liftBody (Phi.OrderedExits.branchValue graph pred) source).toRegion) = true
  | .term tail, cur, depth, typed, current, fresh =>
    version_term_typed_proof graph types exitType pred live versioned tail cur depth typed current
      fresh
  | .let1 x operand rest, cur, depth, typed, current, fresh => by
    simp only [bodyTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    have inRest := version_body_typed_proof graph types exitType pred live versioned rest
      (Version.setv cur (some x) (depth + 1)) (depth + 1) typed.2
      (current_bind_proof types versioned cur depth x (depth + 1) (by omega) current fresh)
      (fun register v later => fresh register v (by omega))
    simp only [Phi.liftBody, Body.toRegion, Version.version, regionTyped, Bool.and_eq_true,
      decide_eq_true_eq, opType_version_proof types versioned cur current, typed.1,
      fresh x (depth + 1) (by omega)]
    exact ⟨trivial, inRest⟩
  | .let2 x y operand rest, cur, depth, typed, current, fresh => by
    simp only [bodyTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    have inRest := version_body_typed_proof graph types exitType pred live versioned rest
      (Version.setv (Version.setv cur (some x) (depth + 1)) (some y) (depth + 2)) (depth + 2)
      typed.2
      (current_bind_proof types versioned _ (depth + 1) y (depth + 2) (by omega)
        (current_bind_proof types versioned cur depth x (depth + 1) (by omega) current fresh)
        (fun register v later => fresh register v (by omega)))
      (fun register v later => fresh register v (by omega))
    simp only [Phi.liftBody, Body.toRegion, Version.version, regionTyped, Bool.and_eq_true,
      decide_eq_true_eq, opType_version_proof types versioned cur current, typed.1,
      fresh x (depth + 1) (by omega), fresh y (depth + 2) (by omega)]
    exact ⟨trivial, inRest⟩

end VersionedBody

/-! ## The prefix of a versioned block -/

section Prefix

variable {Base V K : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

/-- Unpacking a record is typed, when the source has the type of the
record, each register is bound at its declared type, and each temporary
is bound at the type of the rest of the record. -/
theorem unpack_typed_proof {W L : Type u} (ty : W × Nat → Ty Base) (lt : W → Ty Base)
    (labelType : L → Ty Base) (inner : Region (W × Nat) L F)
    (innerOk : regionTyped ty labelType inner = true) :
    (ys : List W) → (src : W × Nat) → (d : Nat) → ty src = recordType lt ys →
    (∀ i (h : i < ys.length), ty (ys[i], d + 2 * i + 1) = lt ys[i] ∧
      ty (ys[i], d + 2 * i + 2) = recordType lt (ys.drop (i + 1))) →
    regionTyped ty labelType (Version.unpack ys src d inner) = true
  | [], _, _, _, _ => innerOk
  | y :: rest, src, d, source, temps => by
    have head := temps 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero, List.drop_succ_cons,
      List.drop_zero] at head
    simp only [Version.unpack, regionTyped, opType, valueType, source, recordType, head.1, head.2,
      decide_true, Bool.true_and]
    exact unpack_typed_proof ty lt labelType inner innerOk rest (y, d + 2) (d + 2) head.2
      fun i h => by
        have step := temps (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.drop_succ_cons] at step
        have first : d + 2 * (i + 1) + 1 = d + 2 + 2 * i + 1 := by omega
        have second : d + 2 * (i + 1) + 2 = d + 2 + 2 * i + 2 := by omega
        rw [first, second] at step
        exact step

/-- Decoding the φ operands is typed, when the packet register holds
what remains of the operands, each temporary is bound at the type of the
rest of the operands, and the current and later versions of source
registers have their declared types. -/
theorem decode_typed_proof [DecidableEq V] [DecidableEq (Option K)]
    (ty : Option V × Nat → Ty Base) (types : V → Ty Base) (labelType : Option K → Ty Base)
    (lenv : Option K → Option (List (Option V))) (live : List (Option V))
    (inner : Body (Option V) (Option K) F)
    (innerOk : ∀ cur d, (∀ r, ty (some r, cur (some r)) = types r) →
      (∀ r v, d < v → ty (some r, v) = types r) →
      regionTyped ty labelType (Version.version lenv live cur d inner.toRegion) = true) :
    (rows : List (Row V K)) → (cur : Option V → Nat) → (d : Nat) →
    ty (none, cur none) = argsType types rows →
    (∀ j, j < rows.length → ty (none, d + 2 * j + 2) = argsType types (rows.drop (j + 1))) →
    (∀ r, ty (some r, cur (some r)) = types r) → (∀ r v, d < v → ty (some r, v) = types r) →
    regionTyped ty labelType (Version.version lenv live cur d (Phi.decode rows inner).toRegion) =
      true
  | [], cur, d, _, _, current, fresh => innerOk cur d current fresh
  | row :: rest, cur, d, packet, tails, current, fresh => by
    have head := tails 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.drop_succ_cons, List.drop_zero] at head
    simp only [Phi.decode, Body.toRegion, Version.version, Version.rnOp, Version.rn, regionTyped,
      opType, valueType, packet, argsType, fresh row.dst (d + 1) (by omega), head, decide_true,
      Bool.true_and]
    exact decode_typed_proof ty types labelType lenv live inner innerOk rest _ (d + 2)
      (by simpa [Version.setv] using head)
      (fun j h => by
        have step := tails (j + 1) (by simp; omega)
        simp only [List.drop_succ_cons] at step
        have shift : d + 2 * (j + 1) + 2 = d + 2 + 2 * j + 2 := by omega
        rw [shift] at step
        exact step)
      (fun r => by
        by_cases same : r = row.dst
        · subst same
          simpa [Version.setv] using fresh row.dst (d + 1) (by omega)
        · simpa [Version.setv, same] using current r)
      (fun r v later => fresh r v (by omega))

/-- The current version of a name after unpacking a record: its earlier
version, or the version at which a position of the record was bound. -/
theorem unpackCur_range_proof {W : Type u} [DecidableEq W] (z : W) : (ys : List W) →
    (cur : W → Nat) → (d : Nat) →
    Version.unpackCur ys cur d z = cur z ∨
      ∃ i, i < ys.length ∧ Version.unpackCur ys cur d z = d + 2 * i + 1
  | [], _, _ => .inl rfl
  | y :: rest, cur, d => by
    rcases unpackCur_range_proof z rest (Version.setv cur y (d + 1)) (d + 2) with kept | ⟨i, h, at_⟩
    · by_cases same : z = y
      · exact .inr ⟨0, by simp, by
          rw [Version.unpackCur, kept]
          simp [Version.setv, same]⟩
      · exact .inl (by
          rw [Version.unpackCur, kept]
          simp [Version.setv, same])
    · exact .inr ⟨i + 1, by simp; omega, by rw [Version.unpackCur, at_]; omega⟩

/-- A name outside an unpacked record keeps its version. -/
theorem unpackCur_outside_proof {W : Type u} [DecidableEq W] (z : W) : (ys : List W) →
    (cur : W → Nat) → (d : Nat) → z ∉ ys → Version.unpackCur ys cur d z = cur z
  | [], _, _, _ => rfl
  | y :: rest, cur, d, absent => by
    simp only [List.mem_cons, not_or] at absent
    rw [Version.unpackCur, unpackCur_outside_proof z rest _ _ absent.2]
    simp [Version.setv, absent.1]

variable [DecidableEq V] [DecidableEq K]

/-- A versioned block of the lowering of a certified graph is typed, from
its packet at the computed packet type. -/
theorem block_typed_proof (graph : Graph V K F) (types : V → Ty Base)
    (exitType : Option K → Ty Base) (certificate : certified graph types exitType = true)
    (item : K × Block V K F) (member : item ∈ graph.blocks) :
    regionTyped (blockTyping graph types item.1 item.2) (targetType graph types exitType)
      (Versioning.compileBlock (Phi.OrderedExits.lower graph)
        (Phi.OrderedExits.lowerBlock graph item.1 item.2)).body.toRegion = true := by
  simp only [certified, Bool.and_eq_true, List.all_eq_true] at certificate
  have bodyOk := certificate.2 item member
  rw [compileBlock_toRegion]
  generalize slotsEq : Versioning.slots (Phi.OrderedExits.lower graph)
    (Phi.OrderedExits.lowerBlock graph item.1 item.2) = slots
  have sources : ∀ y ∈ slots, ∃ r, y = some r := slotsEq ▸ slots_some_proof graph item.1 item.2
  -- the typing at the names the prefix and the body use
  have atSource : ∀ r v, (v % 2 = 1 ∨ v < 4 ∨ 2 + 2 * slots.length < v) →
      blockTyping graph types item.1 item.2 (some r, v) = types r := by
    intro r v side
    simp only [blockTyping, slotsEq]
    split
    · omega
    · rfl
  have atTail : ∀ r i, i < slots.length →
      blockTyping graph types item.1 item.2 (some r, 2 + 2 * i + 2) =
        recordType (lifted types) (slots.drop (i + 1)) := by
    intro r i h
    have inside : (2 + 2 * i + 2) % 2 = 0 ∧ 4 ≤ 2 + 2 * i + 2 ∧
        2 + 2 * i + 2 ≤ 2 + 2 * slots.length := by omega
    simp only [blockTyping, slotsEq, inside, and_self, ↓reduceIte]
    rw [show (2 + 2 * i + 2 - 2) / 2 = i + 1 by omega]
  have atArgs : ∀ j, blockTyping graph types item.1 item.2
      (none, 2 + 2 * slots.length + 2 * j + 2) = argsType types (item.2.rows.drop (j + 1)) := by
    intro j
    have shape : 2 + 2 * slots.length + 2 * j + 2 = (2 * slots.length + 2 * j + 1) + 3 := by omega
    rw [shape]
    simp only [blockTyping, slotsEq]
    rw [show (2 * slots.length + 2 * j + 1 + 3 - (2 + 2 * slots.length)) / 2 = j + 1 by omega]
  show regionTyped _ _ (.let2 (none, 1) (none, 2) (.val (.var (none, 0)))
    (Version.unpack slots (none, 2) 2 (Version.version _ _ _ (2 + 2 * slots.length)
      (Phi.decode item.2.rows (Phi.liftBody (Phi.OrderedExits.branchValue graph (some item.1))
        item.2.body)).toRegion))) = true
  have packet : blockTyping graph types item.1 item.2 (none, 0) =
      .product (blockTyping graph types item.1 item.2 (none, 1))
        (blockTyping graph types item.1 item.2 (none, 2)) := rfl
  simp only [regionTyped, opType, valueType, packet, decide_true, Bool.true_and]
  refine unpack_typed_proof _ (lifted types) _ _ ?_ slots (none, 2) 2
    (by simp only [blockTyping, slotsEq]) (fun i h => ?_)
  · refine decode_typed_proof _ types _ _ _ _ (fun cur d current fresh =>
      version_body_typed_proof graph types exitType (some item.1) _ _ item.2.body cur d bodyOk
        current fresh) item.2.rows _ (2 + 2 * slots.length) ?_ (fun j _ => atArgs j) (fun r => ?_)
      (fun r v later => atSource r v (.inr (.inr later)))
    · have outside : (none : Option V) ∉ slots := fun listed => by
        obtain ⟨r, impossible⟩ := sources none listed
        cases impossible
      rw [unpackCur_outside_proof none slots _ _ outside]
      simp only [Version.setv]
      rfl
    · rcases unpackCur_range_proof (some r) slots (Version.setv (fun _ => 0) none 1) 2 with
        kept | ⟨i, _, at_⟩
      · exact (congrArg (fun v => blockTyping graph types item.1 item.2 (some r, v)) kept).trans
          (atSource r _ (.inr (.inl (by simp [Version.setv]))))
      · exact (congrArg (fun v => blockTyping graph types item.1 item.2 (some r, v)) at_).trans
          (atSource r _ (.inl (by omega)))
  · obtain ⟨r, here⟩ := sources slots[i] (List.getElem_mem h)
    rw [here]
    exact ⟨atSource r _ (.inl (by omega)), atTail r i h⟩

end Prefix

/-! ## From named typing to the positional check

The elaboration replaces names by positions. A positional context agrees
with a typing of names when every position that a name is sent to has
the type of the name. Then an elaborated value has the type of the
value, and an elaborated body that is typed by name passes the
positional check. -/

section Checker

variable {Base N K : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

/-- An elaborated value has the type of the value. -/
theorem value_infer_proof {n : Nat} (names : Names N n) (ctx : BoundCtx (Ty Base) n)
    (ty : N → Ty Base) (agree : ∀ z i, names z = some i → ctx.get i = ty z) :
    (v : Val N) → (tm : LetCase.LocallyNameless.Tm Empty F n) → value names v = some tm →
    infer ctx tm = some (valueType ty v)
  | .var reg, tm, elaborated => by
    simp only [value, Option.map_eq_some_iff] at elaborated
    obtain ⟨i, found, rfl⟩ := elaborated
    simp only [infer, valueType, agree reg i found]
  | .unit, tm, elaborated => by
    simp only [value, Option.some.injEq] at elaborated
    subst elaborated
    rfl
  | .pair a b, tm, elaborated => by
    simp only [value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at elaborated
    obtain ⟨left, inLeft, right, inRight, rfl⟩ := elaborated
    simp only [infer, valueType, value_infer_proof names ctx ty agree a left inLeft,
      value_infer_proof names ctx ty agree b right inRight, Option.bind_some, Option.map_some]

/-- An elaborated operand has the type of the operand. -/
theorem operand_infer_proof {n : Nat} (names : Names N n) (ctx : BoundCtx (Ty Base) n)
    (ty : N → Ty Base) (agree : ∀ z i, names z = some i → ctx.get i = ty z) (op : Op N F)
    (tm : LetCase.LocallyNameless.Tm Empty F n) (A : Ty Base)
    (elaborated : operand names op = some tm) (typed : opType ty op = some A) :
    infer ctx tm = some A := by
  cases op with
  | val a =>
    simp only [opType, Option.some.injEq] at typed
    subst typed
    exact value_infer_proof names ctx ty agree a tm elaborated
  | app f a =>
    simp only [operand, Option.map_eq_some_iff] at elaborated
    obtain ⟨arg, inArg, rfl⟩ := elaborated
    simp only [opType] at typed
    split at typed
    · rename_i source
      simp only [Option.some.injEq] at typed
      subst typed
      simp only [infer, value_infer_proof names ctx ty agree a arg inArg, source, ↓reduceIte]
    · cases typed
  | inl a => simp [operand] at elaborated
  | inr a => simp [operand] at elaborated
  | abort a => simp [operand] at elaborated

variable [DecidableEq N]

omit [DecidableEq Base] [HasTy F (Ty Base)] in
/-- A binder extends the agreement: its position is the newest slot, of
the type of its name, and the older names move one slot. -/
theorem agree_bind_proof {n : Nat} (names : Names N n) (ctx : BoundCtx (Ty Base) n)
    (ty : N → Ty Base) (agree : ∀ z i, names z = some i → ctx.get i = ty z) (x : N) :
    ∀ z i, bindName names x z = some i → (ctx.snoc (ty x)).get i = ty z := by
  intro z i bound
  simp only [bindName] at bound
  split at bound
  · rename_i same
    cases bound
    rw [same]
    rfl
  · obtain ⟨j, found, rfl⟩ := Option.map_eq_some_iff.mp bound
    exact agree z j found

/-- An elaborated terminator that is typed by name passes the positional
check. -/
theorem term_checked_proof {labels : Nat} (index : K → Option (Fin labels))
    (types : Fin labels → Ty Base) (ty : N → Ty Base) (labelType : K → Ty Base)
    (labelsOk : ∀ label i, index label = some i → types i = labelType label) :
    {n : Nat} → (names : Names N n) → (ctx : BoundCtx (Ty Base) n) → (tail : Term N K F) →
    (code : LambdaSSA.Flat F labels n) → (∀ z i, names z = some i → ctx.get i = ty z) →
    regionTyped ty labelType tail.toRegion = true → term index names tail = some code →
    checkBody types ctx code = true
  | _, names, ctx, .br label arg, code, agree, typed, elaborated => by
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at elaborated
    obtain ⟨i, indexed, tm, inArg, rfl⟩ := elaborated
    simp only [Term.toRegion, regionTyped, decide_eq_true_eq] at typed
    simp only [checkBody, value_infer_proof names ctx ty agree arg tm inArg, typed,
      labelsOk label i indexed, decide_true]
  | _, names, ctx, .case op x left y right, code, agree, typed, elaborated => by
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at elaborated
    obtain ⟨discr, inOp, l, inLeft, r, inRight, rfl⟩ := elaborated
    simp only [Term.toRegion, regionTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    simp only [checkBody, operand_infer_proof names ctx ty agree op discr _ inOp typed.1.1,
      Bool.and_eq_true]
    exact ⟨term_checked_proof index types ty labelType labelsOk _ _ left l
        (agree_bind_proof names ctx ty agree x) typed.1.2 inLeft,
      term_checked_proof index types ty labelType labelsOk _ _ right r
        (agree_bind_proof names ctx ty agree y) typed.2 inRight⟩

/-- An elaborated body that is typed by name passes the positional check,
when the positional context agrees with the typing of names and each
indexed label has the type of the label. -/
theorem body_checked_proof {labels : Nat} (index : K → Option (Fin labels))
    (types : Fin labels → Ty Base) (ty : N → Ty Base) (labelType : K → Ty Base)
    (labelsOk : ∀ label i, index label = some i → types i = labelType label) :
    {n : Nat} → (names : Names N n) → (ctx : BoundCtx (Ty Base) n) → (source : Body N K F) →
    (code : LambdaSSA.Flat F labels n) → (∀ z i, names z = some i → ctx.get i = ty z) →
    regionTyped ty labelType source.toRegion = true → body index names source = some code →
    checkBody types ctx code = true
  | _, names, ctx, .term tail, code, agree, typed, elaborated =>
    term_checked_proof index types ty labelType labelsOk names ctx tail code agree typed elaborated
  | _, names, ctx, .let1 x op rest, code, agree, typed, elaborated => by
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at elaborated
    obtain ⟨arg, inOp, tail, inRest, rfl⟩ := elaborated
    simp only [Body.toRegion, regionTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    simp only [checkBody, operand_infer_proof names ctx ty agree op arg _ inOp typed.1]
    exact body_checked_proof index types ty labelType labelsOk _ _ rest tail
      (agree_bind_proof names ctx ty agree x) typed.2 inRest
  | _, names, ctx, .let2 x y op rest, code, agree, typed, elaborated => by
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at elaborated
    obtain ⟨arg, inOp, tail, inRest, rfl⟩ := elaborated
    simp only [Body.toRegion, regionTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    simp only [checkBody, operand_infer_proof names ctx ty agree op arg _ inOp typed.1]
    exact body_checked_proof index types ty labelType labelsOk _ _ rest tail
      (agree_bind_proof (bindName names x) (ctx.snoc (ty x)) ty
        (agree_bind_proof names ctx ty agree x) y) typed.2 inRest

end Checker

/-! ## The elaborated graph -/

section Assembly

variable {Base V K : Type u} {F : Type v}

/-- The value found at a key is the value at the first position of the
key. -/
theorem lookup_first_proof [DecidableEq K] {B : Type*} : (entries : List (K × B)) → (j : Nat) →
    (h : j < entries.length) → (∀ i (hi : i < j), entries[i].1 ≠ entries[j].1) →
    entries.lookup entries[j].1 = some entries[j].2
  | [], j, h, _ => by simp at h
  | (k, b) :: rest, 0, _, _ => by simp
  | (k, b) :: rest, j + 1, h, earlier => by
    have inRest : j < rest.length := by simpa using h
    have head := earlier 0 (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at head ⊢
    have differs : (rest[j].1 == k) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun same => head same.symm
    simp only [List.lookup_cons, differs]
    exact lookup_first_proof rest j inRest fun i hi => by
      have := earlier (i + 1) (by omega)
      simpa using this

/-- No value is found at a key that no entry has. -/
theorem lookup_absent_proof [DecidableEq K] {B : Type*} : (entries : List (K × B)) → (key : K) →
    (∀ item ∈ entries, item.1 ≠ key) → entries.lookup key = none
  | [], _, _ => rfl
  | (k, b) :: rest, key, absent => by
    have differs : (key == k) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun same => absent (k, b) (by simp) same.symm
    simp only [List.lookup_cons, differs]
    exact lookup_absent_proof rest key fun item member => absent item (by simp [member])

variable [DecidableEq V] [DecidableEq K]

/-- The blocks of the versioned lowering, in the order of the φ graph. -/
theorem compiled_blocks_proof (graph : Graph V K F) :
    (Versioning.compile (Phi.OrderedExits.lower graph)).blocks =
      graph.blocks.map fun item =>
        (some item.1, Versioning.compileBlock (Phi.OrderedExits.lower graph)
          (Phi.OrderedExits.lowerBlock graph item.1 item.2)) := by
  simp [Versioning.compile, Phi.OrderedExits.lower, List.map_map, Function.comp_def]

/-- The computed packet type at the position of a block. -/
theorem internal_at_proof (graph : Graph V K F) (types : V → Ty Base)
    (i : Fin (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length)
    (h : i.val < graph.blocks.length) :
    internal graph types i = packetType graph types graph.blocks[i.val].1 graph.blocks[i.val].2 := by
  simp [internal, packets, List.getD_eq_getElem?_getD, h]

/-- The index that the elaboration gives a label has the type that a jump
to the label carries: the computed packet type at the first block of
that label, or the declared type at the first position of the label
among the exits. -/
theorem labels_typed_proof (graph : Graph V K F) (exits : List (Option K)) (types : V → Ty Base)
    (exitType : Option K → Ty Base) :
    ∀ label i, labelIndex (Versioning.compile (Phi.OrderedExits.lower graph)).blocks exits label =
        some i →
      SSA.FiniteSum.append (internal graph types) (external exits exitType) i =
        targetType graph types exitType label := by
  have shape := compiled_blocks_proof graph
  have keyAt : ∀ (i : Nat) (hv : i < (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length)
      (hg : i < graph.blocks.length),
      (Versioning.compile (Phi.OrderedExits.lower graph)).blocks[i].1 = some graph.blocks[i].1 := by
    intro i hv hg
    simp [shape]
  intro label i indexed
  simp only [labelIndex] at indexed
  split at indexed
  · rename_i j found
    simp only [Option.some.injEq] at indexed
    subst indexed
    obtain ⟨hit, firstHit⟩ := List.findFinIdx?_eq_some_iff.mp found
    have inGraph : j.val < graph.blocks.length := by
      have := j.isLt
      simpa [shape] using this
    have labelEq : label = some graph.blocks[j.val].1 :=
      (of_decide_eq_true hit).trans (keyAt j.val j.isLt inGraph)
    have first : ∀ i (hi : i < j.val), graph.blocks[i].1 ≠ graph.blocks[j.val].1 := by
      intro i hi same
      exact firstHit ⟨i, by omega⟩ hi (decide_eq_true
        ((labelEq.trans (congrArg some same.symm)).trans (keyAt i (by omega) (by omega)).symm))
    have looked := lookup_first_proof graph.blocks j.val inGraph first
    rw [SSA.FiniteSum.append_left, labelEq, internal_at_proof graph types j inGraph]
    simp only [targetType, looked, Option.elim]
  · rename_i found
    simp only [Option.map_eq_some_iff] at indexed
    obtain ⟨e, exitFound, rfl⟩ := indexed
    obtain ⟨hit, _⟩ := List.findFinIdx?_eq_some_iff.mp exitFound
    have labelEq : label = exits[e] := of_decide_eq_true hit
    have absent := List.findFinIdx?_eq_none_iff.mp found
    have target : targetType graph types exitType label = exitType label := by
      cases label with
      | none => rfl
      | some key =>
        have missing : graph.blocks.lookup key = none :=
          lookup_absent_proof graph.blocks key fun item member same =>
            absent (some item.1, Versioning.compileBlock (Phi.OrderedExits.lower graph)
              (Phi.OrderedExits.lowerBlock graph item.1 item.2))
              (shape ▸ List.mem_map.mpr ⟨item, member, rfl⟩)
              (decide_eq_true (congrArg some same.symm))
        simp only [targetType, missing, Option.elim]
    rw [SSA.FiniteSum.append_right, target, labelEq]
    rfl

variable [DecidableEq Base] [HasTy F (Ty Base)]

/-- The elaborated lowering of a certified φ graph passes the typing check
at the computed packet types, when the capture context has the declared
types of the captures. -/
theorem certified_checks_proof (graph : Graph V K F) (exits : List (Option K))
    (types : V → Ty Base) (exitType : Option K → Ty Base) {n : Nat} (captures : Fin n → Option V)
    (captureTypes : BoundCtx (Ty Base) n)
    (target : LambdaSSA.FiniteCFG F (Versioning.compile (Phi.OrderedExits.lower graph)).blocks.length
      exits.length n)
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, captureTypes.get i = lifted types (captures i))
    (elaborated : NamedFlat.compile (Phi.OrderedExits.lower graph) exits captures = some target) :
    check target captureTypes (internal graph types) (external exits exitType) = true := by
  have labelsOk := labels_typed_proof graph exits types exitType
  have shape := compiled_blocks_proof graph
  have bodies := certificate
  simp only [certified, Bool.and_eq_true, List.all_eq_true] at bodies
  have unfolded : elaborate (Versioning.compile (Phi.OrderedExits.lower graph)) exits
      (fun i => (captures i, 0)) = some target := elaborated
  simp only [elaborate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at unfolded
  obtain ⟨entry, inEntry, rows, inRows, rfl⟩ := unfolded
  simp only [check, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun i _ => ?_⟩
  · refine body_checked_proof _ _ (canon types) (targetType graph types exitType) labelsOk _
      captureTypes _ entry (fun z i found => ?_) ?_ inEntry
    · have located : (List.finRange n).find? (fun i => decide ((captures i, 0) = z)) = some i :=
        found
      have here : (captures i, 0) = z := of_decide_eq_true
        (List.find?_some (p := fun i => decide ((captures i, 0) = z)) located)
      rw [declared i, ← here]
      rfl
    · rw [compile_entry_toRegion]
      exact version_body_typed_proof graph types exitType none _ (canon types) graph.entry
        (fun _ => 0) 0 bodies.1 (fun _ => rfl) (fun _ _ _ => rfl)
  · have inGraph : i.val < graph.blocks.length := by
      have := i.isLt
      simpa [shape] using this
    have at_ : (Versioning.compile (Phi.OrderedExits.lower graph)).blocks[i] =
        (some graph.blocks[i.val].1, Versioning.compileBlock (Phi.OrderedExits.lower graph)
          (Phi.OrderedExits.lowerBlock graph graph.blocks[i.val].1 graph.blocks[i.val].2)) := by
      simp [shape]
    have row := tabulate_at inRows i
    simp only [at_] at row
    refine body_checked_proof _ _
      (blockTyping graph types graph.blocks[i.val].1 graph.blocks[i.val].2)
      (targetType graph types exitType) labelsOk _ _ _ (rows i) (fun z j bound => ?_)
      (block_typed_proof graph types exitType certificate graph.blocks[i.val]
        (List.getElem_mem inGraph)) row
    simp only [blockNames, bindName] at bound
    split at bound
    · rename_i same
      cases bound
      rw [same]
      exact internal_at_proof graph types i inGraph
    · simp at bound

end Assembly

/-! ## The forwarding normalization keeps the certificate

The normalization renames the reads of a body by the reader of its block,
renames each φ operand by the reader of its predecessor, and appends to
the rows of a block one row for each register that the block receives,
with one operand for each predecessor. It reorders nothing. A copy has
the declared type of its register, so every reader keeps types. -/

section Forwarded

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Forward.Name Forward.Table Forward.forward
  Forward.reader Forward.row Forward.copyRow Forward.block)

variable {Base V K : Type u} {F : Type v}

/-- A renamed value has the type of the value, when the renaming keeps
types. -/
theorem valueType_rename_proof {W : Type u} (types : V → Ty Base) (renamed : W → Ty Base)
    (read : V → W) (keeps : ∀ z, renamed (read z) = types z) : (value : Val V) →
    valueType renamed (value.rename read) = valueType types value
  | .var x => keeps x
  | .unit => rfl
  | .pair a b => by
    simp only [Val.rename, valueType, valueType_rename_proof types renamed read keeps a,
      valueType_rename_proof types renamed read keeps b]

/-- A renamed operand has the type of the operand, when the renaming keeps
types. -/
theorem opType_rename_proof [DecidableEq Base] [HasTy F (Ty Base)] {W : Type u}
    (types : V → Ty Base) (renamed : W → Ty Base) (read : V → W)
    (keeps : ∀ z, renamed (read z) = types z) (operand : Op V F) :
    opType renamed (operand.rename read) = opType types operand := by
  cases operand <;>
    simp only [Op.rename, opType, valueType_rename_proof types renamed read keeps]

variable [DecidableEq V] [DecidableEq K]

/-- Every reader keeps types: a copy has the declared type of its
register. -/
theorem forwardTypes_reader_proof (types : V → Ty Base) (table : Forward.Table V K)
    (pred : Option K) (z : V) : forwardTypes types (Forward.reader table pred z) = types z := by
  cases pred with
  | none => rfl
  | some key =>
    simp only [Forward.reader]
    split <;> rfl

omit [DecidableEq V] in
/-- The operand of an original row for a predecessor is the original
operand, read as the predecessor reads it. -/
theorem row_operand_proof [DecidableEq V] (table : Forward.Table V K) (source : Option K)
    (r : Row V K) :
    (Forward.row table r).operand source =
      (r.operand source).rename (Forward.reader table source) := by
  have inner : ∀ incoming : List (Option K × Val V),
      (incoming.map fun item => (item.1, item.2.rename (Forward.reader table item.1))).lookup
          source =
        (incoming.lookup source).map (·.rename (Forward.reader table source)) := by
    intro incoming
    induction incoming with
    | nil => rfl
    | cons item rest ih =>
      rcases item with ⟨pred, value⟩
      simp only [List.map_cons, List.lookup_cons]
      split
      · rename_i same
        rw [eq_of_beq same]
        rfl
      · exact ih
  simp only [Row.operand, Forward.row]
  rw [inner]
  cases r.incoming.lookup source <;> rfl

omit [DecidableEq V] in
/-- The operand of a copy row for a listed predecessor is the register as
the predecessor reads it. -/
theorem copy_operand_listed_proof [DecidableEq V] (table : Forward.Table V K) (key : K)
    (register : V) (source : Option K) : (predecessors : List (Option K)) →
    source ∈ predecessors →
    (Forward.copyRow table predecessors key register).operand source =
      .var (Forward.reader table source register)
  | [], member => by cases member
  | pred :: rest, member => by
    simp only [Row.operand, Forward.copyRow, List.map_cons, List.lookup_cons]
    split
    · rename_i same
      rw [eq_of_beq same]
      rfl
    · rename_i other
      have differs : source ≠ pred := fun eq => by simp [eq] at other
      exact copy_operand_listed_proof table key register source rest
        ((List.mem_cons.mp member).resolve_left differs)

variable [DecidableEq Base] [HasTy F (Ty Base)]

/-- A certified terminator stays certified under the normalization, when
its block is a listed predecessor of every block it jumps to. -/
theorem forward_term_typed_proof (graph : Graph V K F) (table : Forward.Table V K)
    (types : V → Ty Base) (exitType : Option K → Ty Base) (pred : Option K) :
    (tail : Term V (Option K) F) →
    (∀ key, some key ∈ tail.targets → pred ∈ graph.predecessors key) →
    termTyped graph types exitType pred tail = true →
    termTyped (Forward.forward graph table) (forwardTypes types) exitType pred
      (Phi.Forward.term (Forward.reader table pred) tail) = true
  | .br target value, listed, typed => by
    cases target with
    | none =>
      have absent : Phi.OrderedExits.lookup (Forward.forward graph table) none = none := rfl
      have source : Phi.OrderedExits.lookup graph none = none := rfl
      simp only [termTyped, source, decide_eq_true_eq] at typed
      simp only [Phi.Forward.term, termTyped, absent, decide_eq_true_eq,
        valueType_rename_proof types _ _ (forwardTypes_reader_proof types table pred), typed]
    | some key =>
      have looked : Phi.OrderedExits.lookup (Forward.forward graph table) (some key) =
          (graph.blocks.lookup key).map (Forward.block table graph key) :=
        Phi.Forward.lookup_forward graph table key
      have source : Phi.OrderedExits.lookup graph (some key) = graph.blocks.lookup key := rfl
      cases found : graph.blocks.lookup key with
      | none =>
        rw [found] at looked source
        simp only [termTyped, source, decide_eq_true_eq] at typed
        simp only [Phi.Forward.term, termTyped, looked, Option.map_none, decide_eq_true_eq,
          valueType_rename_proof types _ _ (forwardTypes_reader_proof types table pred), typed]
      | some block =>
        rw [found] at looked source
        simp only [termTyped, source, List.all_eq_true, decide_eq_true_eq] at typed
        have member := listed key (by simp [Term.targets])
        simp only [Phi.Forward.term, termTyped, looked, Option.map_some, List.all_eq_true,
          decide_eq_true_eq, Forward.block, List.mem_append, List.mem_map]
        rintro row (⟨original, inRows, rfl⟩ | ⟨register, _, rfl⟩)
        · rw [row_operand_proof,
            valueType_rename_proof types _ _ (forwardTypes_reader_proof types table pred)]
          exact typed original inRows
        · rw [copy_operand_listed_proof table key register pred _ member]
          exact forwardTypes_reader_proof types table pred register
  | .case operand x left y right, listed, typed => by
    simp only [termTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    simp only [Phi.Forward.term, termTyped, Bool.and_eq_true, decide_eq_true_eq,
      opType_rename_proof types _ _ (forwardTypes_reader_proof types table pred)]
    exact ⟨⟨typed.1.1, forward_term_typed_proof graph table types exitType pred left
        (fun key member => listed key (by simp [Term.targets, member])) typed.1.2⟩,
      forward_term_typed_proof graph table types exitType pred right
        (fun key member => listed key (by simp [Term.targets, member])) typed.2⟩

/-- A certified body stays certified under the normalization, when its
block is a listed predecessor of every block it jumps to. -/
theorem forward_body_typed_proof (graph : Graph V K F) (table : Forward.Table V K)
    (types : V → Ty Base) (exitType : Option K → Ty Base) (pred : Option K) :
    (source : Body V (Option K) F) →
    (∀ key, some key ∈ source.targets → pred ∈ graph.predecessors key) →
    bodyTyped graph types exitType pred source = true →
    bodyTyped (Forward.forward graph table) (forwardTypes types) exitType pred
      (Phi.Forward.body (Forward.reader table pred) source) = true
  | .term tail, listed, typed =>
    forward_term_typed_proof graph table types exitType pred tail listed typed
  | .let1 x operand rest, listed, typed => by
    simp only [bodyTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    simp only [Phi.Forward.body, bodyTyped, Bool.and_eq_true, decide_eq_true_eq,
      opType_rename_proof types _ _ (forwardTypes_reader_proof types table pred)]
    exact ⟨typed.1, forward_body_typed_proof graph table types exitType pred rest listed typed.2⟩
  | .let2 x y operand rest, listed, typed => by
    simp only [bodyTyped, Bool.and_eq_true, decide_eq_true_eq] at typed
    simp only [Phi.Forward.body, bodyTyped, Bool.and_eq_true, decide_eq_true_eq,
      opType_rename_proof types _ _ (forwardTypes_reader_proof types table pred)]
    exact ⟨typed.1, forward_body_typed_proof graph table types exitType pred rest listed typed.2⟩

/-- The normalization keeps the certificate, for any table. -/
theorem certified_forward_proof (graph : Graph V K F) (table : Forward.Table V K)
    (types : V → Ty Base) (exitType : Option K → Ty Base)
    (certificate : certified graph types exitType = true) :
    certified (Forward.forward graph table) (forwardTypes types) exitType = true := by
  simp only [certified, Bool.and_eq_true, List.all_eq_true] at certificate ⊢
  refine ⟨?_, fun item member => ?_⟩
  · exact forward_body_typed_proof graph table types exitType none graph.entry
      (fun key target => by simp [Graph.predecessors, target]) certificate.1
  · obtain ⟨source, original, rfl⟩ := List.mem_map.mp member
    exact forward_body_typed_proof graph table types exitType (some source.1) source.2.body
      (fun key target => List.mem_append_right _
        (List.mem_filterMap.mpr ⟨source, original, by simp [target]⟩))
      (certificate.2 source original)

end Forwarded

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping
