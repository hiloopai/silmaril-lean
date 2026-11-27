module

public import Silmaril.Formats.Hive.WritePlan.Restore.Defs
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
import Silmaril.Formats.Hive.TypedPartitions.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Hive.WritePlan
open Silmaril.Formats.Hive.TypedPartitions (Convert Field PartitionSchema extendRow partitionCells physicalCells)

variable {Kind : Type*} {Value : Kind → Type*} {EncodeFailure DecodeFailure : Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

private theorem mapM_accepted {A B Err : Type*} (check : A → Except Err B)
    {input : List A} {output : List B} (checked : input.mapM check = .ok output) :
    List.Forall₂ (fun x y => check x = .ok y) input output := by
  induction input generalizing output with
  | nil =>
    cases checked
    exact .nil
  | cons head tail ih =>
    rw [List.mapM_cons] at checked
    cases first : check head with
    | error reason => simp [first, bind, Except.bind] at checked
    | ok next =>
      cases later : tail.mapM check with
      | error reason => simp [first, later, bind, Except.bind] at checked
      | ok rest =>
        simp only [first, later, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at checked
        subst output
        exact .cons first (ih later)

private theorem sequenceFin_accepted (n : Nat) {R : Fin n → Type*} {Err : Type*}
    (check : (i : Fin n) → Except (TypedPartitions.Error Err) (R i)) (cells : (i : Fin n) → R i)
    (accepted : ∀ i, check i = .ok (cells i)) :
    TypedPartitions.decode.sequenceFin n check = .ok cells := by
  induction n with
  | zero =>
    rw [TypedPartitions.decode.sequenceFin]
    change Except.ok (fun i => nomatch i) = Except.ok cells
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [TypedPartitions.decode.sequenceFin]
    simp only [accepted 0, bind, Except.bind]
    rw [ih (fun i => check i.succ) (fun i => cells i.succ) (fun i => accepted i.succ)]
    change Except.ok (fun i => Fin.cases (cells 0) (fun j => cells j.succ) i) = Except.ok cells
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

private theorem encodeEntry_name (encode : Encode Value EncodeFailure) (field : Field Kind)
    (cell : Option (Value field.kind)) (entry : PartitionPath.Entry)
    (encoded : encodeEntry encode field cell = .ok entry) : field.name = entry.1 := by
  cases cell with
  | none => exact congrArg Prod.fst (Except.ok.inj encoded)
  | some value =>
    cases checked : encode field value with
    | error reason => simp [encodeEntry, checked, Except.mapError, Except.map] at encoded
    | ok text =>
      have entryEq : (field.name, some text) = entry := by
        simpa [encodeEntry, checked, Except.mapError, Except.map] using encoded
      exact congrArg Prod.fst entryEq

private theorem decodeField_encodeEntry (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (field : Field Kind) (inverse : ∀ value text, encode field value = .ok text → decode field text = .ok value)
    (cell : Option (Value field.kind)) (entries : PartitionPath.Partition) (entry : PartitionPath.Entry)
    (encoded : encodeEntry encode field cell = .ok entry)
    (found : PartitionPath.lookup field.name entries = some entry.2) :
    TypedPartitions.decodeField decode entries field = .ok cell := by
  cases cell with
  | none =>
    have entryEq : (field.name, (none : Option String)) = entry := Except.ok.inj encoded
    rw [← entryEq] at found
    rw [TypedPartitions.decodeField, found]
  | some value =>
    cases checked : encode field value with
    | error reason => simp [encodeEntry, checked, Except.mapError, Except.map] at encoded
    | ok text =>
      have entryEq : (field.name, some text) = entry := by
        simpa [encodeEntry, checked, Except.mapError, Except.map] using encoded
      rw [← entryEq] at found
      rw [TypedPartitions.decodeField, found]
      change ((decode field text).map some).mapError _ = _
      rw [inverse _ _ checked]
      rfl

theorem encodeEntries_keys (encode : Encode Value EncodeFailure) (cells : Scan.Row schema.toScan Value)
    {entries : PartitionPath.Partition} (encoded : encodeEntries encode cells = .ok entries) :
    entries.map Prod.fst = schema.keys := by
  let check (i : Fin schema.fields.size) := encodeEntry encode schema.fields[i] (cells i)
  have accepted := mapM_accepted check encoded
  have nameOf (i : Fin schema.fields.size) (entry : PartitionPath.Entry) (ok : check i = .ok entry) :
      schema.fields[i].name = entry.1 :=
    encodeEntry_name encode schema.fields[i] (cells i) entry ok
  have fieldNames : (List.finRange schema.fields.size).map (fun i => schema.fields[i].name) = schema.keys := by
    simp only [List.finRange, List.map_ofFn, Function.comp_def, PartitionSchema.keys]
    rw [← List.ofFn_getElem (xs := schema.fields.toList), List.map_ofFn]
    rfl
  have aligned : List.Forall₂ (· = ·)
      ((List.finRange schema.fields.size).map (fun i => schema.fields[i].name)) (entries.map Prod.fst) :=
    List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (accepted.imp nameOf))
  rw [fieldNames, List.forall₂_eq_eq_eq] at aligned
  exact aligned.symm

private theorem decode_encodedEntries (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (cells : Scan.Row schema.toScan Value)
    {entries : PartitionPath.Partition} (encoded : encodeEntries encode cells = .ok entries)
    (keysValid : PartitionPath.validateKeys schema.keys = .ok ())
    (unique : (entries.map Prod.fst).Nodup) :
    TypedPartitions.decode schema decode entries = .ok cells := by
  let check (i : Fin schema.fields.size) := encodeEntry encode schema.fields[i] (cells i)
  have accepted := mapM_accepted check encoded
  have nameOf (i : Fin schema.fields.size) (entry : PartitionPath.Entry) (ok : check i = .ok entry) :
      schema.fields[i].name = entry.1 :=
    encodeEntry_name encode schema.fields[i] (cells i) entry ok
  have names := encodeEntries_keys encode cells encoded
  have noExtra : entries.find? (fun entry => !schema.keys.contains entry.1) = none := by
    apply List.find?_eq_none.mpr
    intro entry member
    have included : entry.1 ∈ schema.keys := names ▸ List.mem_map_of_mem member
    simp [included]
  have readCell (i : Fin schema.fields.size) :
      TypedPartitions.decodeField decode entries schema.fields[i] = .ok (cells i) := by
    have inRange : i.val < (List.finRange schema.fields.size).length := by simp
    have inEntries : i.val < entries.length := accepted.length_eq ▸ inRange
    let entry := entries[i.val]
    have ok : check i = .ok entry := by
      simpa [List.get_eq_getElem, List.finRange, entry] using accepted.get inRange inEntries
    have seen : (schema.fields[i].name, entry.2) ∈ entries := by
      rw [nameOf i entry ok]
      exact List.getElem_mem inEntries
    exact decodeField_encodeEntry encode decode schema.fields[i] (inverse i) (cells i) entries entry ok
      ((PartitionPath.lookup_eq_some_iff unique).mpr seen)
  simp only [TypedPartitions.decode, names, keysValid, noExtra]
  exact sequenceFin_accepted schema.fields.size _ cells readCell

theorem decode_renderedEntries (options : PartitionPath.Options)
    (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (cells : Scan.Row schema.toScan Value)
    {entries : PartitionPath.Partition} {directory : String}
    (encoded : encodeEntries encode cells = .ok entries) (rendered : PartitionPath.render options entries = .ok directory) :
    TypedPartitions.decode schema decode entries = .ok cells := by
  have keysValid : PartitionPath.validateKeys (entries.map Prod.fst) = .ok () := by
    cases checked : PartitionPath.validateKeys (entries.map Prod.fst) with
    | error reason =>
      unfold PartitionPath.render at rendered
      split at rendered <;> simp [PartitionPath.validate, checked, Bind.bind, Except.bind] at rendered
    | ok accepted => cases accepted; rfl
  rw [encodeEntries_keys encode cells encoded] at keysValid
  exact decode_encodedEntries encode decode inverse cells encoded keysValid
    (PartitionPath.parse_lookup (PartitionPath.parse_render_of_ok rendered)).1

private theorem tagged_agree (options : PartitionPath.Options) (encode : Encode Value EncodeFailure)
    (rows : Scan.Table (schema.extend physical) Value) (offset : Nat)
    {classified : List (String × Scan.Row physical Value)} (checked : classify options encode rows offset = .ok classified) :
    classified = (taggedRows options encode rows).map (fun pair => (pair.1, physicalCells pair.2)) ∧
      ∀ pair ∈ taggedRows options encode rows,
        classifyRow options encode pair.2 = .ok (pair.1, physicalCells pair.2) := by
  induction rows generalizing offset classified with
  | nil =>
    cases checked
    simp [taggedRows]
  | cons row rest ih =>
    unfold classify at checked
    rw [List.zipIdx_cons, List.mapM_cons] at checked
    cases head : classifyRow options encode row with
    | error reason => simp [head, bind, Except.bind, Except.mapError] at checked
    | ok pair =>
      have payload : pair.2 = physicalCells row := by
        unfold classifyRow at head
        split at head
        · cases head
        · split at head
          · cases head
          · split at head
            · cases head
            · cases head; rfl
      have mapped : (classifyRow options encode row).mapError (Error.row offset) = .ok pair := by
        rw [head]
        rfl
      simp only [mapped, bind, Except.bind, pure, Except.pure] at checked
      have folded : ((rest.zipIdx (offset + 1)).mapM fun entry =>
          (classifyRow options encode entry.1).mapError (Error.row entry.2)) =
          classify options encode rest (offset + 1) := rfl
      rw [folded] at checked
      cases tail : classify options encode rest (offset + 1) with
      | error reason => simp [tail] at checked
      | ok more =>
        simp only [tail, Except.ok.injEq] at checked
        subst classified
        obtain ⟨restEq, admitted⟩ := ih (offset + 1) tail
        have taggedCons : taggedRows options encode (row :: rest) =
            (pair.1, row) :: taggedRows options encode rest := by
          simp [taggedRows, head, Except.toOption]
        rw [taggedCons, List.map_cons, List.cons.injEq]
        have pairEq : pair = (pair.1, physicalCells row) := Prod.ext rfl payload
        refine ⟨⟨pairEq, restEq⟩, ?_⟩
        intro candidate member
        rcases List.mem_cons.mp member with rfl | member
        · exact head.trans (congrArg Except.ok pairEq)
        · exact admitted candidate member

private theorem decode_classified (options : PartitionPath.Options) (encode : Encode Value EncodeFailure)
    (decode : Convert Value DecodeFailure) (inverse : CellLeftInverse schema encode decode)
    (keysValid : PartitionPath.validateKeys schema.keys = .ok ())
    {row : Scan.Row (schema.extend physical) Value} {directory : String}
    (admitted : classifyRow options encode row = .ok (directory, physicalCells row)) :
    decodeDirectory schema options decode directory = .ok (partitionCells row) := by
  unfold classifyRow at admitted
  cases encoded : encodeEntries encode (partitionCells row) with
  | error reason => simp [encoded] at admitted
  | ok entries =>
    cases rendered : PartitionPath.render options entries with
    | error reason => simp [encoded, rendered] at admitted
    | ok path =>
      have parsed := PartitionPath.parse_render_of_ok rendered
      simp only [encoded, rendered, parsed, Except.ok.injEq, Prod.mk.injEq, and_true] at admitted
      subst directory
      simp only [decodeDirectory, parsed, decode_encodedEntries encode decode inverse _ encoded keysValid
        (PartitionPath.parse_lookup parsed).1, Except.mapError]

private theorem extend_split (row : Scan.Row (schema.extend physical) Value) :
    extendRow (physicalCells row) (partitionCells row) = row := by
  funext i
  exact Fin.addCases (fun left => by simp [extendRow, physicalCells])
    (fun right => by simp [extendRow, partitionCells]) i

theorem restore_plan_eq_groupedRows (options : PartitionPath.Options)
    (encode : Encode Value EncodeFailure) (decode : Convert Value DecodeFailure)
    (inverse : CellLeftInverse schema encode decode)
    (rows : Scan.Table (schema.extend physical) Value) (buckets : List (Bucket physical Value))
    (planned : plan physical schema options encode rows = .ok buckets) :
    restore physical schema options decode buckets = .ok (groupOriginalRows options encode rows) := by
  rw [plan_eq_reference] at planned
  unfold reference at planned
  cases schemaOk : TypedPartitions.checkSchema (Failure := EncodeFailure) physical schema with
  | error reason => simp [schemaOk] at planned
  | ok checked =>
    cases checked
    have keys : PartitionPath.validateKeys schema.keys = .ok () := by
      cases valid : PartitionPath.validateKeys schema.keys with
      | error reason => simp [TypedPartitions.checkSchema, valid, Except.mapError, bind, Except.bind] at schemaOk
      | ok accepted => cases accepted; rfl
    have decodeSchema : TypedPartitions.checkSchema (Failure := DecodeFailure) physical schema = .ok () := by
      cases collision : schema.keys.find? (List.ofFn fun i => (physical.kind i).1).contains with
      | none => simp [TypedPartitions.checkSchema, keys, collision, Except.mapError, bind, Except.bind]
      | some name =>
        simp [TypedPartitions.checkSchema, keys, collision, Except.mapError, bind, Except.bind] at schemaOk
    cases classifiedOk : classify options encode rows with
    | error reason => simp [schemaOk, classifiedOk, Except.map] at planned
    | ok classified =>
      simp only [schemaOk, classifiedOk, Except.map, Except.ok.injEq] at planned
      subst buckets
      obtain ⟨classifiedEq, admitted⟩ := tagged_agree options encode rows 0 classifiedOk
      let tagged := taggedRows options encode rows
      have bound (pair : String × Scan.Row (schema.extend physical) Value) (member : pair ∈ tagged) :
          decodeDirectory schema options decode pair.1 = .ok (partitionCells pair.2) :=
        decode_classified options encode decode inverse keys (admitted pair member)
      rw [classifiedEq]
      unfold restore groupOriginalRows referenceGroups
      simp only [decodeSchema, List.map_map, List.filter_map, Function.comp_def]
      let build (directory : String) : Bucket physical Value :=
        ⟨directory, (tagged.filter (fun pair => pair.1 == directory)).map (physicalCells ∘ Prod.snd)⟩
      let read (bucket : Bucket physical Value) : Except (RestoreError DecodeFailure)
          (TypedPartitions.TypedPartition physical schema Value) :=
        (decodeDirectory schema options decode bucket.directory).map (fun cells => ⟨cells, bucket.rows⟩)
      have groups (directories : List String) (present : ∀ d ∈ directories, d ∈ tagged.map Prod.fst) :
          ((directories.map build).mapM read).map TypedPartitions.materialize =
            .ok (directories.flatMap fun d => (tagged.filter (fun pair => pair.1 == d)).map Prod.snd) := by
        induction directories with
        | nil => rfl
        | cons dir rest ih =>
          obtain ⟨pair, member, dirEq⟩ := List.mem_map.mp (present dir (by simp))
          let cells := partitionCells pair.2
          have decoded : decodeDirectory schema options decode dir = .ok cells := dirEq ▸ bound pair member
          have stable :
              ({ cells, rows := (build dir).rows } : TypedPartitions.TypedPartition physical schema Value).materialize =
                (tagged.filter (fun p => p.1 == dir)).map Prod.snd := by
            simp only [TypedPartitions.TypedPartition.materialize, build, List.map_map, Function.comp_def]
            apply List.map_congr_left
            intro other included
            have otherDir : other.1 = dir := beq_iff_eq.mp (List.mem_filter.mp included).2
            have same : partitionCells other.2 = cells :=
              Except.ok.inj ((otherDir ▸ bound other (List.mem_filter.mp included).1).symm.trans decoded)
            rw [← same, extend_split]
          have tail := ih (fun d member => present d (List.mem_cons_of_mem _ member))
          have first : read (build dir) = .ok ⟨cells, (build dir).rows⟩ := by
            simp only [read, build, decoded, Except.map]
          rw [List.map_cons, List.mapM_cons, first]
          cases remaining : (rest.map build).mapM read with
          | error reason =>
            rw [remaining] at tail
            cases tail
          | ok partitions =>
            rw [remaining] at tail
            have tailRows := Except.ok.inj tail
            change Except.ok (({ cells, rows := (build dir).rows } : TypedPartitions.TypedPartition physical schema Value).materialize
              ++ TypedPartitions.materialize partitions) = _
            rw [stable, tailRows]; rfl
      exact groups _ (fun _ member => List.mem_eraseDups.mp member)

end Silmaril.Proofs.Formats.Hive.WritePlan
