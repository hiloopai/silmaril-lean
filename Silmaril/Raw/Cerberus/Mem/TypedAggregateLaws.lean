module

public import Silmaril.Cerberus.Mem.TypedLaws.Defs

/-! Typed pointer copies, aggregate reconstruction and read footprints.
References are to concrete impl_mem.ml at b3e11ea3. -/

@[expose] public section
namespace Silmaril.Cerberus.Mem.Concrete

/-- Removing another address preserves the pointer-copy map lookup. -/
theorem pointer_lookup_erase_other (xs : Map Int (Option Int × Nat))
    (a b : Int) (h : a ≠ b) : (xs.erase b).lookup a = xs.lookup a := by
  exact Finmap.lookup_erase_ne h

/-- Disjoint writes preserve complete pointer-copy entries, including offsets. -/
theorem pointer_find_disjoint (s : State) (a b : Int) (bs : Representation)
    (h : a < b ∨ b + bs.length ≤ a) :
    (writeRepresentation b bs s).pointerBytes.lookup a = s.pointerBytes.lookup a := by
  induction bs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      have ne : a ≠ b := by simp only [List.length_cons] at h; omega
      have ht : a < b+1 ∨ b+1+xs.length ≤ a := by simp only [List.length_cons] at h; omega
      rcases x with ⟨byte, prov⟩
      cases prov with
      | none =>
          simp only [writeRepresentation]
          rw [pointer_lookup_erase_other _ a b ne, ih (b+1) ht]
      | some pr =>
          simp only [writeRepresentation]
          rw [Map.lookup_insert_of_key_ne (x := b) (x' := a) pr _ ne, ih (b+1) ht]

/-- Every supplied copy entry replaces the binding at its address. -/
theorem pointer_find_write (s : State) (a : Int) (bs : Representation) (i : Nat)
    (h : i < bs.length) :
    (writeRepresentation a bs s).pointerBytes.lookup (a+i) = bs[i].2 := by
  induction bs generalizing a i with
  | nil => simp at h
  | cons x xs ih =>
      rcases x with ⟨byte, prov⟩
      cases i with
      | zero =>
          cases prov with
          | none =>
              change Finmap.lookup (a+(0 : Nat)) (Finmap.erase a (writeRepresentation (a+1) xs s).pointerBytes) = none
              rw [show a+(0 : Nat) = a by omega]
              exact Finmap.lookup_erase _ _
          | some pr =>
              change Finmap.lookup (a+(0 : Nat)) (Finmap.insert a pr (writeRepresentation (a+1) xs s).pointerBytes) = some pr
              rw [show a+(0 : Nat) = a by omega]
              exact Finmap.lookup_insert _
      | succ i =>
          have ht : i < xs.length := by simp only [List.length_cons] at h; omega
          have ne : a + (i+1 : Nat) ≠ a := by omega
          have shift : a + (i+1 : Nat) = (a+1)+i := by omega
          cases prov with
          | none =>
              simp only [writeRepresentation]
              rw [pointer_lookup_erase_other _ _ _ ne, shift]
              exact ih (a+1) i ht
          | some pr =>
              simp only [writeRepresentation]
              rw [Map.lookup_insert_of_key_ne (x := a) (x' := a+(i+1 : Nat)) pr _ ne, shift]
              exact ih (a+1) i ht

/-- Plain bytes erase all copy metadata on their footprint. -/
theorem plain_pointer_none (s : State) (a : Int) (bs : List Byte) (i : Nat)
    (h : i < bs.length) :
    (writeRepresentation a (plainBytes bs) s).pointerBytes.lookup (a+i) = none := by
  have write := pointer_find_write s a (plainBytes bs) i (by simpa [plainBytes] using h)
  simpa [plainBytes] using write

/-- Pointer-copy offsets survive a complete eight-byte write. -/
theorem pointer_copy_lookup (s : State) (a n : Int) (id : Option Int) (i : Nat)
    (h : i < 8) :
    (writeRepresentation a ((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j)))) s).pointerBytes.lookup (a+i) = some (id,i) := by
  have length : (((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j))))).length = 8 := by
    simp [encodeInteger_length]
  have hw := pointer_find_write s a ((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j)))) i (by omega)
  simpa [List.getElem_zipIdx] using hw

/-- Non-function references recover the copied allocation ID independently of
old metadata. Numeric zero is excluded because it abstracts to null. -/
theorem abstractPointer_copy (s : State) (a n : Int) (id : Option Int) (refTy : Ctype)
    (nonzero : n ≠ 0)
    (objectRef : (match refTy with | .mk _ (.function ..) => false | _ => true) = true) :
    abstractPointer (writeRepresentation a
      ((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j)))) s) refTy a n =
      .ok (match id with | some id => .allocated id n | none => .unprovenanced n) := by
  let written := writeRepresentation a ((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j)))) s
  have first : written.pointerBytes.lookup a = some (id,0) := by
    simpa [written] using pointer_copy_lookup s a n id 0 (by omega)
  have intact : (List.range 8).all (fun i =>
      written.pointerBytes.lookup (a+i) == some (id,i)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    simp only [List.mem_range] at hi
    simp [written, pointer_copy_lookup s a n id i hi]
  rcases refTy with ⟨ann, kind⟩
  cases kind <;> simp_all [abstractPointer, written, Pure.pure, Except.pure] <;> rfl

/-- Numeric pointer representation roundtrips at all eight bytes. -/
theorem pointer_numeric_roundtrip (s : State) (a n : Int) (id : Option Int)
    (range : 0 ≤ n ∧ n < 18446744073709551616) :
    decodeInteger (fetchBytes 8 a (writeRepresentation a
      ((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j)))) s).bytes) = some n := by
  rw [writeRepresentation_bytes]
  have bytes : (((encodeInteger 8 n).zipIdx.map (fun (b,j) => (b, some (id,j)))).map Prod.fst) = encodeInteger 8 n := by
    simp [List.map_map, Function.comp_def]
  rw [bytes]
  have fetch := fetch_write a (encodeInteger 8 n) s.bytes
  rw [encodeInteger_length] at fetch
  rw [fetch, decode_encode]
  congr 1
  apply Int.emod_eq_of_lt range.1
  norm_num
  exact range.2

/-- Object and function-pointer abstraction preserves copy metadata and registry
lookup when a write's address range is disjoint. impl_mem.ml:807-877. -/
theorem abstractPointer_disjoint (s : State) (refTy : Ctype) (a n b : Int) (bs : Representation)
    (h : a+8 ≤ b ∨ b+bs.length ≤ a) :
    abstractPointer (writeRepresentation b bs s) refTy a n = abstractPointer s refTy a n := by
  have first := pointer_find_disjoint s a b bs (by omega)
  have every (i : Nat) (hi : i < 8) := pointer_find_disjoint s (a+i) b bs (by omega)
  have allEq' (id : Option Int) : (List.range 8).all (fun i =>
      (writeRepresentation b bs s).pointerBytes.lookup (a+i) == some (id,i)) =
      (List.range 8).all (fun i => s.pointerBytes.lookup (a+i) == some (id,i)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro hx i hi <;>
      have e := every i (List.mem_range.mp hi) <;> simpa [e] using hx i hi
  have anyEq : (List.range 8).any (fun i =>
      ((writeRepresentation b bs s).pointerBytes.lookup (a+i)).any (·.1.isSome)) =
      (List.range 8).any (fun i => (s.pointerBytes.lookup (a+i)).any (·.1.isSome)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨i, hi, yes⟩
      exact ⟨i, hi, by simpa [every i (List.mem_range.mp hi)] using yes⟩
    · rintro ⟨i, hi, yes⟩
      exact ⟨i, hi, by simpa [every i (List.mem_range.mp hi)] using yes⟩
  have registry := (writeRepresentation_allocations b bs s).2.2
  have allocs := (writeRepresentation_allocations b bs s).1
  have dead := (writeRepresentation_allocations b bs s).2.1
  rcases refTy with ⟨ann, kind⟩
  cases kind <;> simp only [abstractPointer, first, registry, anyEq, allocs, dead]
  all_goals split <;> try rfl
  all_goals cases s.pointerBytes.lookup a <;> simp only
  all_goals rw [allEq']

/-- The last-used allocation is administrative, not part of pointer abstraction. -/
theorem abstractPointer_lastUsed (s : State) (used : Option Int) (ty : Ctype) (a n : Int) :
    abstractPointer {s with lastUsed := used} ty a n = abstractPointer s ty a n := by
  simp only [abstractPointer]

def copiedPointer (id : Option Int) (n : Int) : Pointer :=
  match id with | some id => .allocated id n | none => .unprovenanced n

/-- Typed store/load preserves all eight numeric bytes and the copied provenance.
The referent may be any non-function type, including aggregates. -/
theorem typed_pointer_load_after_store (tags : Tags) (s s' : State) (ann : List Annot)
    (quals : Qualifiers) (refTy : Ctype) (p : Pointer) (id : Option Int) (n : Int) (fp : Int × Int)
    (range : 0 < n ∧ n < 18446744073709551616)
    (objectRef : (match refTy with | .mk _ (.function ..) => false | _ => true) = true)
    (written : storeTyped tags s (.mk ann (.pointer quals refTy)) p
      (.pointer refTy (copiedPointer id n)) = .ok (fp,s')) :
    ∃ finish, loadTyped tags s' (.mk ann (.pointer quals refTy)) p =
      .ok (.pointer refTy (copiedPointer id n),finish) := by
  let bs := (encodeInteger 8 n).zipIdx.map (fun (b,i) => (b, some (id,i)))
  have hr : represent 64 tags (.pointer refTy (copiedPointer id n)) s = .ok (bs,s) := by
    cases id <;> simp [copiedPointer, represent, representPointer, encodeAddress, bs, range.2, show 0 ≤ n by omega, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases h : accessTyped tags s (.mk ann (.pointer quals refTy)) p with
  | error e => simp [storeTyped, h, Bind.bind, Except.bind] at written
  | ok pair =>
      rcases pair with ⟨ident,addr,size⟩
      cases hw : checkWritable s ident with
      | error e => simp [storeTyped, h, hw, Bind.bind, Except.bind] at written
      | ok result =>
          simp only [storeTyped, h, hw, hr, Bind.bind, Except.bind, Pure.pure] at written
          split at written
          · simp at written
          · cases Except.ok.inj written
            have numeric := pointer_numeric_roundtrip s addr n id (by omega)
            have pointer := abstractPointer_copy s addr n id refTy (by omega) objectRef
            simp [copiedPointer, loadTyped, typed_access_write, h, abstractValue, typeLayout, bs,
              numeric, pointer, abstractPointer_lastUsed, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Geometry of the reads used by typed abstraction. Aggregate constructors
require disjointness of every actual member, rather than assuming that padding
or a flexible array is read. Layout results are the runner's fixed-depth results. -/
inductive DisjointReads (tags : Tags) (b : Int) (width : Nat) : Nat → Ctype → Int → Prop where
  | zero (ty a) : DisjointReads tags b width 0 ty a
  | integer (fuel ann ity a l)
      (layout : typeLayout 64 tags (.mk ann (.basic (.integer ity))) = .ok l)
      (apart : a+l.size.toNat ≤ b ∨ b+width ≤ a) :
      DisjointReads tags b width (fuel+1) (.mk ann (.basic (.integer ity))) a
  | pointer (fuel ann quals refTy a)
      (apart : a+8 ≤ b ∨ b+width ≤ a) :
      DisjointReads tags b width (fuel+1) (.mk ann (.pointer quals refTy)) a
  | array (fuel ann elem count a l e)
      (layout : typeLayout 64 tags (.mk ann (.array elem (some count))) = .ok l)
      (element : typeLayout 64 tags elem = .ok e)
      (members : ∀ i ∈ List.range count.toNat,
        DisjointReads tags b width fuel elem (a+(i : Int)*e.size)) :
      DisjointReads tags b width (fuel+1) (.mk ann (.array elem (some count))) a
  | struct_ (fuel ann sym a l)
      (layout : typeLayout 64 tags (.mk ann (.struct sym)) = .ok l)
      (members : ∀ m ∈ l.members, DisjointReads tags b width fuel m.2.1 (a+m.2.2)) :
      DisjointReads tags b width (fuel+1) (.mk ann (.struct sym)) a
  | atomic (fuel ann ty a l)
      (layout : typeLayout 64 tags (.mk ann (.atomic ty)) = .ok l)
      (member : DisjointReads tags b width fuel ty a) :
      DisjointReads tags b width (fuel+1) (.mk ann (.atomic ty)) a

/-- Pointwise equality on members is sufficient for ordered monadic abstraction. -/
theorem mapM_on_members {α β : Type} (xs : List α) (f g : α → Except Failure β)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons]
      rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

/-- Typed abstraction is unchanged by disjoint representation writes, including
nested aggregates, pointer-copy offsets and function-registry lookups. -/
theorem typed_abstraction_disjoint (tags : Tags) (s : State) (ty : Ctype)
    (a b : Int) (bs : Representation) (fuel : Nat)
    (shape : DisjointReads tags b bs.length fuel ty a) :
    abstractValue fuel tags (writeRepresentation b bs s) ty a = abstractValue fuel tags s ty a := by
  induction shape with
  | zero => rfl
  | integer fuel ann ity a l layout apart =>
      simp only [abstractValue, layout, Bind.bind, Except.bind]
      rw [typed_write_disjoint _ _ _ _ _ apart]
  | pointer fuel ann quals refTy a apart =>
      simp only [abstractValue, typeLayout, Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [typed_write_disjoint _ _ _ _ _ apart]
      cases decodeInteger (fetchBytes 8 a s.bytes) with
      | none => rfl
      | some n => simp only; rw [abstractPointer_disjoint s refTy a n b bs apart]
  | array fuel ann elem count a l e layout element members ih =>
      simp only [abstractValue, layout, element, Bind.bind, Except.bind]
      rw [mapM_on_members _ _ _ ih]
  | struct_ fuel ann sym a l layout members ih =>
      simp only [abstractValue, layout, Bind.bind, Except.bind]
      have same := mapM_on_members l.members
        (fun m => do pure (m.1,m.2.1, ← abstractValue fuel tags (writeRepresentation b bs s) m.2.1 (a+m.2.2)))
        (fun m => do pure (m.1,m.2.1, ← abstractValue fuel tags s m.2.1 (a+m.2.2))) (by
          intro m hm
          rw [ih m hm])
      simp only [Bind.bind, Except.bind] at same
      rw [same]
  | atomic fuel ann ty a l layout member ih =>
      simpa only [abstractValue, layout, Bind.bind, Except.bind] using ih

/-- The reverse byte-map fold writes a suffix before the pre. -/
theorem writeRepresentation_append (s : State) (a : Int) (xs ys : Representation) :
    writeRepresentation a (xs ++ ys) s =
      writeRepresentation a xs (writeRepresentation (a+xs.length) ys s) := by
  induction xs generalizing a with
  | nil => simp [writeRepresentation]
  | cons x xs ih =>
      have shift : a + ((x::xs).length : Int) = (a+1)+xs.length := by simp; omega
      simp only [List.cons_append, writeRepresentation, ih, shift]

/-- A member's universally valid representation survives a disjoint pre.
The suffix is arbitrary prior memory. Registry assumptions remain explicit,
because registry keys are numeric symbol IDs rather than object addresses. -/
theorem representation_member_roundtrip (tags : Tags) (s : State) (ty : Ctype) (v : MemoryValue)
    (a : Int) (pre payload suffix : Representation) (fuel : Nat)
    (apart : DisjointReads tags a pre.length fuel ty (a+pre.length))
    (leaf : ∀ prior addr, prior.functions = s.functions →
      abstractValue fuel tags (writeRepresentation addr payload prior) ty addr = .ok v) :
    abstractValue fuel tags (writeRepresentation a (pre ++ payload ++ suffix) s)
      ty (a+pre.length) = .ok v := by
  rw [List.append_assoc, writeRepresentation_append, typed_abstraction_disjoint _ _ _ _ _ _ _ apart,
    writeRepresentation_append]
  apply leaf
  exact (writeRepresentation_allocations _ _ _).2.2

/-- Array reconstruction is compositional over every element representation.
The hypotheses describe byte splits, element footprints and the registry;
they do not assume successful abstraction of the aggregate. -/
theorem array_representation_roundtrip (tags : Tags) (s : State) (ann : List Annot)
    (elem : Ctype) (count a : Int) (l e : TypeLayout) (bs : Representation)
    (fuel : Nat) (values : Nat → MemoryValue)
    (layout : typeLayout 64 tags (.mk ann (.array elem (some count))) = .ok l)
    (element : typeLayout 64 tags elem = .ok e)
    (members : ∀ i ∈ List.range count.toNat, ∃ pre payload suffix,
      bs = pre ++ payload ++ suffix ∧ (pre.length : Int) = (i : Int)*e.size ∧
      DisjointReads tags a pre.length fuel elem (a+pre.length) ∧
      ∀ prior addr, prior.functions = s.functions →
        abstractValue fuel tags (writeRepresentation addr payload prior) elem addr = .ok (values i)) :
    abstractValue (fuel+1) tags (writeRepresentation a bs s) (.mk ann (.array elem (some count))) a =
      .ok (.array ((List.range count.toNat).map values)) := by
  simp only [abstractValue, layout, element, Bind.bind, Except.bind]
  have each : ∀ i ∈ List.range count.toNat,
      abstractValue fuel tags (writeRepresentation a bs s) elem (a+(i : Int)*e.size) = .ok (values i) := by
    intro i hi
    obtain ⟨pre,payload,suffix,hbs,offset,apart,leaf⟩ := members i hi
    rw [hbs, ← offset]
    exact representation_member_roundtrip tags s elem (values i) a pre payload suffix fuel apart leaf
  rw [mapM_on_members _ _ (fun i => .ok (values i)) each]
  have mappedPure := List.mapM_pure (m := Except Failure) (l := List.range count.toNat) (f := values)
  simp only [Pure.pure, Except.pure] at mappedPure
  rw [mappedPure]
  rfl

/-- Struct reconstruction reads precisely the listed member payloads, skipping
padding. Members may themselves be pointers, arrays or structs. -/
theorem struct_representation_roundtrip (tags : Tags) (s : State) (ann : List Annot)
    (sym : Sym) (a : Int) (l : TypeLayout) (bs : Representation) (fuel : Nat)
    (values : Identifier × Ctype × Int → MemoryValue)
    (layout : typeLayout 64 tags (.mk ann (.struct sym)) = .ok l)
    (members : ∀ m ∈ l.members, ∃ pre payload suffix,
      bs = pre ++ payload ++ suffix ∧ (pre.length : Int) = m.2.2 ∧
      DisjointReads tags a pre.length fuel m.2.1 (a+pre.length) ∧
      ∀ prior addr, prior.functions = s.functions →
        abstractValue fuel tags (writeRepresentation addr payload prior) m.2.1 addr = .ok (values m)) :
    abstractValue (fuel+1) tags (writeRepresentation a bs s) (.mk ann (.struct sym)) a =
      .ok (.struct_ sym (l.members.map (fun m => (m.1,m.2.1,values m)))) := by
  simp only [abstractValue, layout, Bind.bind, Except.bind]
  have each : ∀ m ∈ l.members, abstractValue fuel tags (writeRepresentation a bs s) m.2.1 (a+m.2.2) = .ok (values m) := by
    intro m hm
    obtain ⟨pre,payload,suffix,hbs,offset,apart,leaf⟩ := members m hm
    rw [hbs, ← offset]
    exact representation_member_roundtrip tags s m.2.1 (values m) a pre payload suffix fuel apart leaf
  have mapped := mapM_on_members l.members
    (fun m => do pure (m.1,m.2.1, ← abstractValue fuel tags (writeRepresentation a bs s) m.2.1 (a+m.2.2)))
    (fun m => .ok (m.1,m.2.1,values m)) (by intro m hm; rw [each m hm]; rfl)
  simp only [Bind.bind, Except.bind] at mapped
  rw [mapped]
  have mappedPure := List.mapM_pure (m := Except Failure) (l := l.members) (f := fun m => (m.1,m.2.1,values m))
  simp only [Pure.pure, Except.pure] at mappedPure
  rw [mappedPure]
  rfl

/-- Representation writes commute with administrative last-used updates. -/
theorem writeRepresentation_lastUsed (s : State) (a : Int) (bs : Representation) (used : Option Int) :
    {writeRepresentation a bs s with lastUsed := used} =
      writeRepresentation a bs {s with lastUsed := used} := by
  induction bs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | mk byte prov => cases prov <;> simp [writeRepresentation, ← ih]

/-- A successful monadic fold preserves any invariant preserved by its step. -/
theorem foldlM_preserves {α β : Type} (xs : List α) (step : β → α → Except Failure β)
    (initial final : β) (inv : β → Prop) (start : inv initial)
    (next : ∀ acc x finish, inv acc → step acc x = .ok finish → inv finish)
    (run : xs.foldlM step initial = .ok final) : inv final := by
  induction xs generalizing initial with
  | nil =>
      simp only [List.foldlM_nil, Pure.pure, Except.pure] at run
      cases Except.ok.inj run
      exact start
  | cons x xs ih =>
      cases h : step initial x with
      | error e => simp [List.foldlM_cons, h, Bind.bind, Except.bind] at run
      | ok middle =>
          simp only [List.foldlM_cons, h, Bind.bind, Except.bind] at run
          exact ih middle (next initial x middle start h) run

/-- Function registration changes neither allocation nor lifetime checks. -/
theorem registerFunction_checks (s : State) (sym : Sym) :
    (registerFunction s sym).allocations = s.allocations ∧ (registerFunction s sym).dead = s.dead := by
  rcases sym with ⟨digest,n,desc⟩
  cases desc <;> exact ⟨rfl,rfl⟩

/-- Encoding bytes with a fixed resulting state leaves that state unchanged. -/
theorem encode_state {α : Type} (encoded : Except Failure α) (bytes : α → Representation)
    (s finish : State) (bs : Representation)
    (run : (do let x ← encoded; pure (bytes x,s)) = .ok (bs,finish)) : finish = s := by
  cases encoded with
  | error e => simp [Bind.bind, Except.bind] at run
  | ok value =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      exact (congrArg Prod.snd (Except.ok.inj run)).symm

/-- Pointer representation preserves allocation and lifetime checks. -/
theorem represent_pointer_checks (p : Pointer) (s finish : State) (bs : Representation)
    (run : representPointer p s = .ok (bs,finish)) :
    finish.allocations = s.allocations ∧ finish.dead = s.dead := by
  cases p with
  | null t =>
      simp only [representPointer, Pure.pure, Except.pure] at run
      cases Except.ok.inj run
      exact ⟨rfl,rfl⟩
  | allocated id n | unprovenanced n =>
      cases h : encodeAddress n with
      | error e => simp [representPointer, h, Bind.bind, Except.bind] at run
      | ok bytes =>
          simp only [representPointer, h, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
          cases Except.ok.inj run
          exact ⟨rfl,rfl⟩
  | function sym =>
      rcases sym with ⟨digest,n,desc⟩
      simp only [representPointer] at run
      have eq := encode_state (encodeAddress (n : Int)) plainBytes
        (registerFunction s (.mk digest n desc)) finish bs run
      rw [eq]
      exact registerFunction_checks s (.mk digest n desc)

/-- Representation can extend the function registry, but cannot alter object
allocation or lifetime checks, including through nested aggregate folds. -/
theorem represent_preserves_checks (fuel : Nat) (tags : Tags) (v : MemoryValue) (s finish : State)
    (bs : Representation) (run : represent fuel tags v s = .ok (bs,finish)) :
    finish.allocations = s.allocations ∧ finish.dead = s.dead := by
  induction fuel generalizing v s finish bs with
  | zero => simp [represent] at run
  | succ fuel ih =>
      cases v with
      | unspecified ty =>
          cases h : typeLayout 64 tags ty with
          | error e => simp [represent, h, Bind.bind, Except.bind] at run
          | ok l =>
              simp only [represent, h, Bind.bind, Except.bind, Pure.pure] at run
              cases Except.ok.inj run
              exact ⟨rfl,rfl⟩
      | integer ty n =>
          cases h : registeredIntegerLayout tags ty with
          | none => simp [represent, h] at run
          | some pair =>
              simp only [represent, h] at run
              split at run
              · cases Except.ok.inj run
                exact ⟨rfl,rfl⟩
              · simp at run
      | floating ty x =>
          cases Except.ok.inj run
          exact ⟨rfl,rfl⟩
      | pointer ty p =>
          simp only [represent] at run
          exact represent_pointer_checks p s finish bs run
      | array values =>
          apply foldlM_preserves values _ ([],s) (bs,finish)
            (fun acc : Representation × State => acc.2.allocations = s.allocations ∧ acc.2.dead = s.dead) ⟨rfl,rfl⟩ _ run
          intro acc x next state step
          rcases acc with ⟨acc,prior⟩
          cases h : represent fuel tags x prior with
          | error e => simp [h, Bind.bind, Except.bind] at step
          | ok pair =>
              rcases pair with ⟨bytes,after⟩
              simp only [h, Bind.bind, Except.bind, Pure.pure] at step
              cases Except.ok.inj step
              exact ⟨(ih x prior after bytes h).1.trans state.1, (ih x prior after bytes h).2.trans state.2⟩
      | struct_ sym values =>
          cases ht : typeLayout 64 tags (.mk [] (.struct sym)) with
          | error e => simp [represent, ht, Bind.bind, Except.bind] at run
          | ok l =>
              simp only [represent, ht, Bind.bind, Except.bind] at run
              split at run
              · simp at run
              · split at run
                · simp at run
                · rename_i triple hf
                  rcases triple with ⟨bytes,offset,after⟩
                  simp only [Pure.pure] at run
                  cases Except.ok.inj run
                  apply foldlM_preserves (l.members.zip values) _ ([],0,s) (bytes,offset,finish)
                    (fun acc : Representation × Int × State => acc.2.2.allocations = s.allocations ∧ acc.2.2.dead = s.dead) ⟨rfl,rfl⟩ _ hf
                  intro acc item next state step
                  rcases acc with ⟨acc,offset,prior⟩
                  rcases item with ⟨⟨name,ty,off⟩,⟨name',ty',value⟩⟩
                  cases h : represent fuel tags value prior with
                  | error e => simp [h] at step
                  | ok pair =>
                      rcases pair with ⟨bytes,finish⟩
                      simp only [h, Pure.pure] at step
                      cases Except.ok.inj step
                      exact ⟨(ih value prior finish bytes h).1.trans state.1, (ih value prior finish bytes h).2.trans state.2⟩


/-- A typed aggregate load after store follows from compositional representation
roundtrip and preservation of allocation/lifetime checks. Function registration
is permitted, but each member law uses the resulting registry. -/
theorem typed_aggregate_load_after_store (tags : Tags) (s s' registered : State)
    (ty : Ctype) (p : Pointer) (v : MemoryValue) (bs : Representation) (fp : Int × Int)
    (represented : represent 64 tags v s = .ok (bs,registered))
    (roundtrip : ∀ prior addr, prior.functions = registered.functions →
      abstractValue 64 tags (writeRepresentation addr bs prior) ty addr = .ok v)
    (written : storeTyped tags s ty p v = .ok (fp,s')) :
    ∃ finish, loadTyped tags s' ty p = .ok (v,finish) := by
  have checks := represent_preserves_checks 64 tags v s registered bs represented
  cases h : accessTyped tags s ty p with
  | error e => simp [storeTyped, h, Bind.bind, Except.bind] at written
  | ok pair =>
      rcases pair with ⟨id,addr,size⟩
      cases hw : checkWritable s id with
      | error e => simp [storeTyped, h, hw, Bind.bind, Except.bind] at written
      | ok result =>
          simp only [storeTyped, h, hw, represented, Bind.bind, Except.bind, Pure.pure] at written
          split at written
          · simp at written
          · cases Except.ok.inj written
            have access : accessTyped tags registered ty p = .ok (id,addr,size) := by
              simpa only [accessTyped, checks.1, checks.2] using h
            have read := roundtrip {registered with lastUsed := some id} addr rfl
            rw [← writeRepresentation_lastUsed] at read
            simp [loadTyped, typed_access_write, access, read, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Typed array load after store reconstructs each element from its byte slice. -/
theorem typed_array_load_after_store (tags : Tags) (s s' registered : State)
    (ann : List Annot) (elem : Ctype) (count : Int) (l e : TypeLayout)
    (bs : Representation) (p : Pointer) (fp : Int × Int) (values : Nat → MemoryValue)
    (layout : typeLayout 64 tags (.mk ann (.array elem (some count))) = .ok l)
    (element : typeLayout 64 tags elem = .ok e)
    (represented : represent 64 tags (.array ((List.range count.toNat).map values)) s = .ok (bs,registered))
    (members : ∀ a i, i ∈ List.range count.toNat → ∃ pre payload suffix,
      bs = pre ++ payload ++ suffix ∧ (pre.length : Int) = (i : Int)*e.size ∧
      DisjointReads tags a pre.length 63 elem (a+pre.length) ∧
      ∀ prior addr, prior.functions = registered.functions →
        abstractValue 63 tags (writeRepresentation addr payload prior) elem addr = .ok (values i))
    (written : storeTyped tags s (.mk ann (.array elem (some count))) p
      (.array ((List.range count.toNat).map values)) = .ok (fp,s')) :
    ∃ finish, loadTyped tags s' (.mk ann (.array elem (some count))) p =
      .ok (.array ((List.range count.toNat).map values),finish) := by
  apply typed_aggregate_load_after_store tags s s' registered _ p _ bs fp represented _ written
  intro prior addr registry
  apply array_representation_roundtrip tags prior ann elem count addr l e bs 63 values layout element
  intro i hi
  obtain ⟨pre,payload,suffix,split,offset,apart,leaf⟩ := members addr i hi
  exact ⟨pre,payload,suffix,split,offset,apart,fun state a same => leaf state a (same.trans registry)⟩

/-- Typed struct load after store reconstructs layout members while skipping padding. -/
theorem typed_struct_load_after_store (tags : Tags) (s s' registered : State)
    (ann : List Annot) (sym : Sym) (l : TypeLayout) (bs : Representation)
    (p : Pointer) (fp : Int × Int) (values : Identifier × Ctype × Int → MemoryValue)
    (layout : typeLayout 64 tags (.mk ann (.struct sym)) = .ok l)
    (represented : represent 64 tags (.struct_ sym (l.members.map (fun m => (m.1,m.2.1,values m)))) s = .ok (bs,registered))
    (members : ∀ a m, m ∈ l.members → ∃ pre payload suffix,
      bs = pre ++ payload ++ suffix ∧ (pre.length : Int) = m.2.2 ∧
      DisjointReads tags a pre.length 63 m.2.1 (a+pre.length) ∧
      ∀ prior addr, prior.functions = registered.functions →
        abstractValue 63 tags (writeRepresentation addr payload prior) m.2.1 addr = .ok (values m))
    (written : storeTyped tags s (.mk ann (.struct sym)) p
      (.struct_ sym (l.members.map (fun m => (m.1,m.2.1,values m)))) = .ok (fp,s')) :
    ∃ finish, loadTyped tags s' (.mk ann (.struct sym)) p =
      .ok (.struct_ sym (l.members.map (fun m => (m.1,m.2.1,values m))),finish) := by
  apply typed_aggregate_load_after_store tags s s' registered _ p _ bs fp represented _ written
  intro prior addr registry
  apply struct_representation_roundtrip tags prior ann sym addr l bs 63 values layout
  intro m hm
  obtain ⟨pre,payload,suffix,split,offset,apart,leaf⟩ := members addr m hm
  exact ⟨pre,payload,suffix,split,offset,apart,fun state a same => leaf state a (same.trans registry)⟩

/-- Successful typed access uses exactly the requested type's layout size. -/
theorem typed_access_size (tags : Tags) (s : State) (ty : Ctype) (l : TypeLayout)
    (id addr size : Int) (layout : typeLayout 64 tags ty = .ok l)
    (access : accessTyped tags s ty (.allocated id addr) = .ok (id,addr,size)) : size = l.size := by
  simp only [accessTyped, layout, Bind.bind, Except.bind] at access
  split at access
  · simp at access
  · cases ha : s.allocations.lookup id with
    | none => simp [ha] at access
    | some allocation =>
        simp only [ha] at access
        split at access
        · cases hw : checkAtomic allocation ty addr l.size with
          | error e => simp [hw] at access
          | ok result =>
              simp only [hw] at access
              exact (congrArg (fun x : Int × Int × Int => x.2.2) (Except.ok.inj access)).symm
        · simp at access

/-- A member at its layout offset has exactly its type's footprint, contained
in its live allocation. Interior pointer and array fields use the same law. -/
theorem struct_member_footprint (tags : Tags) (s : State) (sym : Sym) (l field : TypeLayout)
    (name : Identifier) (ty : Ctype) (off base id size : Int)
    (layout : typeLayout 64 tags (.mk [] (.struct sym)) = .ok l)
    (member : (name,ty,off) ∈ l.members) (fieldLayout : typeLayout 64 tags ty = .ok field)
    (access : accessTyped tags s ty (.allocated id (base+off)) = .ok (id,base+off,size)) :
    size = field.size ∧ ∃ allocation, s.allocations.lookup id = some allocation ∧
      allocation.base ≤ base+off ∧ base+off+field.size ≤ allocation.base+allocation.size ∧
      (name,ty,off) ∈ l.members ∧ typeLayout 64 tags (.mk [] (.struct sym)) = .ok l := by
  have width := typed_access_size tags s ty field id (base+off) size fieldLayout access
  obtain ⟨allocation,live,lo,hi⟩ := typed_access_footprint tags s ty id (base+off) size access
  exact ⟨width,allocation,live,lo,by simpa [width] using hi,member,layout⟩

/-- Plain numeric bytes preserve the address even when older bytes had provenance. -/
theorem plain_numeric_roundtrip (s : State) (a n : Int)
    (range : 0 ≤ n ∧ n < 18446744073709551616) :
    decodeInteger (fetchBytes 8 a (writeRepresentation a (plainBytes (encodeInteger 8 n)) s).bytes) = some n := by
  rw [writeRepresentation_bytes]
  simp only [plainBytes, List.map_map, Function.comp_def]
  rw [List.map_id']
  have fetch := fetch_write a (encodeInteger 8 n) s.bytes
  rw [encodeInteger_length] at fetch
  rw [fetch, decode_encode]
  congr 1
  apply Int.emod_eq_of_lt range.1
  norm_num
  exact range.2

/-- Null storage abstracts to null at its declared referent type. -/
theorem typed_null_load_after_store (tags : Tags) (s s' : State) (ann : List Annot)
    (quals : Qualifiers) (refTy : Ctype) (p : Pointer) (fp : Int × Int)
    (written : storeTyped tags s (.mk ann (.pointer quals refTy)) p (.pointer refTy (.null refTy)) = .ok (fp,s')) :
    ∃ finish, loadTyped tags s' (.mk ann (.pointer quals refTy)) p = .ok (.pointer refTy (.null refTy),finish) := by
  apply typed_aggregate_load_after_store tags s s' s _ p _ (plainBytes (encodeInteger 8 0)) fp
    (by simp [represent, representPointer, Pure.pure, Except.pure]) _ written
  intro prior addr registry
  have numeric := plain_numeric_roundtrip prior addr 0 (by norm_num)
  simp [abstractValue, typeLayout, numeric, abstractPointer, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Plain function bytes erase allocation provenance before consulting the
registry. Numeric IDs must be nonzero because zero abstracts to null. -/
theorem function_pointer_abstraction (s : State) (a n : Int) (sym : Sym)
    (ann : List Annot) (ret : Qualifiers × Ctype)
    (params : List (Qualifiers × Ctype × Bool)) (variadic : Bool)
    (nonzero : n ≠ 0)
    (registry : s.functions.lookup n = some sym) :
    abstractPointer (writeRepresentation a (plainBytes (encodeInteger 8 n)) s)
      (.mk ann (.function ret params variadic)) a n = .ok (.function sym) := by
  have clean : (List.range 8).any (fun i =>
      ((writeRepresentation a (plainBytes (encodeInteger 8 n)) s).pointerBytes.lookup (a+i)).any (·.1.isSome)) = false := by
    apply List.any_eq_false.mpr
    intro i hi bad
    have cleared := plain_pointer_none s a (encodeInteger 8 n) i (by simpa [encodeInteger_length] using hi)
    simp [cleared] at bad
  have functions := (writeRepresentation_allocations a (plainBytes (encodeInteger 8 n)) s).2.2
  simp [abstractPointer, nonzero, clean, functions, registry, Pure.pure, Except.pure]

/-- Successful byte encoding returns its bytes with the supplied state. -/
theorem encode_bytes {α : Type} (encoded : Except Failure α) (value : α)
    (bytes : α → Representation) (s : State) (success : encoded = .ok value) :
    (do let x ← encoded; pure (bytes x,s)) = .ok (bytes value,s) := by
  rw [success]
  rfl

/-- Named function representation installs the symbol after address encoding. -/
theorem represent_named_function (fuel : Nat) (tags : Tags) (refTy : Ctype)
    (s : State) (digest : Digest) (name : String) (n : Nat)
    (encoded : encodeAddress (n : Int) = .ok (encodeInteger 8 n)) :
    represent (fuel+1) tags (.pointer refTy (.function (.mk digest n (.id name)))) s =
      .ok (plainBytes (encodeInteger 8 n), {s with functions := s.functions.insert n (.mk digest n (.id name))}) := by
  rw [represent]
  exact encode_bytes (encodeAddress (n : Int)) (encodeInteger 8 n) plainBytes
    (registerFunction s (.mk digest n (.id name))) encoded

/-- Pointer-typed abstraction combines numeric decoding with provenance recovery. -/
theorem pointer_value_abstraction (tags : Tags) (s : State) (ann : List Annot)
    (quals : Qualifiers) (refTy : Ctype) (a n : Int) (p : Pointer)
    (numeric : decodeInteger (fetchBytes 8 a s.bytes) = some n)
    (pointer : abstractPointer s refTy a n = .ok p) :
    abstractValue 64 tags s (.mk ann (.pointer quals refTy)) a = .ok (.pointer refTy p) := by
  simp only [abstractValue, typeLayout, numeric, pointer, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Typed function pointer load after store uses its newly registered named symbol. -/
theorem typed_function_load_after_store (tags : Tags) (s s' : State) (ann refAnn : List Annot)
    (quals : Qualifiers) (ret : Qualifiers × Ctype)
    (params : List (Qualifiers × Ctype × Bool)) (variadic : Bool)
    (digest : Digest) (name : String) (n : Nat) (p : Pointer) (fp : Int × Int)
    (range : 0 < n ∧ (n : Int) < 18446744073709551616)
    (written : storeTyped tags s (.mk ann (.pointer quals (.mk refAnn (.function ret params variadic)))) p
      (.pointer (.mk refAnn (.function ret params variadic)) (.function (.mk digest n (.id name)))) = .ok (fp,s')) :
    ∃ finish, loadTyped tags s' (.mk ann (.pointer quals (.mk refAnn (.function ret params variadic)))) p =
      .ok (.pointer (.mk refAnn (.function ret params variadic)) (.function (.mk digest n (.id name))),finish) := by
  have encoded : encodeAddress (n : Int) = .ok (encodeInteger 8 n) := by
    unfold encodeAddress
    rw [ite_eq_left (show 0 ≤ (n : Int) ∧ (n : Int) < 18446744073709551616 by omega)]
  let registered := {s with functions := s.functions.insert n (.mk digest n (.id name))}
  apply typed_aggregate_load_after_store tags s s' registered _ p _ (plainBytes (encodeInteger 8 n)) fp
    (represent_named_function 63 tags _ s digest name n encoded) _ written
  intro prior addr registry
  have numeric := plain_numeric_roundtrip prior addr n (by omega)
  have lookup : prior.functions.lookup (n : Int) = some (.mk digest n (.id name)) := by
    rw [registry]
    simp [registered]
  have pointer := function_pointer_abstraction prior addr n (.mk digest n (.id name)) refAnn ret params variadic (by omega) lookup
  exact pointer_value_abstraction tags _ ann quals _ addr n _ numeric pointer

/-- The next aligned member starts after the preceding member's footprint. -/
theorem roundUp_footprint (offset align : Int) (positive : 0 < align) : offset ≤ roundUp offset align := by
  unfold roundUp
  split
  · omega
  · have rem := Int.emod_lt_of_pos offset positive
    omega

/-- Adjacent member writes do not alter the preceding member's bytes, including
when alignment inserts padding. This is the offset calculation used by layout. -/
theorem struct_adjacent_disjoint (s : State) (base offset align : Int) (w : Nat) (bs : Representation)
    (positive : 0 < align) :
    fetchBytes w (base+offset) (writeRepresentation (base+roundUp (offset+w) align) bs s).bytes =
      fetchBytes w (base+offset) s.bytes := by
  apply typed_write_disjoint
  have bound := roundUp_footprint (offset+w) align positive
  left
  omega

end Silmaril.Cerberus.Mem.Concrete
