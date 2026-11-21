module

public import Silmaril.Crypto.Blake3.Range.Extension.Defs
public import Silmaril.Crypto.Blake3.Range.EOF.Thms
public import Silmaril.Semantics.Naming.ByteRange.Extension.Thms

public section

namespace Silmaril.Proofs.Crypto.Blake3.Range.Extension

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming
open Silmaril.Semantics.Naming.ByteRange (Fact Observations)

theorem same_input {rel : Compression} (free : ¬ Compression.Collision rel)
    {left right : Input} {output : CV} (lhs : rel left output) (rhs : rel right output) : left = right := by
  by_contra ne
  exact free ⟨left, right, output, ne, lhs, rhs⟩

private theorem chain_mono {base rel : Compression} (extendsRel : base.Extends rel)
    {root first : Bool} {chunk more : Nat} {cv output : CV} {bytes : Bytes}
    (chain : Chain base root chunk more first cv bytes output) : Chain rel root chunk more first cv bytes output := by
  induction chain with
  | last bound hit => exact .last bound (extendsRel hit)
  | step bound hit _ ih => exact .step bound (extendsRel hit) ih

theorem trace_mono {base rel : Compression} (extendsRel : base.Extends rel)
    {root : Bool} {shape : Shape} {opening : Opening} {output : CV}
    (trace : Trace base root shape opening output) : Trace rel root shape opening output := by
  induction trace with
  | «opaque» => exact .opaque ..
  | leaf ok chain => exact .leaf ok (chain_mono extendsRel chain)
  | fork _ _ hit left right => exact .fork left right (extendsRel hit)

theorem named_mono {base rel : Compression} (extendsRel : base.Extends rel) : Subset (Named base) (Named rel) := by
  rintro _ _ ⟨valid, output, trace, eq⟩
  exact ⟨valid, output, trace_mono extendsRel trace, eq⟩

theorem named_binding {rel : Compression} (free : ¬ Compression.Collision rel) : Binding (Named rel) :=
  fun {_ _ _} left right => (Named.eqOrCollision left right).resolve_right free

theorem named_unique {rel : Compression} (canonical : Compression.Canonical rel) : UniqueNames (Named rel) := by
  rintro _ _ _ ⟨_, lcv, lhs, leq⟩ ⟨_, rcv, rhs, req⟩
  exact leq.symm.trans ((congrArg digestBytes (lhs.canonical canonical rhs)).trans req)

theorem realizes_model {base rel : Compression} {seen : Observations Bytes}
    (extendsRel : base.Extends rel) (free : ¬ Compression.Collision rel) (realized : rel.Realizes seen) :
    seen.Model (Named base) (fun digest bytes => Named base digest bytes ∨
      (seen.Queried digest ∧ Named rel digest bytes)) := by
  have included : Subset (fun digest bytes => Named base digest bytes ∨
      (seen.Queried digest ∧ Named rel digest bytes)) (Named rel) :=
    fun {_ _} hit => hit.elim (fun old => named_mono extendsRel old) And.right
  refine ⟨fun {_ _ _} left right => named_binding free (included left) (included right),
    fun {_ _} hit => Or.inl hit, fun {_ _} hit => hit.imp_right And.left, ?_⟩
  intro digest query
  obtain ⟨bytes, named, fits⟩ := realized digest query
  exact ⟨bytes, Or.inr ⟨query, named⟩, fits⟩

theorem witness_union {base : Compression} {seen : Observations Bytes}
    {pick : Bytes → Bytes} {support : Bytes → Compression} (canonical : base.Canonical)
    (free : ¬ base.Collision) (family : base.WitnessFamily seen pick support) :
    let rel := base.witnessUnion seen support
    base.Extends rel ∧ rel.Canonical ∧ ¬ rel.Collision ∧ rel.Realizes seen := by
  dsimp only
  refine ⟨fun {_ _} hit => Or.inl hit, ?_, ?_, ?_⟩
  · rintro input lhs rhs (left | ⟨ld, lq, left⟩) (right | ⟨rd, rq, right⟩)
    · exact canonical left right
    · exact (family.2.1 rd rq).1 left right
    · exact ((family.2.1 ld lq).1 right left).symm
    · exact (family.2.2 ld rd lq rq).1 left right
  · rintro ⟨lhs, rhs, output, ne, left | ⟨ld, lq, left⟩, right | ⟨rd, rq, right⟩⟩
    · exact free ⟨lhs, rhs, output, ne, left, right⟩
    · exact ne ((family.2.1 rd rq).2 left right)
    · exact ne ((family.2.1 ld lq).2 right left).symm
    · exact ne ((family.2.2 ld rd lq rq).2 left right)
  · intro digest query
    obtain ⟨fits, named⟩ := family.1 digest query
    exact ⟨pick digest, named_mono (fun {_ _} hit => Or.inr ⟨digest, query, hit⟩) named, fits⟩

theorem extension_iff {base : Compression} {seen : Observations Bytes} :
    (∃ rel, base.Extends rel ∧ rel.Canonical ∧ ¬ rel.Collision ∧ rel.Realizes seen) ↔
    base.Canonical ∧ ¬ base.Collision ∧ ∃ pick support, base.WitnessFamily seen pick support := by
  classical
  constructor
  · rintro ⟨rel, extendsRel, canonical, free, realized⟩
    let pick (digest : Bytes) := if query : seen.Queried digest then (realized digest query).choose else []
    refine ⟨fun {_ _ _} lhs rhs => canonical (extendsRel lhs) (extendsRel rhs), ?_, pick, fun _ => rel,
      ?_, fun _ _ => ⟨?_, ?_⟩, fun _ _ _ _ => ⟨?_, ?_⟩⟩
    · rintro ⟨left, right, output, ne, lhs, rhs⟩
      exact free ⟨left, right, output, ne, extendsRel lhs, extendsRel rhs⟩
    · intro digest query
      simpa only [pick, dite_eq_left query, and_comm] using (realized digest query).choose_spec
    · exact fun {_ _ _} lhs rhs => canonical (extendsRel lhs) rhs
    · exact fun {_ _ _} lhs rhs => same_input free (extendsRel lhs) rhs
    · exact fun {_ _ _} lhs rhs => canonical lhs rhs
    · exact fun {_ _ _} lhs rhs => same_input free lhs rhs
  · rintro ⟨canonical, free, pick, support, family⟩
    exact ⟨_, witness_union canonical free family⟩

theorem certified_bound {rel : Compression} {seen : Observations Bytes}
    (certified : ∀ digest fact, seen digest fact → Certified rel digest fact) (digest : Bytes) : seen.Bounded digest := by
  refine ⟨2 ^ 64 - 1, ?_⟩
  intro fact observed
  have cert := certified digest fact observed
  cases fact with
  | range offset fragment =>
    obtain ⟨size, opened⟩ := cert
    have bound := opened.bound
    obtain ⟨_, openedRoot, _⟩ := opened
    have valid := openedRoot.1
    unfold validSize at valid
    change offset + fragment.length ≤ _
    omega
  | whole bytes =>
    have valid : validSize bytes.length := cert.1
    unfold validSize at valid
    exact Nat.le_sub_one_of_lt valid
  | eof length =>
    obtain ⟨_, openedRoot, _⟩ := cert
    exact Nat.le_sub_one_of_lt openedRoot.1

theorem fits_of_certifiedAt {rel : Compression} {seen : Observations Bytes} {digest bytes : Bytes}
    (free : ¬ rel.Collision) (named : Named rel digest bytes)
    (certified : ∀ fact, seen digest fact → CertifiedAt rel digest bytes.length fact) : seen.Fits digest bytes := by
  intro fact observed
  have cert := certified fact observed
  cases fact with
  | range offset fragment => exact Fact.range_iff.mpr ((Checked.sliceOrCollision cert named rfl).resolve_right free)
  | whole expected => exact Fact.whole_iff.mpr (named_binding free named cert.2)
  | eof length => exact Fact.eof_iff.mpr cert.1.symm

private def byteAt : Shape → Opening → Nat → Option UInt8
  | .leaf .., .leaf bytes, pos => bytes[pos]?
  | .fork left right, .fork lhs rhs, pos =>
    if pos < left.size then byteAt left lhs pos else byteAt right rhs (pos - left.size)
  | _, _, _ => none

private theorem read_point {shape : Shape} {opening : Opening} {offset : Nat} {fragment : Bytes}
    (read : Read shape opening offset fragment) {index : Nat} {byte : UInt8} (hit : fragment[index]? = some byte) :
    byteAt shape opening (offset + index) = some byte := by
  induction read generalizing index with
  | leaf _ => simpa [byteAt] using hit
  | @left left right lhs rhs offset bytes read ih =>
    have inside := (List.getElem?_eq_some_iff.mp hit).choose
    have bound := read.bound
    simp only [byteAt, ite_eq_left (show offset + index < left.size by omega)]
    exact ih hit
  | @right left right lhs rhs offset bytes _ ih =>
    simp only [byteAt, ite_eq_right (show ¬ left.size + offset + index < left.size by omega)]
    simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using ih hit
  | @join left right lhs rhs offset before after lread rread adjacent lih rih =>
    by_cases onLeft : index < before.length
    · rw [List.getElem?_append_left onLeft] at hit
      exact (ite_eq_left (show offset + index < left.size by omega)).trans (lih hit)
    · have onRight : before.length ≤ index := by omega
      rw [List.getElem?_append_right onRight] at hit
      have diff : offset + index - left.size = index - before.length := by omega
      simpa only [byteAt, ite_eq_right (show ¬ offset + index < left.size by omega), diff, Nat.zero_add] using rih hit
  | @sub shape opening offset bytes start part read slice ih =>
    have atSource := (Fact.range_iff.mpr slice).2.2 (start + index) byte ⟨index, rfl, hit⟩
    simpa only [Nat.add_assoc] using ih atSource

private theorem agree_point {shape : Shape} {lhs rhs : Opening} (agree : Agree lhs rhs)
    {pos : Nat} {left right : UInt8} (lh : byteAt shape lhs pos = some left)
    (rh : byteAt shape rhs pos = some right) : left = right := by
  induction agree generalizing shape pos with
  | opaqueLeft => cases shape <;> simp [byteAt] at lh
  | opaqueRight => cases shape <;> simp [byteAt] at rh
  | leaf => exact Option.some.inj (lh.symm.trans rh)
  | fork _ _ lih rih =>
    cases shape with
    | leaf => simp [byteAt] at lh
    | fork left right =>
      by_cases inside : pos < left.size
      · simp only [byteAt, ite_eq_left inside] at lh rh
        exact lih lh rh
      · simp only [byteAt, ite_eq_right inside] at lh rh
        exact rih lh rh

theorem checked_overlap {rel : Compression} {digest lhs rhs : Bytes} {extent lo ro pos : Nat}
    {left right : UInt8} (free : ¬ rel.Collision)
    (lchecked : Checked rel extent digest lo lhs) (rchecked : Checked rel extent digest ro rhs)
    (lh : (Fact.range lo lhs).reads pos left) (rh : (Fact.range ro rhs).reads pos right) : left = right := by
  obtain ⟨_, lroot, lread⟩ := lchecked
  obtain ⟨_, rroot, rread⟩ := rchecked
  obtain ⟨li, leq, lhit⟩ := lh
  obtain ⟨ri, req, rhit⟩ := rh
  have agree := (lroot.agreeOrCollision rroot).resolve_right free
  exact agree_point agree (leq ▸ read_point lread lhit) (req ▸ read_point rread rhit)

private theorem certifiedAt_bound {rel : Compression} {digest : Bytes} {extent : Nat} {fact : Fact}
    (cert : CertifiedAt rel digest extent fact) : fact.bound ≤ extent := by
  cases fact with
  | range _ _ => exact Checked.bound cert
  | whole _ => exact Nat.le_of_eq cert.1
  | eof _ => exact Nat.le_of_eq cert.1

private theorem certifiedAt_end {rel : Compression} {digest : Bytes} {extent length : Nat} {fact : Fact}
    (cert : CertifiedAt rel digest extent fact) (ending : fact.end? = some length) : length = extent := by
  cases fact with
  | range _ _ => cases ending
  | whole _ => exact (Option.some.inj ending).symm.trans cert.1
  | eof _ => exact (Option.some.inj ending).symm.trans cert.1

theorem compatible_of_certifiedAt {rel : Compression} {seen : Observations Bytes} {digest : Bytes} {extent : Nat}
    (free : ¬ rel.Collision)
    (certified : ∀ fact, seen digest fact → CertifiedAt rel digest extent fact) : seen.Compatible digest := by
  refine ⟨?_, ⟨extent, fun fact hit => certifiedAt_bound (certified fact hit)⟩, ?_⟩
  · rintro pos left right ⟨lhs, lseen, lh⟩ ⟨rhs, rseen, rh⟩
    have lc := certified lhs lseen
    have rc := certified rhs rseen
    cases lhs with
    | eof _ => exact lh.elim
    | whole bytes =>
      have fits := fits_of_certifiedAt free lc.2 (fun fact hit => lc.1 ▸ certified fact hit)
      exact Option.some.inj (lh.symm.trans ((fits rhs rseen).2.2 pos right rh))
    | range offset fragment =>
      cases rhs with
      | eof _ => exact rh.elim
      | whole bytes =>
        have fits := fits_of_certifiedAt free rc.2 (fun fact hit => rc.1 ▸ certified fact hit)
        exact Option.some.inj (((fits (.range offset fragment) lseen).2.2 pos left lh).symm.trans rh)
      | range _ _ => exact checked_overlap free lc rc lh rh
  · intro ending fact length eHit fHit exactEnd
    exact (certifiedAt_end (certified ending eHit) exactEnd).symm ▸ certifiedAt_bound (certified fact fHit)

theorem model_of_certifiedAt {rel : Compression} {seen : Observations Bytes} (free : ¬ rel.Collision)
    (geometryGuard : ∀ digest, seen.Queried digest → ∃ extent,
      (∀ fact, seen digest fact → CertifiedAt rel digest extent fact) ∧
      (∀ bytes, Named rel digest bytes → bytes.length = extent)) :
    ∃ names, seen.Model (Named rel) names := by
  apply Observations.exists_model_iff.mpr
  refine ⟨named_binding free, ?_, ?_⟩
  · intro digest bytes named fact hit
    obtain ⟨extent, cert, agree⟩ := geometryGuard digest ⟨fact, hit⟩
    exact fits_of_certifiedAt free named (fun other obs => agree bytes named ▸ cert other obs) fact hit
  · intro digest queried
    obtain ⟨_, cert, _⟩ := geometryGuard digest queried
    exact compatible_of_certifiedAt free cert

end Silmaril.Proofs.Crypto.Blake3.Range.Extension
