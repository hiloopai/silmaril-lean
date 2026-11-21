module

public import Silmaril.Crypto.Blake3.Range.Extension.Defs
public import Silmaril.Crypto.Blake3.Range.EOF.Thms
public import Silmaril.Semantics.Naming.ByteRange.Extension.Thms
import Silmaril.Proofs.Crypto.Blake3.Range.Extension

public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming
open Silmaril.Semantics.Naming.ByteRange (Fact Observations)

theorem Trace.mono {base rel : Compression} (extendsRel : base.Extends rel)
    {root : Bool} {shape : Shape} {opening : Opening} {output : CV}
    (trace : Trace base root shape opening output) : Trace rel root shape opening output :=
  Proofs.Crypto.Blake3.Range.Extension.trace_mono extendsRel trace

theorem Named.mono {base rel : Compression} (extendsRel : base.Extends rel) :
    Subset (Named base) (Named rel) := Proofs.Crypto.Blake3.Range.Extension.named_mono extendsRel

theorem Named.binding {rel : Compression} (free : ¬ rel.Collision) : Binding (Named rel) :=
  Proofs.Crypto.Blake3.Range.Extension.named_binding free

theorem Named.uniqueNames {rel : Compression} (canonical : rel.Canonical) : UniqueNames (Named rel) :=
  Proofs.Crypto.Blake3.Range.Extension.named_unique canonical

theorem Compression.Realizes.model {base rel : Compression} {seen : Observations Bytes}
    (realized : rel.Realizes seen) (extendsRel : base.Extends rel) (free : ¬ rel.Collision) :
    seen.Model (Named base) (fun digest bytes => Named base digest bytes ∨
      (seen.Queried digest ∧ Named rel digest bytes)) :=
  Proofs.Crypto.Blake3.Range.Extension.realizes_model extendsRel free realized

/-- Combining legal whole-trace witnesses only requires pairwise transition agreement,
including agreement with the existing table. No finiteness or common-length assumption. -/
theorem Compression.WitnessFamily.union {base : Compression} {seen : Observations Bytes}
    {pick : Bytes → Bytes} {support : Bytes → Compression} (family : base.WitnessFamily seen pick support)
    (canonical : base.Canonical) (free : ¬ base.Collision) :
    let rel := base.witnessUnion seen support
    base.Extends rel ∧ rel.Canonical ∧ ¬ rel.Collision ∧ rel.Realizes seen :=
  Proofs.Crypto.Blake3.Range.Extension.witness_union canonical free family

theorem Compression.exists_extension_iff {base : Compression} {seen : Observations Bytes} :
    (∃ rel, base.Extends rel ∧ rel.Canonical ∧ ¬ rel.Collision ∧ rel.Realizes seen) ↔
    base.Canonical ∧ ¬ base.Collision ∧ ∃ pick support, base.WitnessFamily seen pick support :=
  Proofs.Crypto.Blake3.Range.Extension.extension_iff

theorem Certified.bounded {rel : Compression} {seen : Observations Bytes}
    (certified : ∀ digest fact, seen digest fact → Certified rel digest fact) (digest : Bytes) :
    seen.Bounded digest := Proofs.Crypto.Blake3.Range.Extension.certified_bound certified digest

/-- Against any actually named whole with the matched extent, `CertifiedAt` facts hold. -/
theorem CertifiedAt.fits {rel : Compression} {seen : Observations Bytes} {digest bytes : Bytes}
    (free : ¬ rel.Collision) (named : Named rel digest bytes)
    (certified : ∀ fact, seen digest fact → CertifiedAt rel digest bytes.length fact) : seen.Fits digest bytes :=
  Proofs.Crypto.Blake3.Range.Extension.fits_of_certifiedAt free named certified

theorem Checked.overlap {rel : Compression} {digest lhs rhs : Bytes} {extent lo ro pos : Nat}
    {left right : UInt8} (free : ¬ rel.Collision)
    (lchecked : Checked rel extent digest lo lhs) (rchecked : Checked rel extent digest ro rhs)
    (lh : (Fact.range lo lhs).reads pos left) (rh : (Fact.range ro rhs).reads pos right) : left = right :=
  Proofs.Crypto.Blake3.Range.Extension.checked_overlap free lchecked rchecked lh rh

/-- This does not require an actually named whole, and it does not turn an
interior range's extent claim into EOF. -/
theorem CertifiedAt.compatible {rel : Compression} {seen : Observations Bytes} {digest : Bytes} {extent : Nat}
    (free : ¬ rel.Collision)
    (certified : ∀ fact, seen digest fact → CertifiedAt rel digest extent fact) : seen.Compatible digest :=
  Proofs.Crypto.Blake3.Range.Extension.compatible_of_certifiedAt free certified

theorem CertifiedAt.model {rel : Compression} {seen : Observations Bytes} (free : ¬ rel.Collision)
    (geometryGuard : ∀ digest, seen.Queried digest → ∃ extent,
      (∀ fact, seen digest fact → CertifiedAt rel digest extent fact) ∧
      (∀ bytes, Named rel digest bytes → bytes.length = extent)) :
    ∃ names, seen.Model (Named rel) names := Proofs.Crypto.Blake3.Range.Extension.model_of_certifiedAt free geometryGuard

end Silmaril.Crypto.Blake3
