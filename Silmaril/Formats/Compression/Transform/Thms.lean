module

public import Silmaril.Formats.Compression.Transform.Defs
public import Silmaril.Formats.Compression.Format.Thms
import Silmaril.Proofs.Formats.Compression.Transform

/-!
# Whole-message transforms: composition laws

Proved (standard axioms):

* `id_andThen`, `andThen_id`, `andThen_assoc`: the identity is neutral and
  composition is associative (on `run`, as the parameter types are products);
* `inverts_andThen`: round trips compose (encode with the inner encoder first);
* `linearAt_id`, `linearAt_andThen`: linear output bounds multiply;
* `inverts_whole`, `inverts_members`, `linearAt_whole`, `linearAt_members`: a
  format's `RoundTrip` and `OutputLinear` claims give the transform laws, for
  whole buffers and for multi-member files (the latter needs `Consumes`);
* `Certified.inverts_whole`, `Certified.linearAt_members`, …: the same from a
  certificate's listed claims.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

namespace Transform

theorem id_andThen (t : Transform) (p : t.Params) (bytes : List UInt8) :
    (id.andThen t).run ((), p) bytes = t.run p bytes := rfl

theorem andThen_id (t : Transform) (p : t.Params) (bytes : List UInt8) :
    (t.andThen id).run (p, ()) bytes = t.run p bytes := by
  simp [andThen, id]

theorem andThen_assoc (t u v : Transform) (p : t.Params) (q : u.Params) (r : v.Params)
    (bytes : List UInt8) :
    ((t.andThen u).andThen v).run ((p, q), r) bytes = (t.andThen (u.andThen v)).run (p, q, r) bytes :=
  Proofs.Formats.Compression.Transform.andThen_assoc_run t u v p q r bytes

/-- **Round trips compose**: `andThen` reads back the inner encoder's output of
the outer encoder's output. -/
theorem inverts_andThen {t u : Transform} {p : t.Params} {q : u.Params} {e e' : Encoder}
    (ht : t.Inverts p e) (hu : u.Inverts q e') :
    (t.andThen u).Inverts (p, q) (fun data => e (e' data)) :=
  Proofs.Formats.Compression.Transform.inverts_andThen ht hu

theorem inverts_id : id.Inverts () fun data => data := fun _ => rfl

theorem linearAt_id : id.LinearAt () 1 := fun _ _ h => by
  cases h; simp

/-- **Linear bounds multiply** along a chain. -/
theorem linearAt_andThen {t u : Transform} {p : t.Params} {q : u.Params} {k l : Nat}
    (ht : t.LinearAt p k) (hu : u.LinearAt q l) : (t.andThen u).LinearAt (p, q) (l * k) :=
  Proofs.Formats.Compression.Transform.linearAt_andThen ht hu

variable {F : Format} {p : F.Params}

theorem inverts_whole {e : Encoder} (h : RoundTrip (F.decode p) e) : (whole F).Inverts p e :=
  h.whole

theorem inverts_members {e : Encoder} (h : RoundTrip (F.decode p) e) : (members F).Inverts p e :=
  h.members_single

theorem linearAt_whole {k : Nat} (h : (F.decode p).OutputLinear k) : (whole F).LinearAt p k :=
  fun _ _ hw => Decoder.whole_outputLinear h hw

theorem linearAt_members {k : Nat} (hc : (F.decode p).Consumes) (h : (F.decode p).OutputLinear k) :
    (members F).LinearAt p k :=
  fun _ _ hw => Decoder.members_outputLinear hc h hw

end Transform

namespace Certified

variable {F : Format} (C : Certified F)

theorem inverts_whole {E : Encoding F} (h : Capability.roundTrip E ∈ C.claims) (e : E.EParams) :
    (Transform.whole F).Inverts (E.params e) (E.encode e) :=
  Transform.inverts_whole (C.holds h e)

theorem inverts_members {E : Encoding F} (h : Capability.roundTrip E ∈ C.claims) (e : E.EParams) :
    (Transform.members F).Inverts (E.params e) (E.encode e) :=
  Transform.inverts_members (C.holds h e)

theorem linearAt_whole {s : Scope F} {k : Nat} (h : Capability.outputLinear s k ∈ C.claims)
    {p : F.Params} (hp : s p) : (Transform.whole F).LinearAt p k :=
  Transform.linearAt_whole (C.holds h p hp)

theorem linearAt_members {s s' : Scope F} {k : Nat} (hc : Capability.consumes s' ∈ C.claims)
    (h : Capability.outputLinear s k ∈ C.claims) {p : F.Params} (hp' : s' p) (hp : s p) :
    (Transform.members F).LinearAt p k :=
  Transform.linearAt_members (C.holds hc p hp') (C.holds h p hp)

end Certified

end Silmaril.Formats.Compression
