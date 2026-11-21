module

public import Silmaril.Semantics.Arena.Traits.Parsed.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Traits.Cache

variable {Rep Key Name Obj Error Semantic Result : Type}

/-- Positive byte evidence is pinned to the current authoritative observation.
This is not an alternative authoritative store or a negative cache. -/
structure Layer (bytes : Rep → Name → Option ByteArray) where
  backing : Rep
  hot : Name → Option ByteArray
  agrees : ∀ name wire, hot name = some wire → bytes backing name = some wire

namespace Layer

variable {bytes : Rep → Name → Option ByteArray}

def cold (backing : Rep) : Layer bytes := ⟨backing, fun _ => none, fun _ _ found => by cases found⟩

def probe (layer : Layer bytes) : Parsed.Source Name Unit := fun name =>
  match layer.hot name with
  | some wire => .present wire
  | none => .unavailable ()

def get (getBacking : Rep → Name → Except Error (Option ByteArray)) (layer : Layer bytes)
    (name : Name) : Except Error (Option ByteArray) :=
  match layer.hot name with
  | some wire => .ok (some wire)
  | none => getBacking layer.backing name

/-- Staging with agreement proof does not infer bytes from a name. The
read-through adapter obtains this proof at the trusted read boundary. -/
def remember [DecidableEq Name] (layer : Layer bytes) (name : Name) (wire : ByteArray)
    (present : bytes layer.backing name = some wire) : Layer bytes where
  backing := layer.backing
  hot query := if query = name then some wire else layer.hot query
  agrees := fun query value hit => by
    by_cases eq : query = name
    · subst query
      exact present.trans (by simpa using hit)
    · exact layer.agrees _ _ (by simpa [eq] using hit)

def evict [DecidableEq Name] (layer : Layer bytes) (name : Name) : Layer bytes where
  backing := layer.backing
  hot query := if query = name then none else layer.hot query
  agrees := fun query wire hit => by
    by_cases eq : query = name
    · simp [eq] at hit
    · exact layer.agrees _ _ (by simpa [eq] using hit)

def warm [DecidableEq Name] (getBacking : Rep → Name → Except Error (Option ByteArray))
    (sound : ∀ state name found, getBacking state name = .ok found → found = bytes state name) (name : Name) :
    Mutable.Mutation (Layer bytes) Error (Option ByteArray) := fun layer =>
  match read : layer.get getBacking name with
  | .error fault => .error fault
  | .ok none => .ok (none, layer)
  | .ok (some wire) =>
    have present : bytes layer.backing name = some wire := by
      unfold get at read
      split at read
      · exact layer.agrees _ _ ‹_› |>.trans (Except.ok.inj read)
      · exact (sound _ _ _ read).symm
    .ok (some wire, layer.remember name wire present)

/-- Cached hits can survive a backing transition only if it extends the
binding snapshot. For switching authorities use `cold`, not this transport. -/
def advance (layer : Layer bytes) (next : Rep)
    (included : Naming.Subset (Naming.graph (bytes layer.backing)) (Naming.graph (bytes next))) : Layer bytes :=
  ⟨next, layer.hot, fun _ _ found => included (layer.agrees _ _ found)⟩

def lift (edit : Step Rep Semantic Error Result)
    (stable : ∀ state result next, edit state = .ok (result, next) →
      Naming.Subset (Naming.graph (bytes state)) (Naming.graph (bytes next))) : Step (Layer bytes) Semantic Error Result :=
  fun layer => match committed : edit layer.backing with
  | .error fault => .error fault
  | .ok (result, next) => .ok (result, layer.advance next (stable _ _ _ committed))

end Layer
end Silmaril.Semantics.Arena.Traits.Cache
