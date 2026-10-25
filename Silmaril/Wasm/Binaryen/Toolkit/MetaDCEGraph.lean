module

public import Lean

@[expose] public section

/-! The closed-module subset of Binaryen's external DCE graph format.

The runtime computes a finite candidate, then checks roots and edge closure.
`solve_exact` proves that every accepted candidate is precisely graph
reachability; the semantic contract never trusts a fuel bound. Unknown fields,
imports, duplicate bindings and dangling edges reject explicitly.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

open Lean

structure Node where
  name : String
  reaches : List String := []
  root : Bool := false
  exportName : Option String := none
  deriving Repr, DecidableEq

abbrev Graph := List Node

def roots (g : Graph) : List String := (g.filter (·.root)).map (·.name)

def step (g : Graph) (live : List String) : List String :=
  (live ++ ((g.filter fun n => live.contains n.name).flatMap (·.reaches))).eraseDups

def Closed (g : Graph) (live : List String) : Prop :=
  (∀ x ∈ roots g, x ∈ live) ∧
    ∀ n ∈ g, n.name ∈ live → ∀ x ∈ n.reaches, x ∈ live

instance (g : Graph) (live : List String) : Decidable (Closed g live) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive Reachable (g : Graph) : String → Prop where
  | root {x : String} : x ∈ roots g → Reachable g x
  | edge {n : Node} {x : String} : n ∈ g → Reachable g n.name → x ∈ n.reaches → Reachable g x

def iterate (g : Graph) : Nat → List String
  | 0 => roots g
  | fuel + 1 => step g (iterate g fuel)

def solve (g : Graph) : Option (List String) :=
  let live := iterate g g.length
  if Closed g live then some live else none

theorem step_sound {g : Graph} {live : List String}
    (h : ∀ x ∈ live, Reachable g x) :
    ∀ x ∈ step g live, Reachable g x := by
  intro x hx
  simp only [step, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    List.mem_filter, List.contains_iff_mem] at hx
  rcases hx with hx | ⟨n, ⟨hn, hl⟩, hx⟩
  · exact h x hx
  · exact .edge hn (h n.name hl) hx

theorem iterate_sound (g : Graph) (fuel : Nat) :
    ∀ x ∈ iterate g fuel, Reachable g x := by
  induction fuel with
  | zero => exact fun _ h => .root h
  | succ fuel ih =>
    exact step_sound ih

theorem closed_complete {g : Graph} {live : List String} (h : Closed g live)
    {x : String} (hx : Reachable g x) : x ∈ live := by
  induction hx with
  | root hr => exact h.1 _ hr
  | edge hn _ hx ih => exact h.2 _ hn ih _ hx

/-- Successful graph solving is exact, including cycles and rootless graphs. -/
theorem solve_exact {g : Graph} {live : List String} (h : solve g = some live) :
    Closed g live ∧ ∀ x, x ∈ live ↔ Reachable g x := by
  unfold solve at h
  dsimp only at h
  split at h
  · next hc =>
    cases h
    exact ⟨hc, fun _ => ⟨iterate_sound _ _ _, closed_complete hc⟩⟩
  · contradiction

def selected (g : Graph) (live : List String) : List String :=
  (g.filter fun n => live.contains n.name).filterMap (·.exportName)

theorem selected_iff_reachable {g : Graph} {live : List String} (h : solve g = some live)
    (name : String) : name ∈ selected g live ↔
      ∃ n ∈ g, Reachable g n.name ∧ n.exportName = some name := by
  have exactness := (solve_exact h).2
  simp only [selected, List.mem_filterMap, List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨n, ⟨hn, hl⟩, he⟩
    exact ⟨n, hn, (exactness _).mp hl, he⟩
  · rintro ⟨n, hn, hr, he⟩
    exact ⟨n, ⟨hn, (exactness _).mpr hr⟩, he⟩

def validate (g : Graph) : Except String Graph := do
  let names := g.map (·.name)
  if !names.Nodup then throw "metadce: duplicate graph node name"
  let exports := g.filterMap (·.exportName)
  if !exports.Nodup then throw "metadce: duplicate export binding"
  for n in g do
    for target in n.reaches do
      if !names.contains target then throw s!"metadce: dangling graph edge {n.name} -> {target}"
  pure g

def parseNode (j : Json) : Except String Node := do
  let obj ← j.getObj?
  for (key, _) in obj.toList do
    unless ["name", "reaches", "root", "export"].contains key do
      throw s!"metadce: unsupported graph field {key}"
  let name ← j.getObjValAs? String "name"
  let reaches ← if obj.contains "reaches" then j.getObjValAs? (List String) "reaches" else pure []
  let root ← if obj.contains "root" then do
      let root ← j.getObjValAs? Bool "root"
      unless root do throw "metadce: root, when present, must be true"
      pure true
    else pure false
  let exportName ← if obj.contains "export" then some <$> j.getObjValAs? String "export" else pure none
  pure ⟨name, reaches, root, exportName⟩

def parseGraph (text : String) : Except String Graph := do
  let json ← Json.parse text
  let nodes ← json.getArr?
  validate (← nodes.toList.mapM parseNode)

/- Small, nonvacuous statement checks, before the module simulation proof. -/
private def sample : Graph :=
  [⟨"main", ["bridge"], true, none⟩, ⟨"bridge", ["exportNode"], false, none⟩,
   ⟨"exportNode", ["bridge"], false, some "entry"⟩,
   ⟨"dead", [], false, some "unused"⟩]

example : (solve sample).map (selected sample) = some ["entry"] := by decide
example : solve [⟨"cycle", ["cycle"], false, some "unused"⟩] = some [] := by decide
example : validate [⟨"a", ["missing"], true, none⟩] =
    .error "metadce: dangling graph edge a -> missing" := by rfl

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
