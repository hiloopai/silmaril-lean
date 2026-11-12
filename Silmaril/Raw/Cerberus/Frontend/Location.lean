module

public import Silmaril.Cerberus.Ctype.Defs

/-! # Locations: the helpers of `Cerb_location` and `Annot` that the frontend uses

Ports of `util/cerb_location.ml` (`bbox_location`, `with_cursor_from`) and of
`frontend/model/annot.lem` (`get_loc`, `get_loc_`) at `b3e11ea3`, on the cursor-free `Loc`
that the wire format carries. A region's cursor is never printed, so a region with any
cursor is the region; the cursor of a location built here is the one `with_cursor_from`
would give, as far as a later `with_cursor_from` on an unknown location can observe it.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- A position: file, line and byte column. -/
abbrev LocPos := String × Int × Int

/-- `Cerb_location.outer_bbox`'s `pos_lt` (`cerb_location.ml:107-112`): on the same line the
columns decide (the offsets of one line differ by their columns), otherwise the lines. -/
def posLt (p q : LocPos) : Bool :=
  if p.2.1 = q.2.1 then p.2.2 < q.2.2 else p.2.1 < q.2.1

/-- `Cerb_location.outer_bbox` (`cerb_location.ml:102-115`). -/
def outerBbox : List (LocPos × LocPos) → Option (LocPos × LocPos)
  | [] => none
  | (b0, e0) :: xs =>
    some ((b0, e0) :: xs |>.foldl (fun (bAcc, eAcc) (b, e) =>
      ((if posLt b bAcc then b else bAcc), (if posLt e eAcc then eAcc else e))) (b0, e0))

/-- `Cerb_location.bbox_location` (`cerb_location.ml:120-149`): the smallest region that
covers the located ones; with none, the last `Loc_other`, or unknown. -/
def bboxLocation (xs : List Loc) : Loc :=
  let (defLoc, acc) := xs.foldl (fun (defLoc, acc) loc =>
    match loc with
    | .unknown => (defLoc, acc)
    | .other _ => (loc, acc)
    | .point f l c => (defLoc, ((f, l, c), (f, l, c)) :: acc)
    | .region f₁ l₁ c₁ f₂ l₂ c₂ => (defLoc, ((f₁, l₁, c₁), (f₂, l₂, c₂)) :: acc))
    (Loc.unknown, ([] : List (LocPos × LocPos)))
  match outerBbox acc with
  | none => defLoc
  | some ((f₁, l₁, c₁), (f₂, l₂, c₂)) => .region f₁ l₁ c₁ f₂ l₂ c₂

/-- `Cerb_location.with_cursor_from loc1 loc2` (`cerb_location.ml:59-90`): the region of
`loc1` (a point becomes an empty region), with the cursor of `loc2`. Only when `loc1` is
unknown does the cursor show: it becomes the location. -/
def withCursorFrom (loc₁ loc₂ : Loc) : Loc :=
  match loc₁ with
  | .unknown =>
    match loc₂ with
    | .unknown | .other _ => .unknown
    | .point f l c => .point f l c
    | .region f₁ l₁ c₁ f₂ l₂ c₂ => .region f₁ l₁ c₁ f₂ l₂ c₂
  | .other s => .other s
  | .point f l c => .region f l c f l c
  | .region .. => loc₁

/-- `Cerb_location.with_cursor` (`cerb_location.ml:41-54`) of a location without cursor: the
start of a region. (A region built by `withCursorFrom` has the cursor of its second
argument; callers pass that location instead.) -/
def withCursor : Loc → Loc
  | .unknown | .other _ => .unknown
  | .point f l c | .region f l c _ _ _ => .point f l c

/-- `Annot.get_loc` (`annot.lem:126`): the first location annotation. -/
def getLoc : List Annot → Option Loc
  | [] => none
  | .loc l :: _ => some l
  | _ :: annots => getLoc annots

/-- `Annot.get_loc_` (`annot.lem:148`). -/
def getLoc_ (annots : List Annot) : Loc := (getLoc annots).getD .unknown

/-- `Located ctype`'s `locOf` (`ctype.lem:69-73`). -/
def ctypeLocOf : Ctype → Loc
  | .mk annots _ => getLoc_ annots

/-- `Annot.no_attributes` (`annot.lem:24`). -/
def noAttributes : Attributes := .mk []

/-- `Annot.combine_attributes` (`annot.lem:28`). -/
def combineAttributes : Attributes → Attributes → Attributes
  | .mk xs₁, .mk xs₂ => .mk (xs₁ ++ xs₂)

/-- `Annot.is_cerb_byte` (`annot.lem:213`): an attribute `[[cerb::byte]]`. -/
def isCerbByte : Attributes → Bool
  | .mk attrs => attrs.any fun a =>
    a.ns.map (·.name) == some "cerb" && a.id.name == "byte"

end Silmaril.Cerberus.Frontend
