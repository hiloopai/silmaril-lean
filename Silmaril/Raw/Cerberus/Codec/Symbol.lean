module

public import Silmaril.Cerberus.Codec.Tags.Defs
public import Silmaril.Cerberus.Codec.Digest.Defs

/-! # Wire codecs for locations and symbols

Each codec is a hand-written encoder in the wire format of `docs/projects/cerberus.md`
and a table of alternatives for decoding. Both round-trip laws come from
`Silmaril.TaggedCodec`; the obligations here are discharged by the
`codec_*` tactics. `digest` rejects noncanonical
hexadecimal and stores bytes. Document well-formedness checks their length.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec

def encodeLoc : Loc → Tree
  | .unknown => node "$loc_unknown" []
  | .other s => node "$loc_other" [str.enc s]
  | .point f l c => node "$loc_point" [str.enc f, int.enc l, int.enc c]
  | .region f l c f' l' c' =>
    node "$loc_region" [str.enc f, int.enc l, int.enc c, str.enc f', int.enc l', int.enc c']

-- Locations use fixed OCaml wire tags, without constructor entries in `Names`.
def loc : Codec Loc := ofAlts encodeLoc
  [ctorLeaf% Loc.unknown "$loc_unknown",
   ctorAlt% Loc.other "$loc_other" str,
   ctorAlt% Loc.point "$loc_point" (str ⊗ int ⊗ int),
   ctorAlt% Loc.region "$loc_region" (str ⊗ int ⊗ int ⊗ str ⊗ int ⊗ int)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeIdentifier : Identifier → Tree
  | .mk l s => node (tag% Identifier.mk) [loc.enc l, str.enc s]

def identifier : Codec Identifier := ofAlts encodeIdentifier
  [alt% Identifier.mk (loc ⊗ str)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeSymbolDescription : SymbolDescription → Tree
  | .none => node (tag% SymbolDescription.none) []
  | .unnamedTag l => node (tag% SymbolDescription.unnamedTag) [loc.enc l]
  | .id s => node (tag% SymbolDescription.id) [str.enc s]
  | .cnId s => node (tag% SymbolDescription.cnId) [str.enc s]
  | .objectAddress s => node (tag% SymbolDescription.objectAddress) [str.enc s]
  | .return_ => node (tag% SymbolDescription.return_) []
  | .funArgValue s => node (tag% SymbolDescription.funArgValue) [str.enc s]
  | .funArg l n => node (tag% SymbolDescription.funArg) [loc.enc l, nat.enc n]

def symbolDescription : Codec SymbolDescription := ofAlts encodeSymbolDescription
  [leaf% SymbolDescription.none,
   alt% SymbolDescription.unnamedTag loc,
   alt% SymbolDescription.id str,
   alt% SymbolDescription.cnId str,
   alt% SymbolDescription.objectAddress str,
   leaf% SymbolDescription.return_,
   alt% SymbolDescription.funArgValue str,
   alt% SymbolDescription.funArg (loc ⊗ nat)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeSym : Sym → Tree
  | .mk d n s => node (tag% Sym.mk) [digest.enc d, nat.enc n, symbolDescription.enc s]

def sym : Codec Sym := ofAlts encodeSym
  [alt% Sym.mk (digest ⊗ nat ⊗ symbolDescription)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodePrefix : Prefix → Tree
  | .source l ss => node (tag% Prefix.source) [loc.enc l, (list sym).enc ss]
  | .funArg l d n => node (tag% Prefix.funArg) [loc.enc l, digest.enc d, int.enc n]
  | .stringLiteral l d => node (tag% Prefix.stringLiteral) [loc.enc l, digest.enc d]
  | .compoundLiteral l d => node (tag% Prefix.compoundLiteral) [loc.enc l, digest.enc d]
  | .malloc => node (tag% Prefix.malloc) []
  | .temporaryLifetime l d => node (tag% Prefix.temporaryLifetime) [loc.enc l, digest.enc d]
  | .other s => node (tag% Prefix.other) [str.enc s]

def prefix_ : Codec Prefix := ofAlts encodePrefix
  [alt% Prefix.source (loc ⊗ list sym),
   alt% Prefix.funArg (loc ⊗ digest ⊗ int),
   alt% Prefix.stringLiteral (loc ⊗ digest),
   alt% Prefix.compoundLiteral (loc ⊗ digest),
   leaf% Prefix.malloc,
   alt% Prefix.temporaryLifetime (loc ⊗ digest),
   alt% Prefix.other str]
  (by codec_nodup) (by codec_enc) (by codec_cover)

@[simp] theorem loc_budget : loc.budget = none := rfl
@[simp] theorem identifier_budget : identifier.budget = none := rfl
@[simp] theorem symbolDescription_budget : symbolDescription.budget = none := rfl
@[simp] theorem sym_budget : sym.budget = none := rfl
@[simp] theorem prefix_budget : prefix_.budget = none := rfl

-- Literal wire spelling pins the constructor independently of the name map.
example : identifier.dec (node "Identifier" [node "$loc_unknown" [], node "$str" [.atom "main"]]) =
    some (Identifier.mk .unknown "main") := rfl

end Silmaril.Cerberus.Codec
