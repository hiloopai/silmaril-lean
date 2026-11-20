module

public import Silmaril.Wasm.Sublanguages.Strict.Thms
public import Silmaril.Wasm.Sublanguages.Strict.Link.Defs
import Silmaril.Proofs.Wasm.Sublanguages.Strict.Link.Proofs
import Silmaril.Proofs.Wasm.Sublanguages.Strict.Link.Features

@[expose] public section

namespace Silmaril.Wasm.Sublanguages.StrictLink

open Link

/-- Exact assembly agreement before validating the result, including failure. -/
theorem assemble?_toCore (namespaceName : String) (provider : LocalSections) (consumer : FunctionModule) :
    (assemble? namespaceName provider consumer).map (LocalSections.assemble · []) =
      GC.assemble? namespaceName (provider.assemble []) consumer.toCore :=
  Silmaril.Proofs.Wasm.Sublanguages.StrictLink.assemble?_toCore namespaceName provider consumer

/-- Relocation does not add features to code or type groups, including nested
body instructions. The result retains every capability bound of both inputs. -/
theorem assemble_features {namespaceName : String} {provider : LocalSections} {consumer : FunctionModule}
    {result : LocalSections} (caps : Models.FeatureSet)
    (hp : Models.Module.InFeat caps (provider.assemble [])) (hc : Models.Module.InFeat caps consumer.toCore)
    (h : assemble? namespaceName provider consumer = some result) :
    Models.Module.InFeat caps (result.assemble []) :=
  Silmaril.Proofs.Wasm.Sublanguages.StrictLink.assemble_features caps hp hc h

/-- Native static link followed by embedding equals static link of the Core
images. This includes failures, not just successful pairs or observations. -/
theorem link?_toCore (namespaceName : String) (provider : Ultrastrict) (consumer : Strict) :
    (link? namespaceName provider consumer).map Ultrastrict.toCore =
      GC.link? namespaceName provider.toCore consumer.toCore :=
  Silmaril.Proofs.Wasm.Sublanguages.StrictLink.link?_toCore namespaceName provider consumer

theorem link?_valid {namespaceName : String} {provider : Ultrastrict} {consumer : Strict} {result : Ultrastrict}
    (h : link? namespaceName provider consumer = some result) : Validation.ModuleValid result.toCore :=
  GC.link?_valid ((link?_toCore namespaceName provider consumer).symm.trans (congrArg _ h))

end Silmaril.Wasm.Sublanguages.StrictLink
