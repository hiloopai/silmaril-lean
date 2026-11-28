module

public import Silmaril.Logic.ACL2.Recursive.Thms
public import Silmaril.Logic.ACL2.Standard.Objects.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard

/-- Instantiate the recursive certificate interface with the standard `acl2-count`. -/
def objectCdrSize : Recursive.CdrSize objectPrimitives where
  size := Object.acl2Count
  cdr_lt _ := Object.acl2Count_cdr_lt

end Silmaril.Logic.ACL2.Standard
