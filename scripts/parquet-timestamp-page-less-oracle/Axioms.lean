module

import Silmaril.Formats.Parquet.Footer.PageLessTimestamp.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Thms

open Silmaril.Formats.Parquet

#print axioms Footer.PageLessTimestamp.pageLess_zero
#print axioms Footer.PageLessTimestamp.groupStop_empty
#print axioms Footer.PageLessTimestamp.validate_wire
#print axioms Footer.PageLessTimestamp.validate_empty
#print axioms Snapshot.checkPageLessTimestamp_exact
#print axioms Snapshot.check_noPageLessTimestamp

open Timestamp.Leaf.MixedGroups.PageLess

#print axioms openLeaf_exact
#print axioms openBound_sound
#print axioms readGroup_empty
#print axioms readGroup_framed
#print axioms readGroup_missing
#print axioms readBound_reference
#print axioms readBound_first_error
#print axioms convert_readback
#print axioms convert_first_error
