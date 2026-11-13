module

public import Silmaril.Cerberus.Undefined.Defs
public import Silmaril.Semantics.CPort.Encoding.TaggedCodec.Defs
public import Silmaril.Cerberus.Codec.Tags.Defs

/-! # Wire codecs for the undefined-behaviour catalogue

`UndefinedBehaviour` has about 240 constructors, nearly all nullary, so this
file is one encoder line and one alternative per constructor. The laws come
from `ofLeaves`. Its kernel-decided nullary coverage avoids the cubic search of
`codec_cover` on this catalogue. The table still costs more to elaborate and
replay than the smaller codecs; no per-constructor round-trip proof is needed.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec


def encodeUnspecifiedUbContext : UnspecifiedUbContext → Tree
  | .UB_unspec_equality_ptr_vs_NULL => node (tag% UnspecifiedUbContext.UB_unspec_equality_ptr_vs_NULL) []
  | .UB_unspec_equality_both_arith_or_ptr => node (tag% UnspecifiedUbContext.UB_unspec_equality_both_arith_or_ptr) []
  | .UB_unspec_pointer_add => node (tag% UnspecifiedUbContext.UB_unspec_pointer_add) []
  | .UB_unspec_pointer_sub => node (tag% UnspecifiedUbContext.UB_unspec_pointer_sub) []
  | .UB_unspec_conditional => node (tag% UnspecifiedUbContext.UB_unspec_conditional) []
  | .UB_unspec_copy_alloc_id => node (tag% UnspecifiedUbContext.UB_unspec_copy_alloc_id) []
  | .UB_unspec_rvalue_memberof => node (tag% UnspecifiedUbContext.UB_unspec_rvalue_memberof) []
  | .UB_unspec_memberofptr => node (tag% UnspecifiedUbContext.UB_unspec_memberofptr) []
  | .UB_unspec_do => node (tag% UnspecifiedUbContext.UB_unspec_do) []

def unspecifiedUbContext : Codec UnspecifiedUbContext := ofAlts encodeUnspecifiedUbContext
  [leaf% UnspecifiedUbContext.UB_unspec_equality_ptr_vs_NULL,
   leaf% UnspecifiedUbContext.UB_unspec_equality_both_arith_or_ptr,
   leaf% UnspecifiedUbContext.UB_unspec_pointer_add,
   leaf% UnspecifiedUbContext.UB_unspec_pointer_sub,
   leaf% UnspecifiedUbContext.UB_unspec_conditional,
   leaf% UnspecifiedUbContext.UB_unspec_copy_alloc_id,
   leaf% UnspecifiedUbContext.UB_unspec_rvalue_memberof,
   leaf% UnspecifiedUbContext.UB_unspec_memberofptr,
   leaf% UnspecifiedUbContext.UB_unspec_do]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeUndefinedByOmission : UndefinedByOmission → Tree
  | .UB_OMIT_memcpy_non_object => node (tag% UndefinedByOmission.UB_OMIT_memcpy_non_object) []
  | .UB_OMIT_memcpy_out_of_bound => node (tag% UndefinedByOmission.UB_OMIT_memcpy_out_of_bound) []

def undefinedByOmission : Codec UndefinedByOmission := ofAlts encodeUndefinedByOmission
  [leaf% UndefinedByOmission.UB_OMIT_memcpy_non_object,
   leaf% UndefinedByOmission.UB_OMIT_memcpy_out_of_bound]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeUndefinedBehaviour : UndefinedBehaviour → Tree
  | .DUMMY x => node (tag% UndefinedBehaviour.DUMMY) [str.enc x]
  | .UB_unspecified_lvalue => node (tag% UndefinedBehaviour.UB_unspecified_lvalue) []
  | .UB_std_omission x => node (tag% UndefinedBehaviour.UB_std_omission) [undefinedByOmission.enc x]
  | .UB001 => node (tag% UndefinedBehaviour.UB001) []
  | .UB002 => node (tag% UndefinedBehaviour.UB002) []
  | .UB003 => node (tag% UndefinedBehaviour.UB003) []
  | .UB004a_incorrect_main_return_type => node (tag% UndefinedBehaviour.UB004a_incorrect_main_return_type) []
  | .UB004b_incorrect_main_argument1 => node (tag% UndefinedBehaviour.UB004b_incorrect_main_argument1) []
  | .UB004c_incorrect_main_argument2 => node (tag% UndefinedBehaviour.UB004c_incorrect_main_argument2) []
  | .UB004d_main_not_function => node (tag% UndefinedBehaviour.UB004d_main_not_function) []
  | .UB005_data_race => node (tag% UndefinedBehaviour.UB005_data_race) []
  | .UB006 => node (tag% UndefinedBehaviour.UB006) []
  | .UB007 => node (tag% UndefinedBehaviour.UB007) []
  | .UB008_multiple_linkage => node (tag% UndefinedBehaviour.UB008_multiple_linkage) []
  | .UB009_outside_lifetime => node (tag% UndefinedBehaviour.UB009_outside_lifetime) []
  | .UB010_pointer_to_dead_object => node (tag% UndefinedBehaviour.UB010_pointer_to_dead_object) []
  | .UB011_use_indeterminate_automatic_object => node (tag% UndefinedBehaviour.UB011_use_indeterminate_automatic_object) []
  | .UB_modifying_temporary_lifetime => node (tag% UndefinedBehaviour.UB_modifying_temporary_lifetime) []
  | .UB012_lvalue_read_trap_representation => node (tag% UndefinedBehaviour.UB012_lvalue_read_trap_representation) []
  | .UB013_lvalue_side_effect_trap_representation => node (tag% UndefinedBehaviour.UB013_lvalue_side_effect_trap_representation) []
  | .UB014_unsupported_negative_zero => node (tag% UndefinedBehaviour.UB014_unsupported_negative_zero) []
  | .UB015_incompatible_redeclaration => node (tag% UndefinedBehaviour.UB015_incompatible_redeclaration) []
  | .UB016 => node (tag% UndefinedBehaviour.UB016) []
  | .UB017_out_of_range_floating_integer_conversion => node (tag% UndefinedBehaviour.UB017_out_of_range_floating_integer_conversion) []
  | .UB018 => node (tag% UndefinedBehaviour.UB018) []
  | .UB019_lvalue_not_an_object => node (tag% UndefinedBehaviour.UB019_lvalue_not_an_object) []
  | .UB020_nonarray_incomplete_lvalue_conversion => node (tag% UndefinedBehaviour.UB020_nonarray_incomplete_lvalue_conversion) []
  | .UB021 => node (tag% UndefinedBehaviour.UB021) []
  | .UB022_register_array_decay => node (tag% UndefinedBehaviour.UB022_register_array_decay) []
  | .UB023 => node (tag% UndefinedBehaviour.UB023) []
  | .UB024_out_of_range_pointer_to_integer_conversion => node (tag% UndefinedBehaviour.UB024_out_of_range_pointer_to_integer_conversion) []
  | .UB025_misaligned_pointer_conversion => node (tag% UndefinedBehaviour.UB025_misaligned_pointer_conversion) []
  | .UB026 => node (tag% UndefinedBehaviour.UB026) []
  | .UB027 => node (tag% UndefinedBehaviour.UB027) []
  | .UB028 => node (tag% UndefinedBehaviour.UB028) []
  | .UB029 => node (tag% UndefinedBehaviour.UB029) []
  | .UB030 => node (tag% UndefinedBehaviour.UB030) []
  | .UB031 => node (tag% UndefinedBehaviour.UB031) []
  | .UB032 => node (tag% UndefinedBehaviour.UB032) []
  | .UB033_modifying_string_literal => node (tag% UndefinedBehaviour.UB033_modifying_string_literal) []
  | .UB034 => node (tag% UndefinedBehaviour.UB034) []
  | .UB035_unsequenced_race => node (tag% UndefinedBehaviour.UB035_unsequenced_race) []
  | .UB036_exceptional_condition => node (tag% UndefinedBehaviour.UB036_exceptional_condition) []
  | .UB037_illtyped_load => node (tag% UndefinedBehaviour.UB037_illtyped_load) []
  | .UB038_number_of_args => node (tag% UndefinedBehaviour.UB038_number_of_args) []
  | .UB039 => node (tag% UndefinedBehaviour.UB039) []
  | .UB040 => node (tag% UndefinedBehaviour.UB040) []
  | .UB041_function_not_compatible => node (tag% UndefinedBehaviour.UB041_function_not_compatible) []
  | .UB042_access_atomic_structUnion_member => node (tag% UndefinedBehaviour.UB042_access_atomic_structUnion_member) []
  | .UB043_indirection_invalid_value => node (tag% UndefinedBehaviour.UB043_indirection_invalid_value) []
  | .UB044 => node (tag% UndefinedBehaviour.UB044) []
  | .UB045a_division_by_zero => node (tag% UndefinedBehaviour.UB045a_division_by_zero) []
  | .UB045b_modulo_by_zero => node (tag% UndefinedBehaviour.UB045b_modulo_by_zero) []
  | .UB045c_quotient_not_representable => node (tag% UndefinedBehaviour.UB045c_quotient_not_representable) []
  | .UB046_array_pointer_outside => node (tag% UndefinedBehaviour.UB046_array_pointer_outside) []
  | .UB047a_array_pointer_addition_beyond_indirection => node (tag% UndefinedBehaviour.UB047a_array_pointer_addition_beyond_indirection) []
  | .UB047b_array_pointer_subtraction_beyond_indirection => node (tag% UndefinedBehaviour.UB047b_array_pointer_subtraction_beyond_indirection) []
  | .UB048_disjoint_array_pointers_subtraction => node (tag% UndefinedBehaviour.UB048_disjoint_array_pointers_subtraction) []
  | .UB049 => node (tag% UndefinedBehaviour.UB049) []
  | .UB050_pointers_subtraction_not_representable => node (tag% UndefinedBehaviour.UB050_pointers_subtraction_not_representable) []
  | .UB051a_negative_shift => node (tag% UndefinedBehaviour.UB051a_negative_shift) []
  | .UB51b_shift_too_large => node (tag% UndefinedBehaviour.UB51b_shift_too_large) []
  | .UB052a_negative_left_shift => node (tag% UndefinedBehaviour.UB052a_negative_left_shift) []
  | .UB052b_non_representable_left_shift => node (tag% UndefinedBehaviour.UB052b_non_representable_left_shift) []
  | .UB053_distinct_aggregate_union_pointer_comparison => node (tag% UndefinedBehaviour.UB053_distinct_aggregate_union_pointer_comparison) []
  | .UB054a_inexactly_overlapping_assignment => node (tag% UndefinedBehaviour.UB054a_inexactly_overlapping_assignment) []
  | .UB054b_incompatible_overlapping_assignment => node (tag% UndefinedBehaviour.UB054b_incompatible_overlapping_assignment) []
  | .UB055_invalid_integer_constant_expression => node (tag% UndefinedBehaviour.UB055_invalid_integer_constant_expression) []
  | .UB056 => node (tag% UndefinedBehaviour.UB056) []
  | .UB057 => node (tag% UndefinedBehaviour.UB057) []
  | .UB058 => node (tag% UndefinedBehaviour.UB058) []
  | .UB059_incomplete_no_linkage_identifier => node (tag% UndefinedBehaviour.UB059_incomplete_no_linkage_identifier) []
  | .UB060_block_scope_function_with_storage_class => node (tag% UndefinedBehaviour.UB060_block_scope_function_with_storage_class) []
  | .UB061_no_named_members => node (tag% UndefinedBehaviour.UB061_no_named_members) []
  | .UB062 => node (tag% UndefinedBehaviour.UB062) []
  | .UB063 => node (tag% UndefinedBehaviour.UB063) []
  | .UB064_modifying_const => node (tag% UndefinedBehaviour.UB064_modifying_const) []
  | .UB065 => node (tag% UndefinedBehaviour.UB065) []
  | .UB066_qualified_function_specification => node (tag% UndefinedBehaviour.UB066_qualified_function_specification) []
  | .UB067 => node (tag% UndefinedBehaviour.UB067) []
  | .UB068 => node (tag% UndefinedBehaviour.UB068) []
  | .UB069 => node (tag% UndefinedBehaviour.UB069) []
  | .UB070_inline_not_defined => node (tag% UndefinedBehaviour.UB070_inline_not_defined) []
  | .UB071_noreturn => node (tag% UndefinedBehaviour.UB071_noreturn) []
  | .UB072_incompatible_alignment_specifiers => node (tag% UndefinedBehaviour.UB072_incompatible_alignment_specifiers) []
  | .UB073 => node (tag% UndefinedBehaviour.UB073) []
  | .UB074 => node (tag% UndefinedBehaviour.UB074) []
  | .UB075 => node (tag% UndefinedBehaviour.UB075) []
  | .UB076 => node (tag% UndefinedBehaviour.UB076) []
  | .UB077 => node (tag% UndefinedBehaviour.UB077) []
  | .UB078_modified_void_parameter => node (tag% UndefinedBehaviour.UB078_modified_void_parameter) []
  | .UB079 => node (tag% UndefinedBehaviour.UB079) []
  | .UB080 => node (tag% UndefinedBehaviour.UB080) []
  | .UB081_scalar_initializer_not_single_expression => node (tag% UndefinedBehaviour.UB081_scalar_initializer_not_single_expression) []
  | .UB082 => node (tag% UndefinedBehaviour.UB082) []
  | .UB083 => node (tag% UndefinedBehaviour.UB083) []
  | .UB084 => node (tag% UndefinedBehaviour.UB084) []
  | .UB085 => node (tag% UndefinedBehaviour.UB085) []
  | .UB086_incomplete_adjusted_parameter => node (tag% UndefinedBehaviour.UB086_incomplete_adjusted_parameter) []
  | .UB087 => node (tag% UndefinedBehaviour.UB087) []
  | .UB088_reached_end_of_function => node (tag% UndefinedBehaviour.UB088_reached_end_of_function) []
  | .UB089_tentative_definition_internal_linkage => node (tag% UndefinedBehaviour.UB089_tentative_definition_internal_linkage) []
  | .UB090 => node (tag% UndefinedBehaviour.UB090) []
  | .UB091 => node (tag% UndefinedBehaviour.UB091) []
  | .UB092 => node (tag% UndefinedBehaviour.UB092) []
  | .UB093 => node (tag% UndefinedBehaviour.UB093) []
  | .UB094 => node (tag% UndefinedBehaviour.UB094) []
  | .UB095 => node (tag% UndefinedBehaviour.UB095) []
  | .UB096 => node (tag% UndefinedBehaviour.UB096) []
  | .UB097 => node (tag% UndefinedBehaviour.UB097) []
  | .UB098 => node (tag% UndefinedBehaviour.UB098) []
  | .UB099 => node (tag% UndefinedBehaviour.UB099) []
  | .UB100 => node (tag% UndefinedBehaviour.UB100) []
  | .UB101 => node (tag% UndefinedBehaviour.UB101) []
  | .UB102 => node (tag% UndefinedBehaviour.UB102) []
  | .UB103 => node (tag% UndefinedBehaviour.UB103) []
  | .UB104 => node (tag% UndefinedBehaviour.UB104) []
  | .UB105 => node (tag% UndefinedBehaviour.UB105) []
  | .UB106 => node (tag% UndefinedBehaviour.UB106) []
  | .UB107 => node (tag% UndefinedBehaviour.UB107) []
  | .UB108 => node (tag% UndefinedBehaviour.UB108) []
  | .UB109 => node (tag% UndefinedBehaviour.UB109) []
  | .UB110 => node (tag% UndefinedBehaviour.UB110) []
  | .UB111_illtyped_assert => node (tag% UndefinedBehaviour.UB111_illtyped_assert) []
  | .UB112 => node (tag% UndefinedBehaviour.UB112) []
  | .UB113 => node (tag% UndefinedBehaviour.UB113) []
  | .UB114 => node (tag% UndefinedBehaviour.UB114) []
  | .UB115 => node (tag% UndefinedBehaviour.UB115) []
  | .UB116 => node (tag% UndefinedBehaviour.UB116) []
  | .UB117 => node (tag% UndefinedBehaviour.UB117) []
  | .UB118 => node (tag% UndefinedBehaviour.UB118) []
  | .UB119 => node (tag% UndefinedBehaviour.UB119) []
  | .UB120 => node (tag% UndefinedBehaviour.UB120) []
  | .UB121 => node (tag% UndefinedBehaviour.UB121) []
  | .UB122 => node (tag% UndefinedBehaviour.UB122) []
  | .UB123 => node (tag% UndefinedBehaviour.UB123) []
  | .UB124 => node (tag% UndefinedBehaviour.UB124) []
  | .UB125 => node (tag% UndefinedBehaviour.UB125) []
  | .UB126 => node (tag% UndefinedBehaviour.UB126) []
  | .UB127 => node (tag% UndefinedBehaviour.UB127) []
  | .UB128 => node (tag% UndefinedBehaviour.UB128) []
  | .UB129 => node (tag% UndefinedBehaviour.UB129) []
  | .UB130 => node (tag% UndefinedBehaviour.UB130) []
  | .UB131 => node (tag% UndefinedBehaviour.UB131) []
  | .UB132 => node (tag% UndefinedBehaviour.UB132) []
  | .UB133 => node (tag% UndefinedBehaviour.UB133) []
  | .UB134 => node (tag% UndefinedBehaviour.UB134) []
  | .UB135 => node (tag% UndefinedBehaviour.UB135) []
  | .UB136 => node (tag% UndefinedBehaviour.UB136) []
  | .UB137 => node (tag% UndefinedBehaviour.UB137) []
  | .UB138 => node (tag% UndefinedBehaviour.UB138) []
  | .UB139 => node (tag% UndefinedBehaviour.UB139) []
  | .UB140 => node (tag% UndefinedBehaviour.UB140) []
  | .UB141 => node (tag% UndefinedBehaviour.UB141) []
  | .UB142 => node (tag% UndefinedBehaviour.UB142) []
  | .UB143 => node (tag% UndefinedBehaviour.UB143) []
  | .UB144 => node (tag% UndefinedBehaviour.UB144) []
  | .UB145 => node (tag% UndefinedBehaviour.UB145) []
  | .UB146 => node (tag% UndefinedBehaviour.UB146) []
  | .UB147 => node (tag% UndefinedBehaviour.UB147) []
  | .UB148 => node (tag% UndefinedBehaviour.UB148) []
  | .UB149 => node (tag% UndefinedBehaviour.UB149) []
  | .UB150 => node (tag% UndefinedBehaviour.UB150) []
  | .UB151 => node (tag% UndefinedBehaviour.UB151) []
  | .UB152 => node (tag% UndefinedBehaviour.UB152) []
  | .UB153a_insufficient_arguments_for_format => node (tag% UndefinedBehaviour.UB153a_insufficient_arguments_for_format) []
  | .UB153b_illtyped_argument_for_format => node (tag% UndefinedBehaviour.UB153b_illtyped_argument_for_format) []
  | .Invalid_format x => node (tag% UndefinedBehaviour.Invalid_format) [str.enc x]
  | .UB154 => node (tag% UndefinedBehaviour.UB154) []
  | .UB155 => node (tag% UndefinedBehaviour.UB155) []
  | .UB156 => node (tag% UndefinedBehaviour.UB156) []
  | .UB157 => node (tag% UndefinedBehaviour.UB157) []
  | .UB158_invalid_length_modifier => node (tag% UndefinedBehaviour.UB158_invalid_length_modifier) []
  | .UB159 => node (tag% UndefinedBehaviour.UB159) []
  | .UB160 => node (tag% UndefinedBehaviour.UB160) []
  | .UB161 => node (tag% UndefinedBehaviour.UB161) []
  | .UB162 => node (tag% UndefinedBehaviour.UB162) []
  | .UB163 => node (tag% UndefinedBehaviour.UB163) []
  | .UB164 => node (tag% UndefinedBehaviour.UB164) []
  | .UB165 => node (tag% UndefinedBehaviour.UB165) []
  | .UB166 => node (tag% UndefinedBehaviour.UB166) []
  | .UB167 => node (tag% UndefinedBehaviour.UB167) []
  | .UB168 => node (tag% UndefinedBehaviour.UB168) []
  | .UB169 => node (tag% UndefinedBehaviour.UB169) []
  | .UB170 => node (tag% UndefinedBehaviour.UB170) []
  | .UB171 => node (tag% UndefinedBehaviour.UB171) []
  | .UB172 => node (tag% UndefinedBehaviour.UB172) []
  | .UB173 => node (tag% UndefinedBehaviour.UB173) []
  | .UB174 => node (tag% UndefinedBehaviour.UB174) []
  | .UB175 => node (tag% UndefinedBehaviour.UB175) []
  | .UB176 => node (tag% UndefinedBehaviour.UB176) []
  | .UB177 => node (tag% UndefinedBehaviour.UB177) []
  | .UB178 => node (tag% UndefinedBehaviour.UB178) []
  | .UB179a_non_matching_allocation_free => node (tag% UndefinedBehaviour.UB179a_non_matching_allocation_free) []
  | .UB179b_dead_allocation_free => node (tag% UndefinedBehaviour.UB179b_dead_allocation_free) []
  | .UB179c_non_matching_allocation_realloc => node (tag% UndefinedBehaviour.UB179c_non_matching_allocation_realloc) []
  | .UB179d_dead_allocation_realloc => node (tag% UndefinedBehaviour.UB179d_dead_allocation_realloc) []
  | .UB180 => node (tag% UndefinedBehaviour.UB180) []
  | .UB181 => node (tag% UndefinedBehaviour.UB181) []
  | .UB182 => node (tag% UndefinedBehaviour.UB182) []
  | .UB183 => node (tag% UndefinedBehaviour.UB183) []
  | .UB184 => node (tag% UndefinedBehaviour.UB184) []
  | .UB185 => node (tag% UndefinedBehaviour.UB185) []
  | .UB186 => node (tag% UndefinedBehaviour.UB186) []
  | .UB187 => node (tag% UndefinedBehaviour.UB187) []
  | .UB188 => node (tag% UndefinedBehaviour.UB188) []
  | .UB189 => node (tag% UndefinedBehaviour.UB189) []
  | .UB190 => node (tag% UndefinedBehaviour.UB190) []
  | .UB191 => node (tag% UndefinedBehaviour.UB191) []
  | .UB192 => node (tag% UndefinedBehaviour.UB192) []
  | .UB193 => node (tag% UndefinedBehaviour.UB193) []
  | .UB194 => node (tag% UndefinedBehaviour.UB194) []
  | .UB195 => node (tag% UndefinedBehaviour.UB195) []
  | .UB196 => node (tag% UndefinedBehaviour.UB196) []
  | .UB197 => node (tag% UndefinedBehaviour.UB197) []
  | .UB198 => node (tag% UndefinedBehaviour.UB198) []
  | .UB199 => node (tag% UndefinedBehaviour.UB199) []
  | .UB200 => node (tag% UndefinedBehaviour.UB200) []
  | .UB201 => node (tag% UndefinedBehaviour.UB201) []
  | .UB202 => node (tag% UndefinedBehaviour.UB202) []
  | .UB203 => node (tag% UndefinedBehaviour.UB203) []
  | .UB204_illtyped_Static_assert => node (tag% UndefinedBehaviour.UB204_illtyped_Static_assert) []
  | .UB205_atomic_store_memorder => node (tag% UndefinedBehaviour.UB205_atomic_store_memorder) []
  | .UB206_atomic_load_memorder => node (tag% UndefinedBehaviour.UB206_atomic_load_memorder) []
  | .UB207_atomic_compare_exchange_memorder => node (tag% UndefinedBehaviour.UB207_atomic_compare_exchange_memorder) []
  | .UB_CERB001_integer_to_dead_pointer => node (tag% UndefinedBehaviour.UB_CERB001_integer_to_dead_pointer) []
  | .UB_CERB002a_out_of_bound_load => node (tag% UndefinedBehaviour.UB_CERB002a_out_of_bound_load) []
  | .UB_CERB002b_out_of_bound_store => node (tag% UndefinedBehaviour.UB_CERB002b_out_of_bound_store) []
  | .UB_CERB002c_out_of_bound_free => node (tag% UndefinedBehaviour.UB_CERB002c_out_of_bound_free) []
  | .UB_CERB002d_out_of_bound_realloc => node (tag% UndefinedBehaviour.UB_CERB002d_out_of_bound_realloc) []
  | .UB_CERB003_invalid_function_pointer => node (tag% UndefinedBehaviour.UB_CERB003_invalid_function_pointer) []
  | .UB_CHERI_InvalidCap => node (tag% UndefinedBehaviour.UB_CHERI_InvalidCap) []
  | .UB_CHERI_InsufficientPermissions => node (tag% UndefinedBehaviour.UB_CHERI_InsufficientPermissions) []
  | .UB_CHERI_BoundsViolation => node (tag% UndefinedBehaviour.UB_CHERI_BoundsViolation) []
  | .UB_CHERI_UndefinedTag => node (tag% UndefinedBehaviour.UB_CHERI_UndefinedTag) []
  | .UB_CHERI_ZeroLength => node (tag% UndefinedBehaviour.UB_CHERI_ZeroLength) []
  | .UB_CERB004_unspecified x => node (tag% UndefinedBehaviour.UB_CERB004_unspecified) [unspecifiedUbContext.enc x]
  | .UB_CERB005_free_nullptr => node (tag% UndefinedBehaviour.UB_CERB005_free_nullptr) []

/-- The nullary constructors, in declaration order. -/
def undefinedBehaviourLeaves : List (String × UndefinedBehaviour) :=
  [leafPair% UndefinedBehaviour.UB_unspecified_lvalue,
   leafPair% UndefinedBehaviour.UB001,
   leafPair% UndefinedBehaviour.UB002,
   leafPair% UndefinedBehaviour.UB003,
   leafPair% UndefinedBehaviour.UB004a_incorrect_main_return_type,
   leafPair% UndefinedBehaviour.UB004b_incorrect_main_argument1,
   leafPair% UndefinedBehaviour.UB004c_incorrect_main_argument2,
   leafPair% UndefinedBehaviour.UB004d_main_not_function,
   leafPair% UndefinedBehaviour.UB005_data_race,
   leafPair% UndefinedBehaviour.UB006,
   leafPair% UndefinedBehaviour.UB007,
   leafPair% UndefinedBehaviour.UB008_multiple_linkage,
   leafPair% UndefinedBehaviour.UB009_outside_lifetime,
   leafPair% UndefinedBehaviour.UB010_pointer_to_dead_object,
   leafPair% UndefinedBehaviour.UB011_use_indeterminate_automatic_object,
   leafPair% UndefinedBehaviour.UB_modifying_temporary_lifetime,
   leafPair% UndefinedBehaviour.UB012_lvalue_read_trap_representation,
   leafPair% UndefinedBehaviour.UB013_lvalue_side_effect_trap_representation,
   leafPair% UndefinedBehaviour.UB014_unsupported_negative_zero,
   leafPair% UndefinedBehaviour.UB015_incompatible_redeclaration,
   leafPair% UndefinedBehaviour.UB016,
   leafPair% UndefinedBehaviour.UB017_out_of_range_floating_integer_conversion,
   leafPair% UndefinedBehaviour.UB018,
   leafPair% UndefinedBehaviour.UB019_lvalue_not_an_object,
   leafPair% UndefinedBehaviour.UB020_nonarray_incomplete_lvalue_conversion,
   leafPair% UndefinedBehaviour.UB021,
   leafPair% UndefinedBehaviour.UB022_register_array_decay,
   leafPair% UndefinedBehaviour.UB023,
   leafPair% UndefinedBehaviour.UB024_out_of_range_pointer_to_integer_conversion,
   leafPair% UndefinedBehaviour.UB025_misaligned_pointer_conversion,
   leafPair% UndefinedBehaviour.UB026,
   leafPair% UndefinedBehaviour.UB027,
   leafPair% UndefinedBehaviour.UB028,
   leafPair% UndefinedBehaviour.UB029,
   leafPair% UndefinedBehaviour.UB030,
   leafPair% UndefinedBehaviour.UB031,
   leafPair% UndefinedBehaviour.UB032,
   leafPair% UndefinedBehaviour.UB033_modifying_string_literal,
   leafPair% UndefinedBehaviour.UB034,
   leafPair% UndefinedBehaviour.UB035_unsequenced_race,
   leafPair% UndefinedBehaviour.UB036_exceptional_condition,
   leafPair% UndefinedBehaviour.UB037_illtyped_load,
   leafPair% UndefinedBehaviour.UB038_number_of_args,
   leafPair% UndefinedBehaviour.UB039,
   leafPair% UndefinedBehaviour.UB040,
   leafPair% UndefinedBehaviour.UB041_function_not_compatible,
   leafPair% UndefinedBehaviour.UB042_access_atomic_structUnion_member,
   leafPair% UndefinedBehaviour.UB043_indirection_invalid_value,
   leafPair% UndefinedBehaviour.UB044,
   leafPair% UndefinedBehaviour.UB045a_division_by_zero,
   leafPair% UndefinedBehaviour.UB045b_modulo_by_zero,
   leafPair% UndefinedBehaviour.UB045c_quotient_not_representable,
   leafPair% UndefinedBehaviour.UB046_array_pointer_outside,
   leafPair% UndefinedBehaviour.UB047a_array_pointer_addition_beyond_indirection,
   leafPair% UndefinedBehaviour.UB047b_array_pointer_subtraction_beyond_indirection,
   leafPair% UndefinedBehaviour.UB048_disjoint_array_pointers_subtraction,
   leafPair% UndefinedBehaviour.UB049,
   leafPair% UndefinedBehaviour.UB050_pointers_subtraction_not_representable,
   leafPair% UndefinedBehaviour.UB051a_negative_shift,
   leafPair% UndefinedBehaviour.UB51b_shift_too_large,
   leafPair% UndefinedBehaviour.UB052a_negative_left_shift,
   leafPair% UndefinedBehaviour.UB052b_non_representable_left_shift,
   leafPair% UndefinedBehaviour.UB053_distinct_aggregate_union_pointer_comparison,
   leafPair% UndefinedBehaviour.UB054a_inexactly_overlapping_assignment,
   leafPair% UndefinedBehaviour.UB054b_incompatible_overlapping_assignment,
   leafPair% UndefinedBehaviour.UB055_invalid_integer_constant_expression,
   leafPair% UndefinedBehaviour.UB056,
   leafPair% UndefinedBehaviour.UB057,
   leafPair% UndefinedBehaviour.UB058,
   leafPair% UndefinedBehaviour.UB059_incomplete_no_linkage_identifier,
   leafPair% UndefinedBehaviour.UB060_block_scope_function_with_storage_class,
   leafPair% UndefinedBehaviour.UB061_no_named_members,
   leafPair% UndefinedBehaviour.UB062,
   leafPair% UndefinedBehaviour.UB063,
   leafPair% UndefinedBehaviour.UB064_modifying_const,
   leafPair% UndefinedBehaviour.UB065,
   leafPair% UndefinedBehaviour.UB066_qualified_function_specification,
   leafPair% UndefinedBehaviour.UB067,
   leafPair% UndefinedBehaviour.UB068,
   leafPair% UndefinedBehaviour.UB069,
   leafPair% UndefinedBehaviour.UB070_inline_not_defined,
   leafPair% UndefinedBehaviour.UB071_noreturn,
   leafPair% UndefinedBehaviour.UB072_incompatible_alignment_specifiers,
   leafPair% UndefinedBehaviour.UB073,
   leafPair% UndefinedBehaviour.UB074,
   leafPair% UndefinedBehaviour.UB075,
   leafPair% UndefinedBehaviour.UB076,
   leafPair% UndefinedBehaviour.UB077,
   leafPair% UndefinedBehaviour.UB078_modified_void_parameter,
   leafPair% UndefinedBehaviour.UB079,
   leafPair% UndefinedBehaviour.UB080,
   leafPair% UndefinedBehaviour.UB081_scalar_initializer_not_single_expression,
   leafPair% UndefinedBehaviour.UB082,
   leafPair% UndefinedBehaviour.UB083,
   leafPair% UndefinedBehaviour.UB084,
   leafPair% UndefinedBehaviour.UB085,
   leafPair% UndefinedBehaviour.UB086_incomplete_adjusted_parameter,
   leafPair% UndefinedBehaviour.UB087,
   leafPair% UndefinedBehaviour.UB088_reached_end_of_function,
   leafPair% UndefinedBehaviour.UB089_tentative_definition_internal_linkage,
   leafPair% UndefinedBehaviour.UB090,
   leafPair% UndefinedBehaviour.UB091,
   leafPair% UndefinedBehaviour.UB092,
   leafPair% UndefinedBehaviour.UB093,
   leafPair% UndefinedBehaviour.UB094,
   leafPair% UndefinedBehaviour.UB095,
   leafPair% UndefinedBehaviour.UB096,
   leafPair% UndefinedBehaviour.UB097,
   leafPair% UndefinedBehaviour.UB098,
   leafPair% UndefinedBehaviour.UB099,
   leafPair% UndefinedBehaviour.UB100,
   leafPair% UndefinedBehaviour.UB101,
   leafPair% UndefinedBehaviour.UB102,
   leafPair% UndefinedBehaviour.UB103,
   leafPair% UndefinedBehaviour.UB104,
   leafPair% UndefinedBehaviour.UB105,
   leafPair% UndefinedBehaviour.UB106,
   leafPair% UndefinedBehaviour.UB107,
   leafPair% UndefinedBehaviour.UB108,
   leafPair% UndefinedBehaviour.UB109,
   leafPair% UndefinedBehaviour.UB110,
   leafPair% UndefinedBehaviour.UB111_illtyped_assert,
   leafPair% UndefinedBehaviour.UB112,
   leafPair% UndefinedBehaviour.UB113,
   leafPair% UndefinedBehaviour.UB114,
   leafPair% UndefinedBehaviour.UB115,
   leafPair% UndefinedBehaviour.UB116,
   leafPair% UndefinedBehaviour.UB117,
   leafPair% UndefinedBehaviour.UB118,
   leafPair% UndefinedBehaviour.UB119,
   leafPair% UndefinedBehaviour.UB120,
   leafPair% UndefinedBehaviour.UB121,
   leafPair% UndefinedBehaviour.UB122,
   leafPair% UndefinedBehaviour.UB123,
   leafPair% UndefinedBehaviour.UB124,
   leafPair% UndefinedBehaviour.UB125,
   leafPair% UndefinedBehaviour.UB126,
   leafPair% UndefinedBehaviour.UB127,
   leafPair% UndefinedBehaviour.UB128,
   leafPair% UndefinedBehaviour.UB129,
   leafPair% UndefinedBehaviour.UB130,
   leafPair% UndefinedBehaviour.UB131,
   leafPair% UndefinedBehaviour.UB132,
   leafPair% UndefinedBehaviour.UB133,
   leafPair% UndefinedBehaviour.UB134,
   leafPair% UndefinedBehaviour.UB135,
   leafPair% UndefinedBehaviour.UB136,
   leafPair% UndefinedBehaviour.UB137,
   leafPair% UndefinedBehaviour.UB138,
   leafPair% UndefinedBehaviour.UB139,
   leafPair% UndefinedBehaviour.UB140,
   leafPair% UndefinedBehaviour.UB141,
   leafPair% UndefinedBehaviour.UB142,
   leafPair% UndefinedBehaviour.UB143,
   leafPair% UndefinedBehaviour.UB144,
   leafPair% UndefinedBehaviour.UB145,
   leafPair% UndefinedBehaviour.UB146,
   leafPair% UndefinedBehaviour.UB147,
   leafPair% UndefinedBehaviour.UB148,
   leafPair% UndefinedBehaviour.UB149,
   leafPair% UndefinedBehaviour.UB150,
   leafPair% UndefinedBehaviour.UB151,
   leafPair% UndefinedBehaviour.UB152,
   leafPair% UndefinedBehaviour.UB153a_insufficient_arguments_for_format,
   leafPair% UndefinedBehaviour.UB153b_illtyped_argument_for_format,
   leafPair% UndefinedBehaviour.UB154,
   leafPair% UndefinedBehaviour.UB155,
   leafPair% UndefinedBehaviour.UB156,
   leafPair% UndefinedBehaviour.UB157,
   leafPair% UndefinedBehaviour.UB158_invalid_length_modifier,
   leafPair% UndefinedBehaviour.UB159,
   leafPair% UndefinedBehaviour.UB160,
   leafPair% UndefinedBehaviour.UB161,
   leafPair% UndefinedBehaviour.UB162,
   leafPair% UndefinedBehaviour.UB163,
   leafPair% UndefinedBehaviour.UB164,
   leafPair% UndefinedBehaviour.UB165,
   leafPair% UndefinedBehaviour.UB166,
   leafPair% UndefinedBehaviour.UB167,
   leafPair% UndefinedBehaviour.UB168,
   leafPair% UndefinedBehaviour.UB169,
   leafPair% UndefinedBehaviour.UB170,
   leafPair% UndefinedBehaviour.UB171,
   leafPair% UndefinedBehaviour.UB172,
   leafPair% UndefinedBehaviour.UB173,
   leafPair% UndefinedBehaviour.UB174,
   leafPair% UndefinedBehaviour.UB175,
   leafPair% UndefinedBehaviour.UB176,
   leafPair% UndefinedBehaviour.UB177,
   leafPair% UndefinedBehaviour.UB178,
   leafPair% UndefinedBehaviour.UB179a_non_matching_allocation_free,
   leafPair% UndefinedBehaviour.UB179b_dead_allocation_free,
   leafPair% UndefinedBehaviour.UB179c_non_matching_allocation_realloc,
   leafPair% UndefinedBehaviour.UB179d_dead_allocation_realloc,
   leafPair% UndefinedBehaviour.UB180,
   leafPair% UndefinedBehaviour.UB181,
   leafPair% UndefinedBehaviour.UB182,
   leafPair% UndefinedBehaviour.UB183,
   leafPair% UndefinedBehaviour.UB184,
   leafPair% UndefinedBehaviour.UB185,
   leafPair% UndefinedBehaviour.UB186,
   leafPair% UndefinedBehaviour.UB187,
   leafPair% UndefinedBehaviour.UB188,
   leafPair% UndefinedBehaviour.UB189,
   leafPair% UndefinedBehaviour.UB190,
   leafPair% UndefinedBehaviour.UB191,
   leafPair% UndefinedBehaviour.UB192,
   leafPair% UndefinedBehaviour.UB193,
   leafPair% UndefinedBehaviour.UB194,
   leafPair% UndefinedBehaviour.UB195,
   leafPair% UndefinedBehaviour.UB196,
   leafPair% UndefinedBehaviour.UB197,
   leafPair% UndefinedBehaviour.UB198,
   leafPair% UndefinedBehaviour.UB199,
   leafPair% UndefinedBehaviour.UB200,
   leafPair% UndefinedBehaviour.UB201,
   leafPair% UndefinedBehaviour.UB202,
   leafPair% UndefinedBehaviour.UB203,
   leafPair% UndefinedBehaviour.UB204_illtyped_Static_assert,
   leafPair% UndefinedBehaviour.UB205_atomic_store_memorder,
   leafPair% UndefinedBehaviour.UB206_atomic_load_memorder,
   leafPair% UndefinedBehaviour.UB207_atomic_compare_exchange_memorder,
   leafPair% UndefinedBehaviour.UB_CERB001_integer_to_dead_pointer,
   leafPair% UndefinedBehaviour.UB_CERB002a_out_of_bound_load,
   leafPair% UndefinedBehaviour.UB_CERB002b_out_of_bound_store,
   leafPair% UndefinedBehaviour.UB_CERB002c_out_of_bound_free,
   leafPair% UndefinedBehaviour.UB_CERB002d_out_of_bound_realloc,
   leafPair% UndefinedBehaviour.UB_CERB003_invalid_function_pointer,
   leafPair% UndefinedBehaviour.UB_CHERI_InvalidCap,
   leafPair% UndefinedBehaviour.UB_CHERI_InsufficientPermissions,
   leafPair% UndefinedBehaviour.UB_CHERI_BoundsViolation,
   leafPair% UndefinedBehaviour.UB_CHERI_UndefinedTag,
   leafPair% UndefinedBehaviour.UB_CHERI_ZeroLength,
   leafPair% UndefinedBehaviour.UB_CERB005_free_nullptr]

def undefinedBehaviour : Codec UndefinedBehaviour := ofLeaves encodeUndefinedBehaviour
  undefinedBehaviourLeaves
  [alt% UndefinedBehaviour.DUMMY str,
   alt% UndefinedBehaviour.UB_std_omission undefinedByOmission,
   alt% UndefinedBehaviour.Invalid_format str,
   alt% UndefinedBehaviour.UB_CERB004_unspecified unspecifiedUbContext]
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

@[simp] theorem undefinedBehaviour_budget : undefinedBehaviour.budget = none := by
  simp [undefinedBehaviour, unspecifiedUbContext, undefinedByOmission]

example : undefinedBehaviour.dec (node "UB045a_division_by_zero" []) =
    some .UB045a_division_by_zero := rfl
example : undefinedBehaviour.dec (node "UB045b_modulo_by_zero" []) =
    some .UB045b_modulo_by_zero := rfl

end Silmaril.Cerberus.Codec
