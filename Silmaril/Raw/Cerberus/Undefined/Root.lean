module

/-! # Cerberus undefined behaviours

The undefined-behaviour catalogue types of Cerberus's
`frontend/model/undefined.lem` at commit
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. `UndefinedBehaviour` numbers ISO C
Annex J.2 entries (`UB001` …), with Cerberus-specific (`UB_CERB…`) and CHERI
entries. The constructor list was extracted mechanically from the Lem source; the
four argument types were written by hand. The printing and ISO-citation functions
are not ported.

Unlike the rest of the port, these constructors keep their Cerberus names: they
are catalogue identifiers, and Cerberus reports undefined behaviour by exactly
these names (for example `UB045a_division_by_zero`).
-/

@[expose] public section

namespace Silmaril.Cerberus

/-- Operators whose operand evaluated to an unspecified value. -/
inductive UnspecifiedUbContext where
  | UB_unspec_equality_ptr_vs_NULL
  | UB_unspec_equality_both_arith_or_ptr
  | UB_unspec_pointer_add
  | UB_unspec_pointer_sub
  | UB_unspec_conditional
  | UB_unspec_copy_alloc_id
  | UB_unspec_rvalue_memberof
  | UB_unspec_memberofptr
  | UB_unspec_do
  deriving DecidableEq, Repr

/-- Behaviours the standard leaves undefined by omission. -/
inductive UndefinedByOmission where
  | UB_OMIT_memcpy_non_object
  | UB_OMIT_memcpy_out_of_bound
  deriving DecidableEq, Repr

/-- C undefined behaviours. -/
inductive UndefinedBehaviour where
  | DUMMY : String → UndefinedBehaviour
  | UB_unspecified_lvalue
  | UB_std_omission : UndefinedByOmission → UndefinedBehaviour
  | UB001
  | UB002
  | UB003
  | UB004a_incorrect_main_return_type
  | UB004b_incorrect_main_argument1
  | UB004c_incorrect_main_argument2
  | UB004d_main_not_function
  | UB005_data_race
  | UB006
  | UB007
  | UB008_multiple_linkage
  | UB009_outside_lifetime
  | UB010_pointer_to_dead_object
  | UB011_use_indeterminate_automatic_object
  | UB_modifying_temporary_lifetime
  | UB012_lvalue_read_trap_representation
  | UB013_lvalue_side_effect_trap_representation
  | UB014_unsupported_negative_zero
  | UB015_incompatible_redeclaration
  | UB016
  | UB017_out_of_range_floating_integer_conversion
  | UB018
  | UB019_lvalue_not_an_object
  | UB020_nonarray_incomplete_lvalue_conversion
  | UB021
  | UB022_register_array_decay
  | UB023
  | UB024_out_of_range_pointer_to_integer_conversion
  | UB025_misaligned_pointer_conversion
  | UB026
  | UB027
  | UB028
  | UB029
  | UB030
  | UB031
  | UB032
  | UB033_modifying_string_literal
  | UB034
  | UB035_unsequenced_race
  | UB036_exceptional_condition
  | UB037_illtyped_load
  | UB038_number_of_args
  | UB039
  | UB040
  | UB041_function_not_compatible
  | UB042_access_atomic_structUnion_member
  | UB043_indirection_invalid_value
  | UB044
  | UB045a_division_by_zero
  | UB045b_modulo_by_zero
  | UB045c_quotient_not_representable
  | UB046_array_pointer_outside
  | UB047a_array_pointer_addition_beyond_indirection
  | UB047b_array_pointer_subtraction_beyond_indirection
  | UB048_disjoint_array_pointers_subtraction
  | UB049
  | UB050_pointers_subtraction_not_representable
  | UB051a_negative_shift
  | UB51b_shift_too_large
  | UB052a_negative_left_shift
  | UB052b_non_representable_left_shift
  | UB053_distinct_aggregate_union_pointer_comparison
  | UB054a_inexactly_overlapping_assignment
  | UB054b_incompatible_overlapping_assignment
  | UB055_invalid_integer_constant_expression
  | UB056
  | UB057
  | UB058
  | UB059_incomplete_no_linkage_identifier
  | UB060_block_scope_function_with_storage_class
  | UB061_no_named_members
  | UB062
  | UB063
  | UB064_modifying_const
  | UB065
  | UB066_qualified_function_specification
  | UB067
  | UB068
  | UB069
  | UB070_inline_not_defined
  | UB071_noreturn
  | UB072_incompatible_alignment_specifiers
  | UB073
  | UB074
  | UB075
  | UB076
  | UB077
  | UB078_modified_void_parameter
  | UB079
  | UB080
  | UB081_scalar_initializer_not_single_expression
  | UB082
  | UB083
  | UB084
  | UB085
  | UB086_incomplete_adjusted_parameter
  | UB087
  | UB088_reached_end_of_function
  | UB089_tentative_definition_internal_linkage
  | UB090
  | UB091
  | UB092
  | UB093
  | UB094
  | UB095
  | UB096
  | UB097
  | UB098
  | UB099
  | UB100
  | UB101
  | UB102
  | UB103
  | UB104
  | UB105
  | UB106
  | UB107
  | UB108
  | UB109
  | UB110
  | UB111_illtyped_assert
  | UB112
  | UB113
  | UB114
  | UB115
  | UB116
  | UB117
  | UB118
  | UB119
  | UB120
  | UB121
  | UB122
  | UB123
  | UB124
  | UB125
  | UB126
  | UB127
  | UB128
  | UB129
  | UB130
  | UB131
  | UB132
  | UB133
  | UB134
  | UB135
  | UB136
  | UB137
  | UB138
  | UB139
  | UB140
  | UB141
  | UB142
  | UB143
  | UB144
  | UB145
  | UB146
  | UB147
  | UB148
  | UB149
  | UB150
  | UB151
  | UB152
  | UB153a_insufficient_arguments_for_format
  | UB153b_illtyped_argument_for_format
  | Invalid_format : String → UndefinedBehaviour
  | UB154
  | UB155
  | UB156
  | UB157
  | UB158_invalid_length_modifier
  | UB159
  | UB160
  | UB161
  | UB162
  | UB163
  | UB164
  | UB165
  | UB166
  | UB167
  | UB168
  | UB169
  | UB170
  | UB171
  | UB172
  | UB173
  | UB174
  | UB175
  | UB176
  | UB177
  | UB178
  | UB179a_non_matching_allocation_free
  | UB179b_dead_allocation_free
  | UB179c_non_matching_allocation_realloc
  | UB179d_dead_allocation_realloc
  | UB180
  | UB181
  | UB182
  | UB183
  | UB184
  | UB185
  | UB186
  | UB187
  | UB188
  | UB189
  | UB190
  | UB191
  | UB192
  | UB193
  | UB194
  | UB195
  | UB196
  | UB197
  | UB198
  | UB199
  | UB200
  | UB201
  | UB202
  | UB203
  | UB204_illtyped_Static_assert
  | UB205_atomic_store_memorder
  | UB206_atomic_load_memorder
  | UB207_atomic_compare_exchange_memorder
  | UB_CERB001_integer_to_dead_pointer
  | UB_CERB002a_out_of_bound_load
  | UB_CERB002b_out_of_bound_store
  | UB_CERB002c_out_of_bound_free
  | UB_CERB002d_out_of_bound_realloc
  | UB_CERB003_invalid_function_pointer
  | UB_CHERI_InvalidCap
  | UB_CHERI_InsufficientPermissions
  | UB_CHERI_BoundsViolation
  | UB_CHERI_UndefinedTag
  | UB_CHERI_ZeroLength
  | UB_CERB004_unspecified : UnspecifiedUbContext → UndefinedBehaviour
  | UB_CERB005_free_nullptr
  deriving DecidableEq, Repr

end Silmaril.Cerberus
