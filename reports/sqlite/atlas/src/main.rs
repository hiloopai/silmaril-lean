#![allow(non_upper_case_globals)] // CIndex constant spellings in match patterns.
mod clang;

use clang::{children, extent, kind_name, loc, name, spelling_loc, type_name, Location};
use clang_sys::*;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::error::Error;
use std::io::{self, Write};

const UNIT: &str = "sqlite3.c";

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct Declaration {
    name: String,
    kind: String,
    location: Option<Location>,
}

impl Declaration {
    fn of(cursor: CXCursor) -> Option<Self> {
        (unsafe { clang_Cursor_isNull(cursor) } == 0).then(|| Self {
            name: name(cursor),
            kind: kind_name(cursor.kind),
            location: loc(cursor),
        })
    }
}

#[derive(Serialize)]
struct Parameter {
    name: String,
    c_type: String,
    boundary_shape: &'static str,
    pointee_declared_const: Option<bool>,
}

impl Parameter {
    fn of(cursor: CXCursor, ty: CXType) -> Self {
        let (boundary_shape, pointee_declared_const) = unsafe {
            let canonical = clang_getCanonicalType(ty);
            if canonical.kind == CXType_Pointer {
                let pointee = clang_getPointeeType(canonical);
                let shape = match pointee.kind {
                    CXType_FunctionProto | CXType_FunctionNoProto => "callback",
                    CXType_Char_U | CXType_Char_S | CXType_SChar | CXType_UChar => "byte_pointer",
                    CXType_Record => "record_pointer",
                    CXType_Void => "opaque_pointer",
                    _ => "other_pointer",
                };
                (shape, (shape != "callback").then(|| const_object(pointee)))
            } else {
                ("value", None)
            }
        };
        Self {
            name: name(cursor),
            c_type: type_name(ty),
            boundary_shape,
            pointee_declared_const,
        }
    }
}

#[derive(Serialize)]
struct Function {
    name: String,
    definition: Location,
    spelling: Option<Location>,
    extent: Option<[Location; 2]>,
    body: Option<[Location; 2]>,
    linkage: String,
    storage: String,
    result_type: String,
    parameters: Vec<Parameter>,
    declaration_locations: Vec<Location>,
    #[serde(flatten)]
    facts: Facts,
}

#[derive(Default, Serialize)]
struct Facts {
    features: BTreeMap<&'static str, u32>,
    type_shapes: BTreeSet<&'static str>,
    type_declarations: BTreeSet<Declaration>,
    record_layouts: BTreeSet<String>,
    nonlocal_objects: BTreeMap<String, Nonlocal>,
    function_mentions: BTreeSet<Declaration>,
    calls: Vec<Call>,
    #[serde(skip)]
    seen_types: HashSet<(CXTypeKind, usize, usize)>,
}

#[derive(Serialize)]
struct Nonlocal {
    declaration: Declaration,
    storage: &'static str,
    declared_const: bool,
    references: u32,
}

#[derive(Serialize)]
struct Call {
    site: Option<Location>,
    callee: Option<Declaration>,
    callee_expression: Option<String>,
    direct_definition: Option<Location>,
    indirect: bool,
}

#[derive(Serialize)]
struct Layout {
    declaration: Declaration,
    size_bytes: Option<i64>,
    alignment_bytes: Option<i64>,
    fields: Vec<Field>,
}

#[derive(Serialize)]
struct Field {
    name: String,
    c_type: String,
    bit_offset: Option<i64>,
    bit_width: Option<i32>,
}

#[derive(Serialize)]
struct MacroUse {
    name: String,
    site: Location,
    declared_at: Option<Location>,
}

#[derive(Serialize)]
struct Include {
    name: String,
    site: Location,
    resolved_file: Option<String>,
}

#[derive(Serialize)]
struct Unit {
    compiler: String,
    functions: Vec<Function>,
    locationless_function_definitions: Vec<String>,
    system_function_definitions: Vec<Declaration>,
    located_function_declarations: usize,
    record_layouts: BTreeMap<String, Layout>,
    macros: Vec<MacroUse>,
    includes: Vec<Include>,
}

#[derive(Serialize)]
struct DebugDefinition {
    name: String,
    definition: Location,
    body: Option<[Location; 2]>,
}

#[derive(Default, Serialize)]
struct DebugProbes {
    functions: Vec<DebugDefinition>,
    macros: Vec<MacroUse>,
}

fn increment(features: &mut BTreeMap<&'static str, u32>, key: &'static str) {
    *features.entry(key).or_default() += 1;
}

fn callee_designator(mut expression: CXCursor) -> CXCursor {
    loop {
        let transparent = matches!(expression.kind, CXCursor_ParenExpr | CXCursor_UnexposedExpr)
            || (expression.kind == CXCursor_UnaryOperator
                && matches!(
                    unsafe { clang_getCursorUnaryOperatorKind(expression) },
                    CXUnaryOperator_AddrOf | CXUnaryOperator_Deref
                ));
        if !transparent {
            return expression;
        }
        let children = children(expression);
        let [child] = children.as_slice() else {
            return expression;
        };
        expression = *child;
    }
}

fn layout(cursor: CXCursor, ty: CXType) -> Layout {
    let fields = children(cursor)
        .into_iter()
        .filter(|field| field.kind == CXCursor_FieldDecl)
        .map(|field| unsafe {
            let bit_offset = clang_Cursor_getOffsetOfField(field);
            let bit_width = clang_getFieldDeclBitWidth(field);
            Field {
                name: name(field),
                c_type: type_name(clang_getCursorType(field)),
                bit_offset: (bit_offset >= 0).then_some(bit_offset),
                bit_width: (bit_width >= 0).then_some(bit_width),
            }
        })
        .collect();
    let (size, align) = unsafe { (clang_Type_getSizeOf(ty), clang_Type_getAlignOf(ty)) };
    Layout {
        declaration: Declaration::of(cursor).expect("a record declaration"),
        size_bytes: (size >= 0).then_some(size),
        alignment_bytes: (align >= 0).then_some(align),
        fields,
    }
}

impl Facts {
    fn record_type(&mut self, ty: CXType, layouts: &mut BTreeMap<String, Layout>) {
        if ty.kind == CXType_Invalid
            || !self
                .seen_types
                .insert((ty.kind, ty.data[0] as usize, ty.data[1] as usize))
        {
            return;
        }
        unsafe {
            let decl = clang_getTypeDeclaration(ty);
            match ty.kind {
                CXType_Typedef | CXType_Elaborated => {
                    if ty.kind == CXType_Typedef {
                        self.type_declarations.extend(Declaration::of(decl));
                        self.record_type(clang_getTypedefDeclUnderlyingType(decl), layouts);
                    } else {
                        self.record_type(clang_Type_getNamedType(ty), layouts);
                    }
                }
                CXType_Pointer | CXType_BlockPointer => {
                    let pointee = clang_getPointeeType(ty);
                    self.type_shapes.insert("pointer");
                    self.record_element_shape(pointee, layouts);
                }
                CXType_ConstantArray
                | CXType_IncompleteArray
                | CXType_VariableArray
                | CXType_DependentSizedArray
                | CXType_Vector
                | CXType_ExtVector => {
                    self.type_shapes.insert("array_or_vector");
                    if ty.kind == CXType_VariableArray {
                        self.type_shapes.insert("variable_length_array");
                    }
                    self.record_element_shape(clang_getElementType(ty), layouts);
                }
                CXType_Record => {
                    self.type_shapes.insert("record");
                    if decl.kind == CXCursor_UnionDecl {
                        self.type_shapes.insert("union");
                    }
                    let definition = clang_getCursorDefinition(decl);
                    let best = if clang_Cursor_isNull(definition) == 0 {
                        definition
                    } else {
                        decl
                    };
                    self.type_declarations.extend(Declaration::of(best));
                    if let Some(site) = loc(best) {
                        let id = format!("{}:{}:{}", site.file, site.line, site.column);
                        layouts
                            .entry(id.clone())
                            .or_insert_with(|| layout(best, ty));
                        self.record_layouts.insert(id);
                    }
                }
                CXType_Enum => {
                    self.type_shapes.insert("enum");
                    self.type_declarations.extend(Declaration::of(decl));
                }
                CXType_FunctionProto | CXType_FunctionNoProto => {
                    self.record_type(clang_getResultType(ty), layouts);
                    for n in 0..clang_getNumArgTypes(ty) {
                        self.record_type(clang_getArgType(ty, n as u32), layouts);
                    }
                }
                CXType_Atomic => {
                    self.type_shapes.insert("atomic");
                    self.record_type(clang_Type_getValueType(ty), layouts);
                }
                _ => {
                    let canonical = clang_getCanonicalType(ty);
                    if clang_equalTypes(ty, canonical) == 0 {
                        self.record_type(canonical, layouts);
                    }
                }
            }
            if clang_isVolatileQualifiedType(ty) != 0 {
                self.type_shapes.insert("volatile");
            }
        }
    }

    unsafe fn record_element_shape(&mut self, ty: CXType, layouts: &mut BTreeMap<String, Layout>) {
        match clang_getCanonicalType(ty).kind {
            CXType_Char_U | CXType_Char_S | CXType_SChar | CXType_UChar => {
                self.type_shapes.insert("byte_element");
            }
            CXType_FunctionProto | CXType_FunctionNoProto => {
                self.type_shapes.insert("function_pointer");
            }
            _ => {}
        }
        self.record_type(ty, layouts);
    }

    fn record_reference(&mut self, cursor: CXCursor) {
        unsafe {
            let decl = clang_getCursorReferenced(cursor);
            match decl.kind {
                CXCursor_FunctionDecl => self.function_mentions.extend(Declaration::of(decl)),
                CXCursor_EnumConstantDecl | CXCursor_FieldDecl | CXCursor_TypedefDecl => {
                    self.type_declarations.extend(Declaration::of(decl));
                }
                CXCursor_VarDecl => {
                    let scope = clang_getCursorSemanticParent(decl);
                    let storage = match (scope.kind, clang_Cursor_getStorageClass(decl)) {
                        (CXCursor_TranslationUnit, _) => "file_scope",
                        (_, CX_SC_Static) => "static_local",
                        (_, CX_SC_Extern) => "block_extern",
                        _ => return,
                    };
                    let canonical = clang_getCanonicalCursor(decl);
                    if let Some(declaration) = Declaration::of(canonical) {
                        let id = match &declaration.location {
                            Some(loc) => format!("{}:{}:{}", loc.file, loc.line, loc.column),
                            None => format!("locationless:{}", declaration.name),
                        };
                        let item = self.nonlocal_objects.entry(id).or_insert_with(|| Nonlocal {
                            declaration,
                            storage,
                            declared_const: const_object(clang_getCursorType(decl)),
                            references: 0,
                        });
                        item.references += 1;
                    }
                }
                _ => {}
            }
        }
    }

    fn record_call(&mut self, cursor: CXCursor, expression: Option<CXCursor>) {
        let designator = expression.map(callee_designator);
        unsafe {
            // Only a named function designator establishes a direct edge.
            // Querying the CallExpr itself can follow a nested factory call
            // through its result, which is a different invocation.
            let callee = designator
                .filter(|expr| matches!(expr.kind, CXCursor_DeclRefExpr | CXCursor_MemberRefExpr))
                .map(|expr| clang_getCursorReferenced(expr));
            let direct = callee.filter(|decl| decl.kind == CXCursor_FunctionDecl);
            self.calls.push(Call {
                site: loc(cursor),
                callee: callee.and_then(Declaration::of),
                callee_expression: designator.map(|expr| kind_name(expr.kind)),
                direct_definition: direct
                    .map(|decl| clang_getCursorDefinition(decl))
                    .and_then(loc),
                indirect: direct.is_none(),
            });
        }
    }

    fn visit(&mut self, root: CXCursor, layouts: &mut BTreeMap<String, Layout>) {
        let mut pending = vec![root];
        while let Some(cursor) = pending.pop() {
            let nodes = children(cursor);
            let feature = match cursor.kind {
                CXCursor_CallExpr => {
                    self.record_call(cursor, nodes.first().copied());
                    None
                }
                CXCursor_DeclRefExpr | CXCursor_MemberRefExpr | CXCursor_TypeRef => {
                    self.record_reference(cursor);
                    match cursor.kind {
                        CXCursor_MemberRefExpr => Some("member_access"),
                        _ => None,
                    }
                }
                CXCursor_ForStmt | CXCursor_WhileStmt | CXCursor_DoStmt => Some("loop"),
                CXCursor_IfStmt => Some("if"),
                CXCursor_SwitchStmt => Some("switch"),
                CXCursor_GotoStmt | CXCursor_IndirectGotoStmt => Some("goto"),
                CXCursor_StmtExpr => Some("statement_expression"),
                CXCursor_AsmStmt => Some("inline_asm"),
                CXCursor_ArraySubscriptExpr => Some("array_subscript"),
                CXCursor_CompoundLiteralExpr => Some("compound_literal"),
                CXCursor_UnaryExpr => Some("unary_type_trait"),
                CXCursor_CStyleCastExpr => {
                    let ty = unsafe { clang_getCanonicalType(clang_getCursorType(cursor)) };
                    (ty.kind == CXType_Pointer).then_some("explicit_pointer_cast")
                }
                CXCursor_BinaryOperator | CXCursor_CompoundAssignOperator => {
                    let op = unsafe { clang_getCursorBinaryOperatorKind(cursor) };
                    match op {
                        CXBinaryOperator_Assign..=CXBinaryOperator_OrAssign => {
                            self.record_write(nodes.first().copied());
                            if matches!(op, CXBinaryOperator_ShlAssign..=CXBinaryOperator_OrAssign)
                            {
                                increment(&mut self.features, "bitwise_or_shift");
                            }
                            Some("assignment")
                        }
                        CXBinaryOperator_And | CXBinaryOperator_Or | CXBinaryOperator_Xor
                        | CXBinaryOperator_Shl | CXBinaryOperator_Shr => Some("bitwise_or_shift"),
                        _ => None,
                    }
                }
                CXCursor_UnaryOperator => {
                    match unsafe { clang_getCursorUnaryOperatorKind(cursor) } {
                        CXUnaryOperator_PostInc..=CXUnaryOperator_PreDec => {
                            self.record_write(nodes.first().copied());
                            Some("increment_or_decrement")
                        }
                        CXUnaryOperator_Deref => Some("explicit_dereference"),
                        CXUnaryOperator_AddrOf => Some("explicit_address_of"),
                        CXUnaryOperator_Not => Some("bitwise_or_shift"),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(key) = feature {
                increment(&mut self.features, key);
            }
            match cursor.kind {
                CXCursor_VarDecl
                | CXCursor_ParmDecl
                | CXCursor_DeclRefExpr
                | CXCursor_MemberRefExpr
                | CXCursor_CompoundLiteralExpr
                | CXCursor_CStyleCastExpr
                | CXCursor_ArraySubscriptExpr
                | CXCursor_CallExpr
                | CXCursor_TypeRef => {
                    self.record_type(unsafe { clang_getCursorType(cursor) }, layouts);
                }
                _ => {}
            }
            // Push in reverse for source traversal order.
            pending.extend(nodes.into_iter().rev());
        }
    }

    fn record_write(&mut self, operand: Option<CXCursor>) {
        let Some(mut cursor) = operand else {
            return;
        };
        while matches!(cursor.kind, CXCursor_UnexposedExpr | CXCursor_ParenExpr) {
            let Some(child) = children(cursor).first().copied() else {
                return;
            };
            cursor = child;
        }
        let key = match cursor.kind {
            CXCursor_MemberRefExpr => "write_member",
            CXCursor_ArraySubscriptExpr => "write_subscript",
            CXCursor_UnaryOperator
                if unsafe { clang_getCursorUnaryOperatorKind(cursor) } == CXUnaryOperator_Deref =>
            {
                "write_dereference"
            }
            CXCursor_DeclRefExpr => "write_named",
            _ => "write_other",
        };
        increment(&mut self.features, key);
    }
}

unsafe fn const_object(ty: CXType) -> bool {
    let ty = clang_getCanonicalType(ty);
    clang_isConstQualifiedType(ty) != 0
        || (matches!(
            ty.kind,
            CXType_ConstantArray | CXType_IncompleteArray | CXType_VariableArray
        ) && const_object(clang_getElementType(ty)))
}

fn function(
    cursor: CXCursor,
    location: Location,
    declaration_locations: Vec<Location>,
    layouts: &mut BTreeMap<String, Layout>,
) -> Function {
    let mut facts = Facts::default();
    let mut parameters = Vec::new();
    let mut body = None;
    unsafe {
        let result = clang_getCursorResultType(cursor);
        facts.record_type(result, layouts);
        if clang_Cursor_isVariadic(cursor) != 0 {
            increment(&mut facts.features, "variadic_function");
        }
        if clang_Cursor_isFunctionInlined(cursor) != 0 {
            increment(&mut facts.features, "inline_declaration");
        }
        for child in children(cursor) {
            match child.kind {
                CXCursor_ParmDecl => {
                    let ty = clang_getCursorType(child);
                    facts.record_type(ty, layouts);
                    parameters.push(Parameter::of(child, ty));
                }
                CXCursor_CompoundStmt => {
                    body = extent(child);
                    facts.visit(child, layouts);
                }
                _ => {}
            }
        }
        Function {
            name: name(cursor),
            definition: location,
            spelling: spelling_loc(cursor),
            extent: extent(cursor),
            body,
            linkage: match clang_getCursorLinkage(cursor) {
                CXLinkage_Internal => "internal",
                CXLinkage_UniqueExternal => "unique_external",
                CXLinkage_External => "external",
                _ => "other",
            }
            .into(),
            storage: match clang_Cursor_getStorageClass(cursor) {
                CX_SC_Static => "static",
                CX_SC_Extern => "extern",
                CX_SC_None => "none",
                _ => "other",
            }
            .into(),
            result_type: type_name(result),
            parameters,
            declaration_locations,
            facts,
        }
    }
}

fn macro_use(cursor: CXCursor) -> Option<MacroUse> {
    let site = loc(cursor)?;
    (site.file == UNIT).then(|| MacroUse {
        name: name(cursor),
        site,
        declared_at: loc(unsafe { clang_getCursorReferenced(cursor) }),
    })
}

fn include(cursor: CXCursor) -> Option<Include> {
    let site = loc(cursor)?;
    let target = unsafe { clang_getIncludedFile(cursor) };
    Some(Include {
        name: name(cursor),
        site,
        resolved_file: (!target.is_null())
            .then(|| clang::string(unsafe { clang_getFileName(target) })),
    })
}

fn extract(cursors: &[CXCursor]) -> Unit {
    let mut unit = Unit {
        compiler: clang::string(unsafe { clang_getClangVersion() }),
        functions: Vec::new(),
        locationless_function_definitions: Vec::new(),
        system_function_definitions: Vec::new(),
        located_function_declarations: 0,
        record_layouts: BTreeMap::new(),
        macros: Vec::new(),
        includes: Vec::new(),
    };
    let mut definitions = Vec::new();
    let mut declarations = BTreeMap::<_, BTreeSet<_>>::new();
    for &cursor in cursors {
        match cursor.kind {
            CXCursor_FunctionDecl => unsafe {
                let site = loc(cursor);
                if let Some(location) = &site {
                    let usr = clang::string(clang_getCursorUSR(clang_getCanonicalCursor(cursor)));
                    if clang_isCursorDefinition(cursor) != 0 {
                        definitions.push((cursor, usr, location.clone()));
                    } else {
                        unit.located_function_declarations += 1;
                        declarations
                            .entry(usr)
                            .or_default()
                            .insert(location.clone());
                    }
                } else if clang_isCursorDefinition(cursor) != 0 {
                    unit.locationless_function_definitions.push(name(cursor));
                }
            },
            CXCursor_MacroExpansion => unit.macros.extend(macro_use(cursor)),
            CXCursor_InclusionDirective => unit.includes.extend(include(cursor)),
            _ => {}
        }
    }
    for (cursor, usr, site) in definitions {
        if site.file == UNIT {
            let redeclarations = declarations
                .get(&usr)
                .into_iter()
                .flatten()
                .cloned()
                .collect();
            unit.functions.push(function(
                cursor,
                site,
                redeclarations,
                &mut unit.record_layouts,
            ));
        } else {
            unit.system_function_definitions
                .extend(Declaration::of(cursor));
        }
    }
    unit.functions.sort_by_key(|f| f.definition.offset);
    unit
}

fn debug_probes(cursors: &[CXCursor]) -> DebugProbes {
    let mut result = DebugProbes::default();
    for &cursor in cursors {
        match cursor.kind {
            CXCursor_MacroExpansion => result.macros.extend(macro_use(cursor).filter(|entry| {
                matches!(
                    entry.name.as_str(),
                    "assert" | "testcase" | "ALWAYS" | "NEVER"
                )
            })),
            CXCursor_FunctionDecl if unsafe { clang_isCursorDefinition(cursor) } != 0 => {
                if let Some(site) = loc(cursor).filter(|site| site.file == UNIT) {
                    let body = children(cursor)
                        .into_iter()
                        .find(|child| child.kind == CXCursor_CompoundStmt)
                        .and_then(extent);
                    result.functions.push(DebugDefinition {
                        name: name(cursor),
                        definition: site,
                        body,
                    });
                }
            }
            _ => {}
        }
    }
    result
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let (mode, args) = args
        .split_first()
        .ok_or("usage: sqlite-atlas-extract MODE CFLAGS...")?;
    let unit = clang::TranslationUnit::parse(UNIT, args)?;
    let cursors = unit.children();
    let mut stdout = io::BufWriter::new(io::stdout().lock());
    match mode.as_str() {
        "inventory" => serde_json::to_writer(&mut stdout, &extract(&cursors))?,
        "assertions" => serde_json::to_writer(&mut stdout, &debug_probes(&cursors))?,
        _ => return Err(format!("unknown extraction mode {mode}").into()),
    }
    stdout.write_all(b"\n")?;
    stdout.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_the_callee_designator() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/calls.c");
        let tu = clang::TranslationUnit::parse(path, &["-std=gnu11".into()]).unwrap();
        let entry = tu
            .children()
            .into_iter()
            .find(|cursor| cursor.kind == CXCursor_FunctionDecl && name(*cursor) == "calls")
            .unwrap();
        let facts = function(entry, loc(entry).unwrap(), Vec::new(), &mut BTreeMap::new()).facts;
        let direct: Vec<_> = facts
            .calls
            .iter()
            .filter(|call| !call.indirect)
            .map(|call| call.callee.as_ref().unwrap().name.as_str())
            .collect();
        let indirect: Vec<_> = facts
            .calls
            .iter()
            .filter(|call| call.indirect)
            .map(|call| call.callee_expression.as_deref().unwrap())
            .collect();
        assert_eq!(direct, ["a", "a", "a", "a", "factory"]);
        assert_eq!(
            indirect,
            [
                "CStyleCastExpr",
                "DeclRefExpr",
                "MemberRefExpr",
                "ConditionalOperator",
                "CallExpr"
            ]
        );
    }
}
