//! Small CIndex adapter. Cursors, types and locations borrow the translation unit.
use clang_sys::*;
use serde::Serialize;
use std::ffi::{c_void, CStr, CString};
use std::os::raw::c_int;
use std::ptr;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Location {
    pub file: String,
    pub offset: u32,
    pub line: u32,
    pub column: u32,
}

pub fn string(raw: CXString) -> String {
    unsafe {
        let ptr = clang_getCString(raw);
        let value = if ptr.is_null() {
            String::new()
        } else {
            CStr::from_ptr(ptr).to_string_lossy().into_owned()
        };
        clang_disposeString(raw);
        value
    }
}

pub fn name(cursor: CXCursor) -> String {
    string(unsafe { clang_getCursorSpelling(cursor) })
}

pub fn kind_name(kind: CXCursorKind) -> String {
    string(unsafe { clang_getCursorKindSpelling(kind) })
}

pub fn type_name(ty: CXType) -> String {
    string(unsafe { clang_getTypeSpelling(ty) })
}

fn location(raw: CXSourceLocation, spelling: bool) -> Option<Location> {
    let mut file = ptr::null_mut();
    let (mut line, mut column, mut offset) = (0, 0, 0);
    unsafe {
        let get_location = if spelling {
            clang_getSpellingLocation
        } else {
            clang_getExpansionLocation
        };
        get_location(raw, &mut file, &mut line, &mut column, &mut offset);
        (!file.is_null()).then(|| Location {
            file: string(clang_getFileName(file)),
            offset,
            line,
            column,
        })
    }
}

pub fn loc(cursor: CXCursor) -> Option<Location> {
    location(unsafe { clang_getCursorLocation(cursor) }, false)
}

pub fn spelling_loc(cursor: CXCursor) -> Option<Location> {
    location(unsafe { clang_getCursorLocation(cursor) }, true)
}

pub fn extent(cursor: CXCursor) -> Option<[Location; 2]> {
    unsafe {
        let range = clang_getCursorExtent(cursor);
        Some([
            location(clang_getRangeStart(range), false)?,
            location(clang_getRangeEnd(range), false)?,
        ])
    }
}

extern "C" fn append(cursor: CXCursor, _: CXCursor, data: CXClientData) -> CXChildVisitResult {
    unsafe { (*data.cast::<Vec<CXCursor>>()).push(cursor) };
    CXChildVisit_Continue
}

pub fn children(cursor: CXCursor) -> Vec<CXCursor> {
    let mut result = Vec::new();
    unsafe {
        clang_visitChildren(
            cursor,
            append,
            (&mut result as *mut Vec<_>).cast::<c_void>(),
        )
    };
    result
}

pub struct TranslationUnit {
    index: CXIndex,
    unit: CXTranslationUnit,
}

impl TranslationUnit {
    pub fn parse(path: &str, args: &[String]) -> Result<Self, String> {
        let source = CString::new(path).map_err(|e| e.to_string())?;
        let args: Vec<_> = args
            .iter()
            .map(|arg| CString::new(arg.as_str()))
            .collect::<Result<_, _>>()
            .map_err(|e| e.to_string())?;
        let argv: Vec<_> = args.iter().map(|arg| arg.as_ptr()).collect();
        unsafe {
            let index = clang_createIndex(0, 0);
            let mut unit = ptr::null_mut();
            // DetailedPreprocessingRecord retains macro instantiation and include cursors.
            let status = clang_parseTranslationUnit2(
                index,
                source.as_ptr(),
                argv.as_ptr(),
                argv.len() as c_int,
                ptr::null_mut(),
                0,
                CXTranslationUnit_DetailedPreprocessingRecord,
                &mut unit,
            );
            if status != CXError_Success {
                clang_disposeIndex(index);
                return Err(format!("libclang parse failed ({status})"));
            }
            let result = Self { index, unit };
            let mut warnings = Vec::new();
            for i in 0..clang_getNumDiagnostics(unit) {
                let diag = clang_getDiagnostic(unit, i);
                if clang_getDiagnosticSeverity(diag) >= CXDiagnostic_Warning {
                    warnings.push(string(clang_formatDiagnostic(
                        diag,
                        clang_defaultDiagnosticDisplayOptions(),
                    )));
                }
                clang_disposeDiagnostic(diag);
            }
            if warnings.is_empty() {
                Ok(result)
            } else {
                Err(warnings.join("\n"))
            }
        }
    }

    pub fn children(&self) -> Vec<CXCursor> {
        children(unsafe { clang_getTranslationUnitCursor(self.unit) })
    }
}

impl Drop for TranslationUnit {
    fn drop(&mut self) {
        unsafe {
            clang_disposeTranslationUnit(self.unit);
            clang_disposeIndex(self.index);
        }
    }
}
