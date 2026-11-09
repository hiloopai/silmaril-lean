//! sids: 256-bit silmaril identifiers, written as 64
//! lowercase hex digits. The project sid is mandatory in `silmaril.toml`; an object's default
//! sid is derived from its kind, its project's sid and its name; an artifact's sid is its
//! BLAKE3 content digest.

/// The `derive_key` context of object sids.
pub const CONTEXT: &str = "silmaril.sid.v0";

/// `BLAKE3.derive_key("silmaril.sid.v0", kind ‖ 0x00 ‖ project_sid ‖ 0x00 ‖ name)`.
pub fn derive(kind: &str, project: &[u8; 32], name: &str) -> String {
    let mut m = Vec::with_capacity(kind.len() + name.len() + 34);
    m.extend_from_slice(kind.as_bytes());
    m.push(0);
    m.extend_from_slice(project);
    m.push(0);
    m.extend_from_slice(name.as_bytes());
    super::hash::hex(&blake3::derive_key(CONTEXT, &m))
}

/// 64 lowercase hex digits, as raw bytes.
pub fn parse(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 || !s.bytes().all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f')) {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(out)
}

/// A fresh random sid from the OS (`sil project init`).
pub fn random() -> std::io::Result<String> {
    use std::io::Read;
    let mut b = [0u8; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut b)?;
    Ok(super::hash::hex(&b))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The design's test vector (computed with the `blake3` 1.8.7 crate).
    #[test]
    fn design_vectors() {
        let p = parse("3d4eb2e501a982cff67337f8e00d2ea1a4183f11c9e23164d6f411a2f8726cf8").unwrap();
        assert_eq!(
            derive("value", &p, "demo.config"),
            "dfad7077ce79d684d29dcbb64d573848839e57fe5a17ee9baa2b8ff802700e64"
        );
        assert_eq!(
            derive("problem", &p, "demo.config.port_is_8080"),
            "05d59ec041ef169422bde02c686e8926bcb989843c2d946cb4cb63148945d181"
        );
    }

    #[test]
    fn parse_rejects_bad_hex() {
        assert!(parse(&"a".repeat(64)).is_some());
        assert!(parse(&"A".repeat(64)).is_none());
        assert!(parse(&"a".repeat(63)).is_none());
        assert!(parse(&"g".repeat(64)).is_none());
        let r = random().unwrap();
        assert!(parse(&r).is_some() && r != random().unwrap());
    }
}
