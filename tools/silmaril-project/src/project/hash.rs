//! Blob digests: the DASL CID (CIDv1, codec raw
//! `0x55`, multihash BLAKE3-256 `0x1e`, multibase base32-lower `b`), and the aliases SHA-256
//! and Git blob SHA-1 (SHA-1 of `"blob " ++ decimal(len) ++ "\0" ++ bytes`).

use sha1::Sha1;
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Digests {
    pub size: u64,
    pub sha256: String,
    pub blake3: String,
    pub git_sha1: String,
    pub cid: String,
}

/// The CID prefix of every v0.1 artifact: version 1, codec raw, BLAKE3, 32-byte digest.
pub const CID_HEADER: [u8; 4] = [0x01, 0x55, 0x1e, 0x20];

/// RFC 4648 base32, lower case, no padding.
fn base32(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";
    let mut out = String::new();
    let (mut acc, mut bits) = (0u32, 0u32);
    for &b in bytes {
        acc = (acc << 8) | u32::from(b);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(ALPHABET[((acc >> bits) & 31) as usize] as char);
        }
    }
    if bits > 0 {
        out.push(ALPHABET[((acc << (5 - bits)) & 31) as usize] as char);
    }
    out
}

fn unbase32(s: &str) -> Option<Vec<u8>> {
    let (mut out, mut acc, mut bits) = (Vec::new(), 0u32, 0u32);
    for c in s.bytes() {
        let v = match c {
            b'a'..=b'z' => c - b'a',
            b'2'..=b'7' => c - b'2' + 26,
            _ => return None,
        };
        acc = (acc << 5) | u32::from(v);
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
        }
    }
    Some(out)
}

/// The CID of a BLAKE3-256 digest.
pub fn cid_of_blake3(digest: &[u8; 32]) -> String {
    let mut b = CID_HEADER.to_vec();
    b.extend_from_slice(digest);
    format!("b{}", base32(&b))
}

/// The BLAKE3 digest (lowercase hex) inside a v0.1 CID, or `None` if `cid` is not one.
pub fn blake3_of_cid(cid: &str) -> Option<String> {
    let b = unbase32(cid.strip_prefix('b')?)?;
    (b.len() == 36 && b[..4] == CID_HEADER && cid_of_blake3(b[4..].try_into().ok()?) == cid)
        .then(|| hex(&b[4..]))
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

impl Digests {
    pub fn of(bytes: &[u8]) -> Self {
        let mut git = Sha1::new();
        git.update(format!("blob {}\0", bytes.len()).as_bytes());
        git.update(bytes);
        let b3 = blake3::hash(bytes);
        Digests {
            size: bytes.len() as u64,
            sha256: hex(&Sha256::digest(bytes)),
            blake3: b3.to_hex().to_string(),
            cid: cid_of_blake3(b3.as_bytes()),
            git_sha1: hex(&git.finalize()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_answers_for_the_empty_file() {
        let d = Digests::of(b"");
        assert_eq!(d.size, 0);
        assert_eq!(
            d.sha256,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            d.blake3,
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
        assert_eq!(d.git_sha1, "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391");
        assert_eq!(
            d.cid,
            "bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi"
        );
        assert_eq!(blake3_of_cid(&d.cid).as_deref(), Some(d.blake3.as_str()));
    }

    #[test]
    fn cid_of_one_zero_byte() {
        // BLAKE3's published test vector for the 1-byte input `[0]` (test_vectors.json).
        let d = Digests::of(&[0]);
        assert_eq!(
            d.blake3,
            "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"
        );
        assert!(d.cid.starts_with("bafkr4i"), "{}", d.cid);
        assert_eq!(blake3_of_cid(&d.cid).as_deref(), Some(d.blake3.as_str()));
    }

    #[test]
    fn malformed_cids() {
        let good = Digests::of(b"").cid;
        assert_eq!(good.len(), 59);
        assert!(good.starts_with("bafkr4i"));
        assert!(blake3_of_cid(&good[1..]).is_none());
        assert!(blake3_of_cid(&good.to_uppercase()).is_none());
        assert!(blake3_of_cid(&good[..58]).is_none());
        assert!(blake3_of_cid(&format!("{good}a")).is_none());
        // a sha2-256 multihash (0x12) is not a v0.1 CID
        assert!(
            blake3_of_cid("bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenxquvyku").is_none()
        );
    }

    #[test]
    fn known_answers_for_hello() {
        // `printf 'hello\n' | git hash-object --stdin`, `sha256sum`, `b3sum`.
        let d = Digests::of(b"hello\n");
        assert_eq!(d.git_sha1, "ce013625030ba8dba906f756967f9e9ca394464a");
        assert_eq!(
            d.sha256,
            "5891b5b522d5df086d0ff0b110fbd9d21bb4fc7163af34d08286a2e846f6be03"
        );
    }

    #[test]
    fn git_blob_matches_git_hash_object() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("x.bin");
        let bytes: Vec<u8> = (0..=255u8).cycle().take(5000).collect();
        std::fs::write(&path, &bytes).unwrap();
        let Ok(out) = std::process::Command::new("git")
            .arg("hash-object")
            .arg(&path)
            .output()
        else {
            return; // no git on this machine
        };
        let git = String::from_utf8(out.stdout).unwrap();
        assert_eq!(Digests::of(&bytes).git_sha1, git.trim());
    }
}
