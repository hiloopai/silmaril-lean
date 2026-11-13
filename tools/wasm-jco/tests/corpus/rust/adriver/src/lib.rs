#![allow(clippy::all)]
mod adriver;
use adriver::corpus::astream::bytes;

struct C;

impl adriver::Guest for C {
    async fn check(n: u32) -> u32 {
        let s = bytes::gen(n).await;
        bytes::count(s).await
    }
    async fn both(x: u32) -> u64 {
        let d = bytes::delay(x).await;
        bytes::total(vec![d, x, 1]).await
    }
}

adriver::export!(C with_types_in adriver);
