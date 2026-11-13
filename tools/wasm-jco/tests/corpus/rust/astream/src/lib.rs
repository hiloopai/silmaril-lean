#![allow(clippy::all)]
mod astream;
use astream::exports::corpus::astream::bytes::Guest as Bytes;
use astream::wit_stream;
use wit_bindgen::StreamReader;

struct C;

impl astream::Guest for C {
    async fn twice(x: u32) -> u32 {
        x.wrapping_mul(2)
    }
}

impl Bytes for C {
    async fn count(mut s: StreamReader<u8>) -> u32 {
        let mut n = 0u32;
        while let Some(_) = s.next().await {
            n += 1;
        }
        n
    }
    async fn gen(n: u32) -> StreamReader<u8> {
        let (mut tx, rx) = wit_stream::new::<u8>();
        wit_bindgen::spawn_local(async move {
            let v: Vec<u8> = (0..n).map(|i| b'a' + (i % 26) as u8).collect();
            tx.write_all(v).await;
        });
        rx
    }
    async fn delay(x: u32) -> u32 {
        x.wrapping_mul(2).wrapping_add(1)
    }
    async fn total(xs: Vec<u32>) -> u64 {
        xs.iter().map(|&x| x as u64).sum()
    }
}

astream::export!(C with_types_in astream);
