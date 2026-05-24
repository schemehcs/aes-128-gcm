use aes_128::{AES128, Key};
use subtle::ConstantTimeEq;
const MAX_BLOCKS: usize = (1 << 32) - 1;
pub fn encrypt(aad: &[u8], plaintext: &[u8], key: &Key, nonce: &[u8]) -> (Vec<u8>, [u8; 16]) {
    assert!(plaintext.len() <= MAX_BLOCKS * 16, "plaintext exceeds GCM limit");
    assert!(!nonce.is_empty(), "nonce must not be empty");
    let mut ciphertext = Vec::with_capacity(plaintext.len());
    let ciph = AES128::new(key);
    let h = u128::from_be_bytes(ciph.encrypt(&[0; 16]));
    let y0_be = if nonce.len() == 12 {
        let mut t = [0u8; 16];
        t[..12].copy_from_slice(nonce);
        t[15] = 1;
        t
    } else {
        ghash_streaming(h, &[], nonce).to_be_bytes()
    };
    let mut y_be = y0_be;
    incr_be(&mut y_be);
    let mut chunks = plaintext.chunks_exact(16);
    for chunk_n in chunks
        .by_ref()
        .map(|c| u128::from_be_bytes(c.try_into().unwrap()))
    {
        let stream = ciph.encrypt(&y_be);
        let stream_n = u128::from_be_bytes(stream);
        let cipher = stream_n ^ chunk_n;
        ciphertext.extend_from_slice(&cipher.to_be_bytes());
        incr_be(&mut y_be);
    }
    let remainder = chunks.remainder();
    if !remainder.is_empty() {
        let stream = ciph.encrypt(&y_be);
        let stream_n = u128::from_be_bytes(stream);
        let mut block: [u8; 16] = [0; 16];
        block[..remainder.len()].copy_from_slice(remainder);
        let block_n = u128::from_be_bytes(block);
        let cipher = stream_n ^ block_n;
        ciphertext.extend_from_slice(&cipher.to_be_bytes()[..remainder.len()]);
    }
    let tag_ghash = ghash_streaming(h, aad, &ciphertext);
    let e0 = ciph.encrypt(&y0_be);
    let e0_n = u128::from_be_bytes(e0);
    let tag_n = tag_ghash ^ e0_n;
    (ciphertext, tag_n.to_be_bytes())
}

fn incr_be(y: &mut [u8; 16]) {
    let mut ctr: u32 = u32::from_be_bytes(y[12..].try_into().unwrap());
    ctr = ctr.wrapping_add(1);
    y[12..].copy_from_slice(&ctr.to_be_bytes());
}

#[derive(Debug, PartialEq)]
pub struct DecryptErr;

impl std::fmt::Display for DecryptErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failed to decrypt")
    }
}
impl std::error::Error for DecryptErr {}

pub fn decrypt(
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8; 16],
    key: &Key,
    nonce: &[u8],
) -> Result<Vec<u8>, DecryptErr> {
    assert!(ciphertext.len() <= MAX_BLOCKS * 16, "ciphertext exceeds GCM limit");
    assert!(!nonce.is_empty(), "nonce must not be empty");
    let ciph = AES128::new(key);
    let h = u128::from_be_bytes(ciph.encrypt(&[0; 16]));
    let y0_be = if nonce.len() == 12 {
        let mut t = [0u8; 16];
        t[..12].copy_from_slice(nonce);
        t[15] = 1;
        t
    } else {
        ghash_streaming(h, &[], nonce).to_be_bytes()
    };
    let e0 = ciph.encrypt(&y0_be);
    let ghash = ghash_streaming(h, aad, ciphertext);
    let ghash_bytes = ghash.to_be_bytes();
    let mut expected_tag = [0u8; 16];
    for i in 0..16 {
        expected_tag[i] = e0[i] ^ ghash_bytes[i];
    }
    if expected_tag.ct_eq(tag).unwrap_u8() != 1 {
        return Err(DecryptErr);
    }
    let mut plaintext = Vec::with_capacity(ciphertext.len());
    let mut y_be = y0_be;
    incr_be(&mut y_be);
    let mut chunks = ciphertext.chunks_exact(16);
    for chunk_n in chunks
        .by_ref()
        .map(|c| u128::from_be_bytes(c.try_into().unwrap()))
    {
        let stream = ciph.encrypt(&y_be);
        let stream_n = u128::from_be_bytes(stream);
        let cipher = chunk_n ^ stream_n;
        plaintext.extend_from_slice(&cipher.to_be_bytes());
        incr_be(&mut y_be);
    }
    let remainder = chunks.remainder();
    if !remainder.is_empty() {
        let stream = ciph.encrypt(&y_be);
        let stream_n = u128::from_be_bytes(stream);
        let mut block = [0u8; 16];
        block[..remainder.len()].copy_from_slice(remainder);
        let block_n = u128::from_be_bytes(block);
        let text = block_n ^ stream_n;
        plaintext.extend_from_slice(&text.to_be_bytes()[..remainder.len()]);
    }
    Ok(plaintext)
}

fn ghash_streaming(h: u128, aad: &[u8], ciphertext: &[u8]) -> u128 {
    let mut y = 0u128;
    let mut chunks = aad.chunks_exact(16);
    for xc in chunks.by_ref() {
        let x = u128::from_be_bytes(xc.try_into().unwrap());
        y = gmul(y ^ x, h);
    }
    let rem = chunks.remainder();
    if !rem.is_empty() {
        let mut last_block = [0_u8; 16];
        last_block[..rem.len()].copy_from_slice(rem);
        y = gmul(y ^ u128::from_be_bytes(last_block), h);
    }
    let mut chunks = ciphertext.chunks_exact(16);
    for xc in chunks.by_ref() {
        let x = u128::from_be_bytes(xc.try_into().unwrap());
        y = gmul(y ^ x, h);
    }
    let rem = chunks.remainder();
    if !rem.is_empty() {
        let mut last_block = [0_u8; 16];
        last_block[..rem.len()].copy_from_slice(rem);
        y = gmul(y ^ u128::from_be_bytes(last_block), h);
    }
    let len_a = (aad.len() as u64).wrapping_mul(8);
    let len_c = (ciphertext.len() as u64).wrapping_mul(8);
    let mut len_block = [0u8; 16];
    len_block[..8].copy_from_slice(&len_a.to_be_bytes());
    len_block[8..].copy_from_slice(&len_c.to_be_bytes());
    gmul(y ^ u128::from_be_bytes(len_block), h)
}

#[inline]
fn gmul(mut x: u128, mut y: u128) -> u128 {
    const REM: u128 = 0xE1 << 120;
    let mut z = 0u128;
    for _ in 0..128 {
        let mask_z = 0_u128.wrapping_sub(y >> 127);
        z ^= x & mask_z;
        y <<= 1;
        let mask_x = 0_u128.wrapping_sub(x & 1);
        x = (x >> 1) ^ (REM & mask_x);
    }
    z
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gmul_case1() {
        assert_eq!(
            gmul(
                0x0388dace60b6a392f328c2b971b2fe78,
                0x80000000000000000000000000000000
            ),
            0x0388dace60b6a392f328c2b971b2fe78
        );
        assert_eq!(
            gmul(
                0x80000000000000000000000000000000,
                0x0388dace60b6a392f328c2b971b2fe78
            ),
            0x0388dace60b6a392f328c2b971b2fe78
        );
    }

    #[test]
    fn gmul_case2() {
        assert_eq!(
            gmul(
                0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                0x00000000000000000000000000000000
            ),
            0x00000000000000000000000000000000
        );
        assert_eq!(
            gmul(
                0x00000000000000000000000000000000,
                0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            ),
            0x00000000000000000000000000000000
        );
    }

    #[test]
    fn gmul_case3() {
        assert_eq!(
            gmul(
                0xacbef20579b4b8ebce889bac8732dad7,
                0xed95f8e164bf3213febc740f0bd9c4af
            ),
            0x4db870d37cb75fcb46097c36230d1612
        );
        assert_eq!(
            gmul(
                0xed95f8e164bf3213febc740f0bd9c4af,
                0xacbef20579b4b8ebce889bac8732dad7
            ),
            0x4db870d37cb75fcb46097c36230d1612
        );
    }

    #[test]
    fn gmul_case4() {
        assert_eq!(
            gmul(
                0x0388dace60b6a392f328c2b971b2fe78,
                0x66e94bd4ef8a2c3b884cfa59ca342b2e
            ),
            0x5e2ec746917062882c85b0685353deb7
        );
        assert_eq!(
            gmul(
                0x66e94bd4ef8a2c3b884cfa59ca342b2e,
                0x0388dace60b6a392f328c2b971b2fe78
            ),
            0x5e2ec746917062882c85b0685353deb7
        );
    }

    #[test]
    fn ghash_case1() {
        let h = 0x66e94bd4ef8a2c3b884cfa59ca342b2e;
        let a = [];
        let c = 0x0388dace60b6a392f328c2b971b2fe78_u128.to_be_bytes();
        assert_eq!(
            ghash_streaming(h, &a, &c),
            0xf38cbb1ad69223dcc3457ae5b6b0f885
        );
    }

    /* ref: https://luca-giuzzi.unibs.it/corsi/Support/papers-cryptography/gcm-spec.pdf */
    #[test]
    fn gcm_case1() {
        let key: [u8; 16] = [0; 16];
        let aad: [u8; 0] = [];
        let plaintext: [u8; 0] = [];
        let nonce: [u8; 12] = [0; 12];
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(ciphertext, &[], "comparing ciphertext");
        assert_eq!(
            u128::from_be_bytes(tag),
            0x58e2fccefa7e3061367f1d57a4e7455a,
            "comparing tag"
        );
    }

    #[test]
    fn gcm_case1_de() {
        let key: [u8; 16] = [0; 16];
        let aad: [u8; 0] = [];
        let ciphertext: [u8; 0] = [];
        let tag = 0x58e2fccefa7e3061367f1d57a4e7455a_u128.to_be_bytes();
        let nonce: [u8; 12] = [0; 12];
        let plaintext = decrypt(&aad, &ciphertext, &tag, &key, &nonce).unwrap();
        assert_eq!(plaintext, &[], "comparing plaintext");
        let forged_tag = 0x48e2fccefa7e3061367f1d57a4e7455a_u128.to_be_bytes();
        assert_eq!(
            decrypt(&aad, &ciphertext, &forged_tag, &key, &nonce),
            Err(DecryptErr)
        );
    }

    #[test]
    fn gcm_case2() {
        let key: [u8; 16] = [0; 16];
        let aad: [u8; 0] = [];
        let plaintext: [u8; 16] = 0_u128.to_be_bytes();
        let nonce: [u8; 12] = [0; 12];
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(
            u128::from_be_bytes(ciphertext.try_into().unwrap()),
            0x0388dace60b6a392f328c2b971b2fe78,
            "comparing ciphertext"
        );
        assert_eq!(
            u128::from_be_bytes(tag),
            0xab6e47d42cec13bdf53a67b21257bddf,
            "comparing tag"
        );
    }

    #[test]
    fn gcm_case2_de() {
        let key: [u8; 16] = [0; 16];
        let aad: [u8; 0] = [];
        let ciphertext = 0x0388dace60b6a392f328c2b971b2fe78_u128.to_be_bytes();
        let tag = 0xab6e47d42cec13bdf53a67b21257bddf_u128.to_be_bytes();
        let nonce: [u8; 12] = [0; 12];
        let plaintext = decrypt(&aad, &ciphertext, &tag, &key, &nonce).unwrap();
        assert_eq!(plaintext, &0_u128.to_be_bytes(), "comparing plaintext");
        let forged_tag = 0xab6e47d42cec13bdf53a67b21257bdde_u128.to_be_bytes();
        assert_eq!(
            decrypt(&aad, &ciphertext, &forged_tag, &key, &nonce),
            Err(DecryptErr)
        );
    }

    #[test]
    fn gcm_case3() {
        let key: [u8; 16] = 0xfeffe9928665731c6d6a8f9467308308_u128.to_be_bytes();
        let aad: [u8; 0] = [];
        let nonce = hex::decode("cafebabefacedbaddecaf888").unwrap();
        let plaintext = hex::decode("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255").unwrap();
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(ciphertext, hex::decode(&"42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985").unwrap(), "comparing ciphertext");
        assert_eq!(
            u128::from_be_bytes(tag),
            0x4d5c2af327cd64a62cf35abd2ba6fab4,
            "comparing tag"
        );
    }

    #[test]
    fn gcm_case3_de() {
        let key: [u8; 16] = 0xfeffe9928665731c6d6a8f9467308308_u128.to_be_bytes();
        let aad: [u8; 0] = [];
        let nonce = hex::decode("cafebabefacedbaddecaf888").unwrap();
        let ciphertext = hex::decode("42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985").unwrap();
        let tag = 0x4d5c2af327cd64a62cf35abd2ba6fab4_u128.to_be_bytes();
        let plaintext = decrypt(&aad, &ciphertext, &tag, &key, &nonce).unwrap();
        let expected_plaintext = hex::decode("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255").unwrap();
        assert_eq!(expected_plaintext, plaintext, "comparing plaintext");
        let forged_tag = 0x5d5c2af327cd64a62cf35abd2ba6fab4_u128.to_be_bytes();
        assert_eq!(
            decrypt(&aad, &ciphertext, &forged_tag, &key, &nonce),
            Err(DecryptErr)
        );
    }

    #[test]
    fn gcm_case4() {
        let key: [u8; 16] = 0xfeffe9928665731c6d6a8f9467308308_u128.to_be_bytes();
        let aad = hex::decode("feedfacedeadbeeffeedfacedeadbeefabaddad2").unwrap();
        let plaintext = hex::decode("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39").unwrap();
        let nonce = hex::decode("cafebabefacedbaddecaf888").unwrap();
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(ciphertext, hex::decode(&"42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091").unwrap(), "comparing ciphertext");
        assert_eq!(
            u128::from_be_bytes(tag),
            0x5bc94fbc3221a5db94fae95ae7121a47,
            "comparing tag"
        );
    }

    #[test]
    fn gcm_case5() {
        let key: [u8; 16] = 0xfeffe9928665731c6d6a8f9467308308_u128.to_be_bytes();
        let aad = hex::decode("feedfacedeadbeeffeedfacedeadbeefabaddad2").unwrap();
        let plaintext = hex::decode("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39").unwrap();
        let nonce = hex::decode("cafebabefacedbad").unwrap();
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(ciphertext, hex::decode(&"61353b4c2806934a777ff51fa22a4755699b2a714fcdc6f83766e5f97b6c742373806900e49f24b22b097544d4896b424989b5e1ebac0f07c23f4598").unwrap(), "comparing ciphertext");
        assert_eq!(
            u128::from_be_bytes(tag),
            0x3612d2e79e3b0785561be14aaca2fccb,
            "comparing tag"
        );
    }

    #[test]
    fn gcm_case6() {
        let key: [u8; 16] = 0xfeffe9928665731c6d6a8f9467308308_u128.to_be_bytes();
        let aad = hex::decode("feedfacedeadbeeffeedfacedeadbeefabaddad2").unwrap();
        let plaintext = hex::decode("d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39").unwrap();
        let nonce = hex::decode("9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b").unwrap();
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(ciphertext, hex::decode(&"8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5").unwrap(), "comparing ciphertext");
        assert_eq!(
            u128::from_be_bytes(tag),
            0x619cc5aefffe0bfa462af43c1699d050,
            "comparing tag"
        );
    }

    #[test]
    fn gcm_case7() {
        let key: [u8; 16] = "0123456789123456".as_bytes().try_into().unwrap();
        let aad = "0011223344556677".as_bytes();
        let plaintext = "I will become what I deserve, Is there anything like freewil?".as_bytes();
        let nonce = "abcdef012345".as_bytes();
        let (ciphertext, tag) = encrypt(&aad, &plaintext, &key, &nonce);
        assert_eq!(ciphertext, hex::decode(&"03feb633afbc123a3ab9f1119694c4becdf1bdc5c1fc584f128d893f1bf08862e1a2e29e821d9c8b59dc1942c1033724e3a1128c9586104c88bf720449").unwrap(), "comparing ciphertext");
        assert_eq!(
            &tag[..],
            &hex::decode("d067e05d1155ab4c9f30c5eb194d9f67").unwrap(),
            "comparing tag"
        );
    }
}
