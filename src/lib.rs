use aes_128::{AES128, Key};

pub fn encrypt(aad: &[u8], plaintext: &[u8], key: &Key, nonce: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let mut ciphertext = Vec::new();
    let mut tag = [0u8; 16];
    let ciph = AES128::new(key);
    let h = u128::from_be_bytes(ciph.encrypt(&[0; 16]));
    let y0: u128 = if nonce.len() == 12 {
        let mut y_bytes = [0u8; 16];
        y_bytes[..12].copy_from_slice(nonce);
        y_bytes[15] = 1;
        u128::from_be_bytes(y_bytes)
    } else {
        ghash_a_c(h, &[], nonce)
    };
    let mut y = incr(y0);
    for chunk in plaintext.chunks(16) {
        let stream = ciph.encrypt(&y.to_be_bytes());
        for i in 0..chunk.len() {
            ciphertext.push(stream[i] ^ chunk[i]);
        }
        y = incr(y);
    }
    let tag_ghash = ghash_a_c(h, aad, &ciphertext);
    let tag_bytes = tag_ghash.to_be_bytes();
    let e0 = ciph.encrypt(&y0.to_be_bytes());
    for i in 0..16 {
        tag[i] = tag_bytes[i] ^ e0[i];
    }

    (ciphertext, tag)
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
    let ciph = AES128::new(key);
    let h = u128::from_be_bytes(ciph.encrypt(&[0; 16]));
    let y0: u128 = if nonce.len() == 12 {
        let mut y_bytes = [0u8; 16];
        y_bytes[..12].copy_from_slice(nonce);
        y_bytes[15] = 1;
        u128::from_be_bytes(y_bytes)
    } else {
        ghash_a_c(h, &[], nonce)
    };
    let e0 = ciph.encrypt(&y0.to_be_bytes());
    let ghash = ghash_a_c(h, aad, ciphertext);
    let ghash_bytes = ghash.to_be_bytes();
    let mut tag_match: bool = true;
    for i in 0..16 {
        if tag[i] != e0[i] ^ ghash_bytes[i] {
            tag_match = false;
        }
    }
    if !tag_match {
        return Err(DecryptErr);
    }

    let mut plaintext = Vec::new();
    let mut y = incr(y0);
    for chunk in ciphertext.chunks(16) {
        let stream = ciph.encrypt(&y.to_be_bytes());
        for i in 0..chunk.len() {
            plaintext.push(stream[i] ^ chunk[i]);
        }
        y = incr(y);
    }
    Ok(plaintext)
}

fn incr(y: u128) -> u128 {
    const CTR_MASK: u128 = 0xFFFFFFFF;
    if y & CTR_MASK != CTR_MASK {
        y + 1
    } else {
        y & !CTR_MASK
    }
}

/// calculate the ghash of bytes
///
/// Blocks are chunked by 16b each, the last block is padded with 0s if 1<=len(last)<16
fn ghash_raw(h: u128, xs: &[u8]) -> u128 {
    let mut y = 0;
    let mut chunks = xs.chunks_exact(16);
    for xc in chunks.by_ref() {
        let x: u128 = u128::from_be_bytes(xc.try_into().unwrap());
        y = gmul(y ^ x, h);
    }
    let remainder = chunks.remainder();
    if !remainder.is_empty() {
        let mut last_block = [0_u8; 16];
        last_block[..remainder.len()].copy_from_slice(remainder);
        let ln = u128::from_be_bytes(last_block);
        y = gmul(y ^ ln, h);
    }
    y
}

/// calculate the ghash for associated data and ciphered bytes
///
/// align with aes gcm GHASH specification
fn ghash_a_c(h: u128, a: &[u8], c: &[u8]) -> u128 {
    let mut hash_input: Vec<u8> = Vec::new();
    hash_input.extend_from_slice(a);
    let a_pad = a.len() % 16;
    if a_pad != 0 {
        hash_input.extend(std::iter::repeat_n(0, 16 - a_pad));
    }
    hash_input.extend_from_slice(c);
    let c_pad = c.len() % 16;
    if c_pad != 0 {
        hash_input.extend(std::iter::repeat_n(0, 16 - c_pad));
    }
    let len_a = a.len() * 8;
    hash_input.extend_from_slice(&len_a.to_be_bytes());

    let len_c = c.len() * 8;
    hash_input.extend_from_slice(&len_c.to_be_bytes());
    ghash_raw(h, &hash_input)
}

fn gmul(mut x: u128, mut y: u128) -> u128 {
    const REM: u128 = 0xE1 << 120;
    const MSB: u128 = 1 << 127;
    let mut p = 0;
    for _ in 0..128 {
        if y & MSB == MSB {
            p ^= x;
        }
        y <<= 1;
        x = if x & 1 == 1 { (x >> 1) ^ REM } else { x >> 1 };
    }
    p
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
        assert_eq!(ghash_a_c(h, &a, &c), 0xf38cbb1ad69223dcc3457ae5b6b0f885);
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
}
