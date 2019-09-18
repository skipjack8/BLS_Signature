extern crate pairing;
extern crate rand;
extern crate blake2;
extern crate byteorder;
//extern crate generic_array;
use std::mem;
use byteorder::{ReadBytesExt, BigEndian, ByteOrder, NativeEndian};
use rand::{SeedableRng, Rng, Rand, XorShiftRng};
use rand::chacha::ChaChaRng;
//use generic_array::GenericArray;
use pairing::bls12_381::*;
//use pairing::bls12_381::*;
use pairing::*;
use blake2::{Blake2b, Digest, Blake2s};
use std::fmt;
use std::time::{Duration, Instant};

fn get_b_coeff()-> Fq2{
    /*
    let b_coeff_fq = Fq::from_repr(FqRepr([
        0xaa270000000cfff3,
        0x53cc0032fc34000a,
        0x478fe97a6b0a807f,
        0xb1d37ebee6ba24d7,
        0x8ec9733bbf78ab2f,
        0x9d645513d83de7e,
    ])).unwrap();
    */
    let b_coeff_fq = Fq::from_repr(FqRepr([4, 0, 0, 0, 0, 0])).unwrap();
    Fq2 {
        c0: b_coeff_fq,
        c1: b_coeff_fq,
    }
}

fn get_swenc_const0() -> Fq2{
    let swenc_const0 = Fq::from_repr(FqRepr([
        0x5c03fffffffdfffd,
        0xbc2fb026c4140004,
        0xbb675277cdf12d11,
        0x74d38c0ed41eefd5,
        0xbe32ce5fbeed9ca3,
        0,
    ])).unwrap();
    Fq2 {
        c0: swenc_const0,
        c1: Fq::zero(),
    }
}
fn get_swenc_const1() -> Fq2{
    let swenc_const1 = Fq::from_repr(FqRepr([
        0x2e01fffffffefffe,
        0xde17d813620a0002,
        0xddb3a93be6f89688,
        0xba69c6076a0f77ea,
        0x5f19672fdf76ce51 ,
        0,
    ])).unwrap();
    Fq2 {
        c0: swenc_const1,
        c1: Fq::zero(),
    }
}


pub fn read_fr(from: &[u8]) -> FrRepr {
    assert_eq!(from.len(), 32);

    let mut f = FrRepr::default();
    f.read_le(from).expect("length is 32 bytes");

    f
}

//Hash to Fq
fn hash_to_Fq(mut hasher: Blake2b) -> Fq {
    let mut repr: [u64; 6] = [0; 6];
    let mut count: u32 = 0;
    let mut count_u8: [u8; 4] = [0; 4];

    // hash in counter mode: append to the nonce a counter
    loop {
        // increment the counter
        count += 1;
        NativeEndian::write_u32(&mut count_u8, count);
        hasher.input(&count_u8);
        // truncate and shave the hash result
        BigEndian::read_u64_into(&hasher.result().as_slice()[..48], &mut repr);
        let mut e = FqRepr(repr);
        e.shr(3);
        let q = Fq::from_repr(e);
        match q {
            Ok(n) => {
                return n;
            }
            _ => (),
        }
    }
}

//Hash to Fq2
fn hash_to_Fq2(mut hasher: Blake2b) -> Fq2 {
    let mut hasher_c0 = hasher.clone();
    let mut hasher_c1 = hasher.clone();
    hasher_c0.input("_c0".as_bytes());
    hasher_c1.input("_c1".as_bytes());
    let c0 = hash_to_Fq(hasher_c0);//parity()
    let c1 = hash_to_Fq(hasher_c1);
    Fq2 { c0: c0 , c1: c1 }
}

/// Attempts to construct an affine point given an x-coordinate. The
/// point is not guaranteed to be in the prime order subgroup.
///
/// If and only if `greatest` is set will the lexicographically
/// largest y-coordinate be selected.
fn get_point_from_x(x: Fq2, greatest: bool) -> Option<G2Affine> {
    struct g2_affine {
        x: Fq2,
        y: Fq2,
        infinity: bool,
    }
// Compute x^3 + b
    let mut x3b = x;
    x3b.square();
    x3b.mul_assign(&x);
    x3b.add_assign(&get_b_coeff());

    x3b.sqrt().map(|y| {
        let mut negy = y;
        negy.negate();
        let y_cor = {
            if (y < negy) ^ greatest{
                y
            }
            else{
                negy
            }
        };
        unsafe{
            let g2_point = g2_affine{
                x:x,
                y:y,
                infinity:false
            };
            let g2 = mem::transmute::<g2_affine, G2Affine>(g2_point);
            g2
        }

    })
}

fn sw_encode(t: Fq2, parity: bool) -> G2Affine {
    let zero: G2Affine = G2Affine::zero();
    // handle the case t == 0
    if t.is_zero() { return zero; };

    // w = (t^2 + b + 1)^(-1) * sqrt(-3) * t
    let mut w = t;
    w.square();
    w.add_assign(&get_b_coeff());
    w.add_assign(&Fq2::one());
    // handle the case t^2 + b + 1 == 0
    if w.is_zero() { return zero; };
    w = w.inverse().unwrap();
    w.mul_assign(&get_swenc_const0());
    w.mul_assign(&t);

    // We choose the corresponding y-coordinate with the same parity as t.
    // x1 = - wt  + (sqrt(-3) - 1) / 2
    let mut x1 = w;
    x1.mul_assign(&t);
    x1.negate();
    x1.add_assign(&get_swenc_const1());
    if let Some(p) = get_point_from_x(x1, parity) {
        return p;
    }

    // x2 = -1 -x1
    let mut x2 = x1;
    x2.negate();
    x2.sub_assign(&Fq2::one());
    if let Some(p) = get_point_from_x(x2, parity) {
        return p;
    }

    // x3 = 1/w^2 + 1
    let mut x3 = w;
    x3.square();
    x3 = x3.inverse().unwrap();
    x3.add_assign(&Fq2::one());
    get_point_from_x(x3, parity).unwrap()
}


/*
fn msg_hash(msg: &[u8]) -> G2Affine {
    // the key must be of at least 128 bits.
    assert!(msg.len() >= 16);

    // The construction of Foque et al. requires us to construct two
    // "random oracles" in the field, encode their image with `sw_encode`,
    // and finally add them.
    // We construct them appending to the message the string
    // $name_$oracle
    // For instance, the first oracle in group G1 appends: "G1_0"
    let mut hasher = Blake2b::new();
    hasher.input(msg);
    hasher.input("G1_0".as_bytes());
    let t1 = hash_to_Fq2(hasher);
    let t1 = Self::sw_encode(t1);

    let mut hasher = Blake2b::new();
    hasher.input(msg);
    hasher.input("G1_1".as_bytes());
    let t2 = hash_to_Fq2(hasher);
    let t2 = Self::sw_encode(t2);

    let mut res = t2.into_projective();
    res.add_assign_mixed(&t1);
    res.into_affine().scale_by_cofactor().into_affine()

}*/

//hash n pks to n elements of Fr
pub fn hash_pks(pks: &Vec<G1Affine>) -> Vec<FrRepr> {
    let mut t = Vec::new();
    let h = {
        let mut h = Blake2s::default();
        for pk in pks.iter() {
            h.input(G1Compressed::from_affine(*pk).as_ref());
        }
        h.result()
    };
    let mut pk_hash_preimage = [0u8; 36];
    (&mut pk_hash_preimage[4..36]).copy_from_slice(&(&*h)[..]);
    for i in 0..27 {
        pk_hash_preimage[3] = i;
        let mut h1 = Blake2s::default();
        h1.input(&pk_hash_preimage);
        let f = read_fr(&h1.result());
        t.push(f);
    }
    return t;
}

//hash msg to a point in G2
pub fn hash_to_g2(msg: &[u8]) -> G2
{
    let h = {
        let mut h = Blake2b::default();
        h.input(msg);
        h.result()
    };
    //println!("{:?}",h);
    let mut h = h.as_ref();

    let mut seed = Vec::with_capacity(8);
    for _ in 0..8 {
        seed.push(h.read_u32::<BigEndian>().expect("assertion above guarantees this to work"));
    }
    ChaChaRng::from_seed(&seed).gen()
}
#[test]
fn test_hash_to_g2(){
    const MSG_LEN: usize = 1024000;
    let mut msg = [0u8; MSG_LEN];
    for i in 0..MSG_LEN {
        msg[i] = (i % 256) as u8;
    }
    let mut time = Duration::new(0, 0);
    let start = Instant::now();
    for _ in 0..100{
        let h = hash_to_g2(&msg);
    }
    time += start.elapsed();
    let verify_time = time.subsec_nanos() as f64 / 1000_000f64
        + (time.as_secs() as f64) * 1000f64;
    println!("time is {:?} ms", verify_time);
}

fn aggregate_pubkey(pks: &Vec<G1Affine>) -> G1Affine {
    let t = hash_pks(&pks);
    let mut pubkey_sum = G1::zero();
    for (ti, pki) in t.iter().zip(pks.iter()) {
        pubkey_sum.add_assign(&pki.mul(*ti));
    }

    pubkey_sum.into_affine()
}

fn aggregate_signature(sigs: &Vec<G2Affine>, pks: &Vec<G1Affine>) -> G2Affine {
    let t = hash_pks(&pks);
    let mut pubkey_sum = G2::zero();
    for (ti, sigi) in t.iter().zip(sigs.iter()) {
        pubkey_sum.add_assign(&sigi.mul(*ti));
    }

    pubkey_sum.into_affine()
}

fn single_sig()
{
    //key gen
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let sk = Fr::rand(&mut rng);
    //println!("sk:{:?}",sk);
    let mut g1 = G1Affine::one();//g1
    let pk = g1.mul(sk);//projective
    let one = Fq12::one();
    g1.negate();

    //println!("pk:{:?}",pk);

    let msg: [u8; 32] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31];
    let h_m = hash_to_g2(&msg).into_affine();
    //println!("{:?}",h_m);
    let sig = h_m.mul(sk);
    //println!("sig:{:?}",sig);

    let mut time = Duration::new(0, 0);
    let start = Instant::now();

    //verify
    //assert_eq!(Bls12::pairing(g1,sig), Bls12::pairing(pk,h_m));

    assert_eq!(Bls12::final_exponentiation(
        &Bls12::miller_loop([
            (&g1.prepare(), &sig.into_affine().prepare()),
            (&pk.into_affine().prepare(), &h_m.prepare())
        ].iter())
    ).unwrap(), one);

    time += start.elapsed();
    let verify_time = time.subsec_nanos() as f64 / 1000_000_000f64
        + (time.as_secs() as f64);
    println!("time is {:?} s", verify_time);
}

fn aggregate_sig() {
    let one = Fq12::one();
    let msg: [u8; 32] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31];
    //@TODO: optimize hash_to_g2 implementation
    let h_m = hash_to_g2(&msg).into_affine();

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let mut g1 = G1Affine::one();
    let mut sk = Vec::new();
    let mut pk = Vec::new();
    let mut sig = Vec::new();

    let mut aux_verify_coeffs = Vec::new();

    for _ in 0..27 {
        let sk_i = Fr::rand(&mut rng);
        sk.push(sk_i);
        pk.push(g1.mul(sk_i).into_affine());
        sig.push(h_m.mul(sk_i).into_affine());

        let rand_coeffs = Fr::rand(&mut rng);
        aux_verify_coeffs.push(rand_coeffs);
    }
    let mut time = Duration::new(0, 0);
    let start = Instant::now();


    //verify one by one
    g1.negate();
    for i in 0..1 {
        assert_eq!(Bls12::final_exponentiation(
            &Bls12::miller_loop([
                (&g1.prepare(), &sig[i].prepare()),
                (&pk[i].prepare(), &h_m.prepare())
            ].iter())
        ).unwrap(), one);
    }

    /*
        //batch verify
        let mut sig_rand_sum = G2::zero();
        let mut pk_rand_sum = G1::zero();
        /****batch verify*/

        for ((coeff_i, sig_i),pk_i) in aux_verify_coeffs.iter()
            .zip(sig.iter())
            .zip(pk.iter()) {
            sig_rand_sum.add_assign(&sig_i.mul(coeff_i.into_repr()));
            pk_rand_sum.add_assign(&pk_i.mul(coeff_i.into_repr()));

        }

        assert_eq!(Bls12::final_exponentiation(
            &Bls12::miller_loop([
                (&g1.prepare(), &sig_rand_sum.into_affine().prepare()),
                (&pk_rand_sum.into_affine().prepare(), &h_m.prepare())
            ].iter())
        ).unwrap(), one);
    */


    //aggregation \sum{sig}, \sum{pk}
    let mut sig_sum = G2::zero();
    let mut pk_sum = G1::zero();
    for i in 0..27 {
        sig_sum.add_assign(&sig[i].into_projective());
        pk_sum.add_assign(&pk[i].into_projective());
    }

    //let start = Instant::now();
    assert_eq!(Bls12::final_exponentiation(
        &Bls12::miller_loop([
            (&g1.prepare(), &sig_sum.into_affine().prepare()),
            (&pk_sum.into_affine().prepare(), &h_m.prepare())
        ].iter())
    ).unwrap(), one);

    time += start.elapsed();
    let verify_time = time.subsec_nanos() as f64 / 1000_000f64
        + (time.as_secs() as f64) * 1000f64;

    println!("time is {:?} ms", verify_time);
}

fn secure_aggregate_sig() {
    const MSG_LEN: usize = 1024000;
    let one = Fq12::one();
    let mut msg = [0u8; MSG_LEN];
    for i in 0..MSG_LEN {
        msg[i] = (i % 256) as u8;
    }
    let mut time = Duration::new(0, 0);

    //@TODO: optimize hash_to_g2 implementation
    let h_m = hash_to_g2(&msg).into_affine();//8ms

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let mut g1 = G1Affine::one();
    let mut sk = Vec::new();
    let mut pk = Vec::new();
    let mut sig = Vec::new();

    let mut aux_verify_coeffs = Vec::new();
    //generate simulated msg
    for _ in 0..27 {
        let sk_i = Fr::rand(&mut rng);
        sk.push(sk_i);
        pk.push(g1.mul(sk_i).into_affine());//A
        sig.push(h_m.mul(sk_i).into_affine());//A

        let rand_coeffs = Fr::rand(&mut rng);
        aux_verify_coeffs.push(rand_coeffs);
    }


    //verify one by one
    g1.negate();
    let start = Instant::now();
    for i in 0..1 {
        assert_eq!(Bls12::final_exponentiation(
            &Bls12::miller_loop([
                (&g1.prepare(), &sig[i].prepare()),
                (&pk[i].prepare(), &h_m.prepare())
            ].iter())
        ).unwrap(), one);
    }

    //aggregate siganature, pubkey
    let sig_sum = aggregate_signature(&sig, &pk);

    //verify
    //let h_m = hash_to_g2(&msg).into_affine();
    let pk_sum = aggregate_pubkey(&pk);

    assert_eq!(Bls12::final_exponentiation(
        &Bls12::miller_loop([
            (&g1.prepare(), &sig_sum.prepare()),
            (&pk_sum.prepare(), &h_m.prepare())
        ].iter())
    ).unwrap(), one);

    time += start.elapsed();
    let verify_time = time.subsec_nanos() as f64 / 1000_000f64
        + (time.as_secs() as f64) * 1000f64;
    println!("time is {:?} ms", verify_time);
}

fn main()
{
    //single_sig();
    //aggregate_sig();
    secure_aggregate_sig()
}
