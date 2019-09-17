extern crate pairing;
extern crate rand;
extern crate blake2;
extern crate byteorder;
//extern crate generic_array;

use byteorder::{ReadBytesExt, BigEndian};
use rand::{SeedableRng, Rng, Rand,XorShiftRng};
use rand::chacha::ChaChaRng;
//use generic_array::GenericArray;
use pairing::bls12_381::*;
use pairing::*;
use blake2::{Blake2b, Digest, Blake2s};
use std::fmt;
use std::time::{Duration, Instant};

fn read_fr(from: &[u8]) -> FrRepr {
    assert_eq!(from.len(), 32);

    let mut f = FrRepr::default();
    f.read_le(from).expect("length is 32 bytes");

    f
}
//hash msg to a point in G2
fn hash_to_g2(msg: &[u8])-> G2
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

fn hash_pks(pks:&Vec<G1Affine>)-> Vec<FrRepr>{
    let mut t = Vec::new();
    let mut h = {
        let mut h = Blake2s::default();
        for pk in pks.iter() {
            h.input(G1Compressed::from_affine(*pk).as_ref());
        }
        h.result()
    };
    let mut pkHashImage = [0u8;36];
    (&mut pkHashImage[4..36]).copy_from_slice(&(unsafe { &*h })[..]);
    for i in 0..27{
        pkHashImage[3] = i;
        let mut h1 = Blake2s::default();
        h1.input(&pkHashImage);
        let f = read_fr(&h1.result());
        t.push(f);
    }
    return t;
}

fn aggregate_pubkey(pks:&Vec<G1Affine>) -> G1Affine{
    let t = hash_pks(&pks);
    let mut pubkey_sum = G1::zero();
    for (ti,pki) in t.iter().zip(pks.iter()){
        pubkey_sum.add_assign(&pki.mul(*ti));
    }

    pubkey_sum.into_affine()
}

fn aggregate_signature(sigs:&Vec<G2Affine>, pks:&Vec<G1Affine>) -> G2Affine{
    let t = hash_pks(&pks);
    let mut pubkey_sum = G2::zero();
    for (ti,sigi) in t.iter().zip(sigs.iter()){
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

    let msg:[u8;32] = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31];
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

fn aggregate_sig(){
    let one = Fq12::one();
    let msg:[u8;32] = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31];
    //@TODO: optimize hash_to_g2 implementation
    let h_m = hash_to_g2(&msg).into_affine();

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let mut g1 = G1Affine::one();
    let mut sk = Vec::new();
    let mut pk = Vec::new();
    let mut sig = Vec::new();

    let mut aux_verify_coeffs = Vec::new();

    for _ in 0..27 {
        let sk_i =Fr::rand(&mut rng);
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
    for i in 0..1{
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
    for i in 0..27{
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

fn secure_aggregate_sig(){
    const msg_len:usize = 1024000;
    let one = Fq12::one();
    let mut msg= [0u8;msg_len];
    for i in 0..msg_len{
        msg[i] = (i % 256) as u8;
    }
    let mut time = Duration::new(0, 0);

    //@TODO: optimize hash_to_g2 implementation

    let h_m = hash_to_g2(&msg).into_affine();

    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let mut g1 = G1Affine::one();
    let mut sk = Vec::new();
    let mut pk = Vec::new();
    let mut sig = Vec::new();

    let mut aux_verify_coeffs = Vec::new();
    //generate simulated msg
    for _ in 0..27 {
        let sk_i =Fr::rand(&mut rng);
        sk.push(sk_i);
        pk.push(g1.mul(sk_i).into_affine());//A
        sig.push(h_m.mul(sk_i).into_affine());//A

        let rand_coeffs = Fr::rand(&mut rng);
        aux_verify_coeffs.push(rand_coeffs);
    }

    //verify one by one
    g1.negate();
    let start = Instant::now();
    for i in 0..1{
        assert_eq!(Bls12::final_exponentiation(
            &Bls12::miller_loop([
                (&g1.prepare(), &sig[i].prepare()),
                (&pk[i].prepare(), &h_m.prepare())
            ].iter())
        ).unwrap(), one);
    }

    //aggregate siganature, pubkey
    let sig_sum = aggregate_signature(&sig, &pk);
    let pk_sum = aggregate_pubkey(&pk);

    //verify
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
