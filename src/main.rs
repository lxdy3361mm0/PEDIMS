use anyhow::Result;
use log::{Level, LevelFilter};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::util::timing::TimingTree;
use plonky2_sha256::circuit::{array_to_bits, range_proof};
use sha2::{Digest, Sha256};
use rand::Rng;


pub fn u32_array_to_bits(bytes: &[u32]) -> Vec<bool> {
    let mut ret = Vec::new();
    for &byte in bytes {
        for i in (0..32).rev() {
            let b = (byte >> i) & 1;
            ret.push(b == 1);
        }
    }
    ret
}

pub fn u8_array_to_bits(bytes: &[u8]) -> Vec<bool> {
    let mut ret = Vec::new();
    for &byte in bytes {
        for i in (0..8).rev() {
            let b = (byte >> i) & 1;
            ret.push(b == 1);
        }
    }
    ret
}

pub fn bits_to_u8_array(bits: Vec<bool>) -> Vec<u8> {
    let mut ret = Vec::new();
    let len = bits.len();
    
    for i in (0..len).step_by(8) {
        let mut byte = 0u8;
        for j in 0..8 {
            if i + j < len && bits[i + j] {
                byte |= 1 << (7 - j);
            }
        }
        ret.push(byte);
    }
    
    ret
}

pub fn prove_sha256(msg: &mut [u8], min: u8, max: u8, sk: &mut [u32]) -> Result<()> {
    //private key of user:sk
    let sk_hash_bits = u32_array_to_bits(sk);
    let sk_u8 = bits_to_u8_array(sk_hash_bits.clone());
    
    //public key of user:pk
    let mut hasher = Sha256::new();
    hasher.update(&sk_u8);
    let pk = hasher.finalize();
    let pk_u : Vec<u8> = pk.into_iter().collect();
    println!("pk: {:#04X}", pk);
    
    //token[] += creator||salt_claim
    let mut rng = rand::thread_rng();
    for i in 0..51{
        let n : u8 = rng.gen();
        msg[i + 7] = n;
    }
    
    let mut waste = vec![0; 12 as usize];
    
    for i in 0..8{
        waste[i] = sk[i];//waste[] += sk
    }
    for i in 0..4{
        let n : u32 = rng.gen();
        waste[i + 8] = n;//waste[] += salt_waste
    }
    
    let msg_hash_bits = u8_array_to_bits(msg);
    
    let waste_hash_bits = u32_array_to_bits(&waste);
    let waste_u8 = bits_to_u8_array(waste_hash_bits.clone());
    
    let mut hasher = Sha256::new();
    hasher.update(msg);
    let hash = hasher.finalize();
    let hash_claim: Vec<u8> = hash.into_iter().collect();
    println!("Hashclaim: {:#04X}", hash);
    
    let mut message = vec![0; 80 as usize];
    let mut salt_sign = vec![0; 16 as usize];
    for i in 0..32{
        message[i] = hash_claim[i];
        message[32 + i] = pk_u[i];
    }
    for i in 0..16{
        let n : u8 = rng.gen();
        message[64 + i] = n;
        salt_sign[i] = n;
    }
    
    let digest_len = u8_array_to_bits(&message).len();
    
    let salt_sign_bits = u8_array_to_bits(&salt_sign);
    
    let mut hasher = Sha256::new();
    hasher.update(waste_u8.clone());
    let waste = hasher.finalize();
    println!("Waste: {:#04X}", waste);
    
    let mut hasher = Sha256::new();
    hasher.update(message.clone());
    let message_digest = hasher.finalize();
    println!("message_digest: {:#04X}", message_digest);
    
    let mut rp_min = vec![0; 3 as usize];
    let mut rp_max = vec![0; 3 as usize];
    
    rp_min[0] = min;
    rp_max[0] = max;
    rp_min[1] = min;
    rp_max[1] = max;
    rp_min[2] = min;
    rp_max[2] = max;
    
    let min_bits = u8_array_to_bits(&rp_min);
    let max_bits = u8_array_to_bits(&rp_max);
    
    let range_len = max_bits.len();
    let hash_len = msg_hash_bits.len();
    let waste_len = waste_hash_bits.len();
    let sk_len = sk_hash_bits.len();
    let salt_len = salt_sign_bits.len();
    let mut msg_length = 0;
    
    for i in 0..range_len{
        if max_bits[i] == true{
            msg_length = range_len - 1 - i;
            break;
        }
    }
    msg_length = msg_length + 1;
    
    println!("block count: {}", (range_len + 65 + 511) / 512);
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let proof = range_proof(&mut builder, range_len as u64, hash_len as u64, waste_len as u64, sk_len as u64, salt_len as u64, digest_len as u64, msg_length as usize);
    
    let mut pw = PartialWitness::new();
    
    for i in 0..range_len {
        pw.set_bool_target(proof.min[i], min_bits[i]);
        pw.set_bool_target(proof.max[i], max_bits[i]);
    }
    for i in 0..hash_len {
        pw.set_bool_target(proof.hash_msg[i], msg_hash_bits[i]);
    }
    for i in 0..waste_len {
        pw.set_bool_target(proof.waste_pre[i], waste_hash_bits[i]);
    }
    for i in 0..sk_len {
        pw.set_bool_target(proof.sk[i], sk_hash_bits[i]);
    }
    
    for i in 0..salt_len {
        pw.set_bool_target(proof.salt_sign[i], salt_sign_bits[i]);
    }
    
    let expected_res = array_to_bits(hash.as_slice());
    for i in 0..expected_res.len() {
        if expected_res[i] {
            builder.assert_one(proof.digest[i].target);
        } else {
            builder.assert_zero(proof.digest[i].target);
        }
    }
    
    let expected_res = array_to_bits(waste.as_slice());
    for i in 0..expected_res.len() {
        if expected_res[i] {
            builder.assert_one(proof.waste[i].target);
        } else {
            builder.assert_zero(proof.waste[i].target);
        }
    }
    
    let expected_res = array_to_bits(pk.as_slice());
    for i in 0..expected_res.len() {
        if expected_res[i] {
            builder.assert_one(proof.pk[i].target);
        } else {
            builder.assert_zero(proof.pk[i].target);
        }
    }
    
    let expected_res = array_to_bits(message_digest.as_slice());
    for i in 0..expected_res.len() {
        if expected_res[i] {
            builder.assert_one(proof.message_digest[i].target);
        } else {
            builder.assert_zero(proof.message_digest[i].target);
        }
    }

    println!(
        "Constructing inner proof with {} gates",
        builder.num_gates()
    );
    let data = builder.build::<C>();
    let timing = TimingTree::new("prove", Level::Debug);
    let proof = data.prove(pw).unwrap();
    timing.print();
    let proof_bytes = proof.to_bytes();
    println!("Proof size: {} KB", proof_bytes.len() / 1024);

    let timing = TimingTree::new("verify", Level::Debug);
    let res = data.verify(proof);
    timing.print();

    res
}

fn main() -> Result<()> {
    // Initialize logging
    let mut builder = env_logger::Builder::from_default_env();
    builder.format_timestamp(None);
    builder.filter_level(LevelFilter::Debug);
    builder.try_init()?;
    
    let mut rng = rand::thread_rng();
    
    for _ in 0..9
    {
        let mut msg = vec![0; 58 as usize];
        let max = rng.gen::<u8>();
        let min = rng.gen_range(0..max);
        msg[4] = rng.gen_range(min..max);
        msg[5] = rng.gen_range(min..max);
        msg[6] = rng.gen_range(min..max);
        msg[0] = rng.gen::<u8>();
        msg[1] = rng.gen::<u8>();
        msg[2] = rng.gen::<u8>();
        msg[3] = rng.gen::<u8>();
    
        let mut sk = vec![0; 8 as usize];
        for i in 0..8{
            let n : u32 = rng.gen();
            sk[i] = n;
        }
        
        println!("min: {}", min);
        println!("x: {}", msg[4]);
        println!("max: {}", max);
        let _ = prove_sha256(&mut msg, min, max, &mut sk);
    }
    
    let mut msg = vec![0; 58 as usize];
    let max = rng.gen::<u8>();
    let min = rng.gen_range(0..max);
    msg[4] = rng.gen_range(min..max);
    msg[5] = rng.gen_range(min..max);
    msg[6] = rng.gen_range(min..max);
    msg[0] = rng.gen::<u8>();
    msg[1] = rng.gen::<u8>();
    msg[2] = rng.gen::<u8>();
    msg[3] = rng.gen::<u8>();
    
    let mut sk = vec![0; 8 as usize];
    for i in 0..8{
        let n : u32 = rng.gen();
        sk[i] = n;
    }
    
    println!("min: {}", min);
    println!("x: {}", msg[4]);
    println!("max: {}", max);
    prove_sha256(&mut msg, min, max, &mut sk)
    
}
