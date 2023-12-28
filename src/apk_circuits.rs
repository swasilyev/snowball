use std::marker::PhantomData;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::{FieldOpsBounds, FieldVar};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::nonnative::AllocatedNonNativeFieldVar;
use ark_r1cs_std::fields::nonnative::params::OptimizationType;
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::ToBitsGadget;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use derivative::Derivative;

use crate::affine_gen::NonZeroAffineVarGeneric;

#[derive(Derivative)]
#[derivative(Debug, Clone)]
pub struct ApkCircuit<P: SWCurveConfig, CF: Field, F: FieldVar<P::BaseField, CF>> {
    keys: Vec<Affine<P>>,
    seed: Affine<P>,
    packed_bits: CF,
    #[derivative(Debug = "ignore")]
    _f: PhantomData<F>,
}

impl<P, CF, F> ConstraintSynthesizer<CF> for ApkCircuit<P, CF, F>
    where P: SWCurveConfig,
          CF: PrimeField,
          F: FieldVar<P::BaseField, CF>,
          for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF>) -> ark_relations::r1cs::Result<()> {
        let seed_const = NonZeroAffineVarGeneric::<P, F, CF>::new_constant(ark_relations::ns!(cs, "seed"), &self.seed)?;
        let key_vars = Vec::<NonZeroAffineVarGeneric::<P, F, CF>>::new_input(ark_relations::ns!(cs, "keys"), || Ok(self.keys))?;
        let packed_bits_var = FpVar::new_input(ark_relations::ns!(cs, "bitmask_packed"), || Ok(&self.packed_bits))?;
        let bit_vars = packed_bits_var.to_bits_le()?;

        let mut curr_sum = seed_const;
        for (b, key) in bit_vars.iter().zip(key_vars) {
            let next_sum = curr_sum.add_unchecked(&key)?;
            curr_sum = NonZeroAffineVarGeneric::<P, F, CF>::conditionally_select(b, &next_sum, &curr_sum)?;
        }
        Ok(())
    }
}

pub fn keys_to_limbs<F: PrimeField, CF: PrimeField, P: SWCurveConfig<BaseField=F>>(keys: &[Affine<P>]) -> Vec<CF> {
    keys.iter()
        .flat_map(|p| vec![p.x, p.y])
        .flat_map(|c| AllocatedNonNativeFieldVar::<F, CF>::get_limbs_representations(&c, OptimizationType::Constraints).unwrap())
        .collect()
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_bw6_761::BW6_761;
    use ark_groth16::{Groth16, PreparedVerifyingKey};
    use ark_r1cs_std::boolean::Boolean;
    use ark_r1cs_std::fields::nonnative::NonNativeFieldVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_snark::SNARK;
    use ark_std::{test_rng, UniformRand};
    use rand::Rng;
    use rand::rngs::OsRng;

    use super::*;

    #[test]
    fn apk_foreign() {
        let rng = &mut OsRng;
        let n = 3;
        let keys: Vec<ark_bls12_381::G1Affine> = (0..n).map(|_| ark_bls12_381::G1Affine::rand(rng)).collect();
        let bits: Vec<bool> = (0..n).map(|_| rng.gen_bool(0.9)).collect();
        let seed = ark_bls12_381::G1Affine::rand(rng); // TODO

        let cs = ConstraintSystem::<ark_bls12_381::Fr>::new_ref();
        let bit_vars = Vec::<Boolean<ark_bls12_381::Fr>>::new_constant(cs, bits.clone()).unwrap();
        let packed_bits = Boolean::le_bits_to_fp_var(&bit_vars).unwrap().value().unwrap();

        let circuit = ApkCircuit {
            keys: keys.clone(),
            seed,
            packed_bits,
            _f: PhantomData::<NonNativeFieldVar<ark_bls12_381::Fq, ark_bls12_381::Fr>>,
        };

        //TODO: circuit can be empty
        let (pk, vk) = Groth16::<Bls12_381>::circuit_specific_setup(circuit.clone(), rng).unwrap();
        let proof = Groth16::<Bls12_381>::prove(&pk, circuit.clone(), rng).unwrap();

        let pvk: PreparedVerifyingKey<Bls12_381> = vk.into();
        let mut pi = keys_to_limbs(&keys);
        pi.push(packed_bits);
        let pi = Groth16::<Bls12_381>::prepare_inputs(&pvk, &pi).unwrap();
        assert!(Groth16::<Bls12_381>::verify_proof_with_prepared_inputs(&pvk, &proof, &pi).unwrap());
    }

    #[test]
    fn apk_native() {
        let rng = &mut OsRng;
        let n = 3;
        let keys: Vec<ark_bls12_377::G1Affine> = (0..n).map(|_| ark_bls12_377::G1Affine::rand(rng)).collect();
        let bits: Vec<bool> = (0..n).map(|_| rng.gen_bool(0.9)).collect();
        let seed = ark_bls12_377::G1Affine::rand(rng); // TODO

        let cs = ConstraintSystem::<ark_bw6_761::Fr>::new_ref();
        let bit_vars = Vec::<Boolean<ark_bw6_761::Fr>>::new_constant(cs, bits.clone()).unwrap();
        let packed_bits = Boolean::le_bits_to_fp_var(&bit_vars).unwrap().value().unwrap();

        let circuit = ApkCircuit {
            keys: keys.clone(),
            seed,
            packed_bits,
            _f: PhantomData::<FpVar<ark_bw6_761::Fr>>,
        };

        //TODO: circuit can be empty
        let (pk, vk) = Groth16::<BW6_761>::circuit_specific_setup(circuit.clone(), rng).unwrap();
        let proof = Groth16::<BW6_761>::prove(&pk, circuit.clone(), rng).unwrap();

        let pvk: PreparedVerifyingKey<BW6_761> = vk.into();
        let mut pi: Vec<ark_bw6_761::Fr> = keys.iter().flat_map(|p| vec![p.x, p.y]).collect();
        pi.push(packed_bits);
        let pi = Groth16::<BW6_761>::prepare_inputs(&pvk, &pi).unwrap();
        assert!(Groth16::<BW6_761>::verify_proof_with_prepared_inputs(&pvk, &proof, &pi).unwrap());
    }

    #[test]
    fn test_bit_packing() {
        let rng = &mut test_rng();
        let n = 100;
        let bits: Vec<bool> = (0..n).map(|_| bool::rand(rng)).collect();

        let cs = ConstraintSystem::<ark_bls12_381::Fr>::new_ref();
        let bit_vars = Vec::<Boolean<ark_bls12_381::Fr>>::new_constant(cs, bits.clone()).unwrap();
        let bits_packed_var = Boolean::le_bits_to_fp_var(&bit_vars).unwrap();
        let bits_back: Vec<bool> = bits_packed_var.to_bits_le().unwrap().iter()
            .take(n)
            .map(|b| b.value().unwrap())
            .collect();
        assert_eq!(bits, bits_back);
    }

    #[test]
    fn test_limbs_foreign() {
        let limbs: Vec<ark_bls12_381::Fr> = keys_to_limbs(&[ark_bls12_381::G1Affine::rand(&mut test_rng())]);
        println!("bls12_381::G1Affine is represented with {} limbs in bls12_381::Fr", limbs.len());
    }
}