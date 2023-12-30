use std::marker::PhantomData;

use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::{Field, PrimeField, Zero};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::{FieldOpsBounds, FieldVar};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::nonnative::NonNativeFieldVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::ns;
use ark_relations::r1cs::SynthesisError;
use derivative::Derivative;

use crate::affine_gen::NonZeroAffineVarGeneric;

#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct SumAccumulator<P, F, CF>
    where
        P: SWCurveConfig,
        CF: Field, // Constraint system field aka 'native'
        F: FieldVar<P::BaseField, CF>, // Represents elements of P::BaseField in CF either as-is or using non-native arithmetic.
{
    pub x1_prev: F,
    pub y1_prev: F,
    pub lambda_prev: F,
    pub x3_prev: F,

    #[derivative(Debug = "ignore")]
    _p: PhantomData<P>,
    #[derivative(Debug = "ignore")]
    _cf: PhantomData<CF>,
}

impl<P: SWCurveConfig, CF: Field, F: FieldVar<P::BaseField, CF>> SumAccumulator<P, F, CF>
    where for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F> {
    fn init(p1: NonZeroAffineVarGeneric<P, F, CF>, p2: NonZeroAffineVarGeneric<P, F, CF>) -> Result<Self, SynthesisError> {
        let numerator = &p2.y - &p1.y;
        let denominator = &p2.x - &p1.x;
        assert!(!denominator.value()?.is_zero());
        let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
        let x3 = lambda.square()? - &p1.x - &p2.x;
        let acc = Self {
            x1_prev: p1.x,
            y1_prev: p1.y,
            lambda_prev: lambda,
            x3_prev: x3,
            _p: PhantomData,
            _cf: PhantomData,
        };
        Ok(acc)
    }

    // Generic implementation. Suboptimal for non-native as it can't enjoy `mul_without_reduce`

    // fn add(&self, p: NonZeroAffineVarGeneric<P, F, CF>) -> Result<Self, SynthesisError> {
    //     let numerator = &self.lambda_prev * (&self.x3_prev - &self.x1_prev) + &self.y1_prev + &p.y;
    //     let denominator = &p.x - &self.x3_prev;
    //     assert!(!denominator.value()?.is_zero());
    //     let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
    //     let x3 = lambda.square()? - &self.x3_prev - &p.x;
    //     let acc = Self {
    //         x1_prev: p.x,
    //         y1_prev: p.y,
    //         lambda_prev: lambda,
    //         x3_prev: x3,
    //         _p: PhantomData,
    //         _cf: PhantomData,
    //     };
    //     Ok(acc)
    // }

    fn finalize(self) -> Result<NonZeroAffineVarGeneric<P, F, CF>, SynthesisError> {
        let y3_prev = &self.lambda_prev * (&self.x1_prev - &self.x3_prev) - &self.y1_prev;
        let res = NonZeroAffineVarGeneric::new(self.x3_prev, y3_prev);
        Ok(res)
    }
}

// Native field impl.
impl<F: PrimeField, P: SWCurveConfig<BaseField=F>> SumAccumulator<P, FpVar<F>, F> {
    fn add(&self, p: NonZeroAffineVarGeneric<P, FpVar<F>, F>) -> Result<Self, SynthesisError> {
        let numerator = &self.lambda_prev * (&self.x3_prev - &self.x1_prev) + &self.y1_prev + &p.y;
        let denominator = &p.x - &self.x3_prev;
        assert!(!denominator.value()?.is_zero());
        let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
        let x3 = lambda.square()? - &self.x3_prev - &p.x;
        let acc = Self {
            x1_prev: p.x,
            y1_prev: p.y,
            lambda_prev: lambda,
            x3_prev: x3,
            _p: PhantomData,
            _cf: PhantomData,
        };
        Ok(acc)
    }
}

// Emulated field iml: saves `1` reduction of `3`.
// `lambda  =  (lambda_prev * (x3_prev - x1_prev) + y1_prev + y)  /  (x - x3_prev)` that requires `2` reductions.
// Instead we will prove  `lambda * (x - x3_prev) + (lambda_prev * (x1_prev - x3_prev)) - y1_prev - y  =  0`.
impl<F: PrimeField, P: SWCurveConfig<BaseField=F>, CF: PrimeField> SumAccumulator<P, NonNativeFieldVar<F, CF>, CF> {
    fn add(&self, p: NonZeroAffineVarGeneric<P, NonNativeFieldVar<F, CF>, CF>) -> Result<Self, SynthesisError> {
        // let numerator = &self.lambda_prev * (&self.x3_prev - &self.x1_prev) + &self.y1_prev + &p.y;
        // let denominator = &p.x - &self.x3_prev;
        // assert!(!denominator.value()?.is_zero());
        // let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
        //
        //
        assert_ne!(p.x, self.x3_prev);
        let lambda = (self.lambda_prev.value()? * (self.x3_prev.value()? - self.x1_prev.value()?) + self.y1_prev.value()? + p.y.value()?)
            / (p.x.value()? - self.x3_prev.value()?);
        let lambda = NonNativeFieldVar::<F, CF>::new_witness(ns!(p.cs(), "lambda"), || Ok(lambda))?;

        let prod1 = lambda.mul_without_reduce(&(&p.x - &self.x3_prev))?;
        let prod2 = self.lambda_prev.mul_without_reduce(&(&self.x1_prev - &self.x3_prev))?;
        let zero = (prod1 + prod2).reduce()? - &self.y1_prev - &p.y;
        zero.enforce_equal(&NonNativeFieldVar::zero())?;

        let x3 = lambda.square()? - &self.x3_prev - &p.x;

        let acc = Self {
            x1_prev: p.x,
            y1_prev: p.y,
            lambda_prev: lambda,
            x3_prev: x3,
            _p: PhantomData,
            _cf: PhantomData,
        };
        Ok(acc)
    }
}


#[cfg(test)]
mod tests {
    use ark_bls12_381;
    use ark_ec::CurveGroup;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::ns;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    use crate::tests::{BlsInBls, Tracker};

    use super::*;

    #[test]
    fn test_acc_native() {
        let rng = &mut test_rng();
        let cs = ConstraintSystem::<ark_bw6_761::Fr>::new_ref();
        let n = 10;
        let keys: Vec<ark_bls12_377::G1Affine> = (0..n).map(|_| ark_bls12_377::G1Affine::rand(rng)).collect();
        let mut tracker = Tracker::new(&cs);
        let mut key_vars = Vec::<NonZeroAffineVarGeneric<_, FpVar<ark_bw6_761::Fr>, _>>::new_witness(ns!(cs, "keys"), || Ok(keys.clone())).unwrap().into_iter();
        println!("allocating {} native points: {:?}", n, tracker.update(&cs));
        let mut acc = SumAccumulator::init(key_vars.next().unwrap(), key_vars.next().unwrap()).unwrap();
        for key in key_vars {
            acc = acc.add(key).unwrap();
        }
        let sum = acc.finalize().unwrap();
        println!("summing {} native points: {:?}", n, tracker.update(&cs));
        assert_eq!(sum.value().unwrap(), keys.iter().sum::<ark_bls12_377::G1Projective>().into_affine());
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_acc_emulated() {
        let rng = &mut test_rng();
        let cs = ConstraintSystem::<ark_bls12_381::Fr>::new_ref();
        let n = 10;
        let keys: Vec<ark_bls12_381::G1Affine> = (0..n).map(|_| ark_bls12_381::G1Affine::rand(rng)).collect();
        let mut tracker = Tracker::new(&cs);
        let mut key_vars = Vec::<NonZeroAffineVarGeneric<_, BlsInBls, _>>::new_witness(ns!(cs, "keys"), || Ok(keys.clone())).unwrap().into_iter();
        println!("allocating {} emulated points: {:?}", n, tracker.update(&cs));
        let mut acc = SumAccumulator::init(key_vars.next().unwrap(), key_vars.next().unwrap()).unwrap();
        for key in key_vars {
            acc = acc.add(key).unwrap();
        }
        let sum = acc.finalize().unwrap();
        println!("summing {} emulated points: {:?}", n, tracker.update(&cs));
        assert_eq!(sum.value().unwrap(), keys.iter().sum::<ark_bls12_381::G1Projective>().into_affine());
        assert!(cs.is_satisfied().unwrap());
    }
}