use std::marker::PhantomData;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::Field;
use ark_r1cs_std::fields::{FieldOpsBounds, FieldVar};
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

    fn start(p1: NonZeroAffineVarGeneric<P, F, CF>, p2: NonZeroAffineVarGeneric<P, F, CF>) -> Result<Self, SynthesisError> {
        let numerator = &p2.y - &p1.y;
        let denominator = &p2.x - &p1.x;
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

    fn stop(self) -> Result<NonZeroAffineVarGeneric<P, F, CF>, SynthesisError> {
        let y3_prev = &self.lambda_prev * (&self.x1_prev - &self.x3_prev) - &self.y1_prev;
        let res = NonZeroAffineVarGeneric::new(self.x3_prev, y3_prev);
        Ok(res)
    }

// fn add(&self, p: Affine<P>) -> Self {
//     let numerator = self.lambda_prev * (self.x3_prev - self.x1_prev) + self.y1_prev + p.y;
//     let denominator = p.x - self.x3_prev;
//     let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
//     let x3 = lambda.square()? - self.x3_prev - p.x;
//     Self {
//         x1_prev: p.x,
//         y1_prev: p.y,
//         lambda_prev: lambda,
//         x3_prev: x3,
//         _p: PhantomData,
//         _cf: PhantomData,
//     }
// }
}

struct SumAcc<F: Field> {
    x1_prev: F,
    y1_prev: F,
    lambda_prev: F,
    x3_prev: F,
}

impl<F: Field> SumAcc<F> {
    fn start<P: SWCurveConfig<BaseField=F>>(p1: Affine<P>, p2: Affine<P>) -> Self {
        let numerator = p2.y - p1.y;
        let denominator = p2.x - p1.x;
        let lambda = numerator / denominator;
        let x3 = lambda.square() - p1.x - p2.x;
        Self {
            x1_prev: p1.x,
            y1_prev: p1.y,
            lambda_prev: lambda,
            x3_prev: x3,
        }
    }

    fn add<P: SWCurveConfig<BaseField=F>>(&mut self, p: Affine<P>) {
        let numerator = self.lambda_prev * (self.x3_prev - self.x1_prev) + self.y1_prev + p.y;
        let denominator = p.x - self.x3_prev;
        let lambda = numerator / denominator;
        self.x3_prev = lambda.square() - self.x3_prev - p.x;
        self.x1_prev = p.x;
        self.y1_prev = p.y;
        self.lambda_prev = lambda;
    }

    fn stop<P: SWCurveConfig<BaseField=F>>(&self) -> Affine<P> {
        let y3 = self.lambda_prev * (self.x1_prev - self.x3_prev) - self.y1_prev;
        Affine::<P>::new_unchecked(self.x3_prev, y3)
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::G1Projective;
    use ark_ec::CurveGroup;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::fields::nonnative::NonNativeFieldVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};
    use crate::tests::Tracker;

    use super::*;

    #[test]
    fn test_one() {
        let rng = &mut test_rng();
        let p1 = ark_bls12_381::G1Affine::rand(rng);
        let p2 = ark_bls12_381::G1Affine::rand(rng);
        let acc = SumAcc::start(p1, p2);
        assert_eq!(acc.stop(), (p1 + p2).into_affine());
    }

    #[test]
    fn test_many() {
        let rng = &mut test_rng();
        let n = 100;
        let ps: Vec<ark_bls12_381::G1Affine> = (0..n).map(|_| ark_bls12_381::G1Affine::rand(rng)).collect();
        let mut acc = SumAcc::start(ps[0], ps[1]);
        for p in &ps[2..] {
            acc.add(*p);
        }
        assert_eq!(acc.stop::<ark_bls12_381::g1::Config>(), ps.iter().sum::<G1Projective>().into_affine());
    }

    #[test]
    fn test_foreign_acc() {
        let rng = &mut test_rng();
        let cs = ConstraintSystem::<ark_bls12_381::Fr>::new_ref();
        let p1 = ark_bls12_381::G1Affine::rand(rng);
        let p2 = ark_bls12_381::G1Affine::rand(rng);
        let mut tracker = Tracker::new(&cs);
        let p1_var = NonZeroAffineVarGeneric::<_, NonNativeFieldVar<ark_bls12_381::Fq, ark_bls12_381::Fr>, _>::new_witness(ark_relations::ns!(cs, "p1"), || Ok(&p1)).unwrap();
        let p2_var = NonZeroAffineVarGeneric::<_, NonNativeFieldVar<ark_bls12_381::Fq, ark_bls12_381::Fr>, _>::new_witness(ark_relations::ns!(cs, "p2"), || Ok(&p2)).unwrap();
        println!("allocating 2 points: {:?}", tracker.update(&cs));
        let acc = SumAccumulator::start(p1_var, p2_var).unwrap();
        println!("starting the acc: {:?}", tracker.update(&cs));
        let sum = acc.stop().unwrap();
        println!("stoping the acc: {:?}", tracker.update(&cs));
        assert_eq!(sum.value().unwrap(), (p1 + p2).into_affine());
        assert!(cs.is_satisfied().unwrap());
    }
}