use std::borrow::Borrow;
use std::marker::PhantomData;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_r1cs_std::alloc::{AllocationMode, AllocVar};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::{FieldOpsBounds, FieldVar};
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::select::CondSelectGadget;
use ark_relations::r1cs::{ConstraintSystemRef, Field, Namespace, SynthesisError};
use derivative::Derivative;

#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct NonZeroAffineVarGeneric<P, F, CF>
    where
        P: SWCurveConfig,
        CF: Field, // Constraint system field aka 'native'
        F: FieldVar<P::BaseField, CF>, // Represents elements of P::BaseField in CF either as-is or using non-native arithmetic.
{
    pub x: F,
    pub y: F,
    #[derivative(Debug = "ignore")]
    _p: PhantomData<P>,
    #[derivative(Debug = "ignore")]
    _cf: PhantomData<CF>,
}

impl<P, F, CF> AllocVar<Affine<P>, CF> for NonZeroAffineVarGeneric<P, F, CF>
    where
        P: SWCurveConfig,
        CF: Field,
        F: FieldVar<P::BaseField, CF>,
{
    fn new_variable<T: Borrow<Affine<P>>>(cs: impl Into<Namespace<CF>>, f: impl FnOnce() -> Result<T, SynthesisError>, mode: AllocationMode) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let point = f().map(|b| *b.borrow());
        let x = F::new_variable(ark_relations::ns!(cs, "x"), || point.map(|p| p.x), mode)?;
        let y = F::new_variable(ark_relations::ns!(cs, "y"), || point.map(|p| p.y), mode)?;
        let point_var = NonZeroAffineVarGeneric { x, y, _p: PhantomData, _cf: PhantomData };
        Ok(point_var)
    }
}

impl<P, F, CF> CondSelectGadget<CF> for NonZeroAffineVarGeneric<P, F, CF>
    where
        P: SWCurveConfig,
        CF: Field,
        F: FieldVar<P::BaseField, CF>,
{
    fn conditionally_select(cond: &Boolean<CF>, true_value: &Self, false_value: &Self) -> Result<Self, SynthesisError> {
        let x = cond.select(&true_value.x, &false_value.x)?;
        let y = cond.select(&true_value.y, &false_value.y)?;
        Ok(Self::new(x, y))
    }
}

impl<P, F, CF> R1CSVar<CF> for NonZeroAffineVarGeneric<P, F, CF>
    where
        P: SWCurveConfig,
        CF: Field,
        F: FieldVar<P::BaseField, CF>,
{
    type Value = Affine<P>;

    fn cs(&self) -> ConstraintSystemRef<CF> {
        self.x.cs().or(self.y.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        Ok(Affine::<P>::new(self.x.value()?, self.y.value()?))
    }
}

impl<P, F, CF> NonZeroAffineVarGeneric<P, F, CF>
    where
        P: SWCurveConfig,
        CF: Field,
        F: FieldVar<P::BaseField, CF>,
{
    pub fn new(x: F, y: F) -> Self {
        Self { x, y, _p: Default::default(), _cf: Default::default() }
    }

    pub fn add_unchecked(&self, other: &Self) -> Result<Self, SynthesisError>
        where for<'a> &'a F: FieldOpsBounds<'a, P::BaseField, F>
    {
        let (x1, y1) = (&self.x, &self.y);
        let (x2, y2) = (&other.x, &other.y);
        let numerator = y2 - y1;
        let denominator = x2 - x1;
        let lambda = numerator.mul_by_inverse_unchecked(&denominator)?;
        let x3 = lambda.square()? - x1 - x2;
        let y3 = lambda * &(x1 - &x3) - y1;
        Ok(Self::new(x3, y3))
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::CurveGroup;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::ns;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    use crate::tests::{BlsInBls, Tracker};

    use super::*;

    #[test]
    fn test_sum_native() {
        let rng = &mut test_rng();
        let cs = ConstraintSystem::<ark_bw6_761::Fr>::new_ref();
        let n = 10;
        let keys: Vec<ark_bls12_377::G1Affine> = (0..n).map(|_| ark_bls12_377::G1Affine::rand(rng)).collect();
        let mut tracker = Tracker::new(&cs);
        let mut key_vars = Vec::<NonZeroAffineVarGeneric<_, FpVar<ark_bw6_761::Fr>, _>>::new_witness(ns!(cs, "keys"), || Ok(keys.clone())).unwrap().into_iter();
        println!("allocating {} native points: {:?}", n, tracker.update(&cs));
        let mut sum = key_vars.next().unwrap();
        for key in key_vars {
            sum = sum.add_unchecked(&key).unwrap();
        }
        println!("summing {} native points: {:?}", n, tracker.update(&cs));
        assert_eq!(sum.value().unwrap(), keys.iter().sum::<ark_bls12_377::G1Projective>().into_affine());
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_sum_emulated() {
        let rng = &mut test_rng();
        let cs = ConstraintSystem::<ark_bls12_381::Fr>::new_ref();
        let n = 10;
        let keys: Vec<ark_bls12_381::G1Affine> = (0..n).map(|_| ark_bls12_381::G1Affine::rand(rng)).collect();
        let mut tracker = Tracker::new(&cs);
        let mut key_vars = Vec::<NonZeroAffineVarGeneric<_, BlsInBls, _>>::new_witness(ns!(cs, "keys"), || Ok(keys.clone())).unwrap().into_iter();
        println!("allocating {} emulated points: {:?}", n, tracker.update(&cs));
        let mut sum = key_vars.next().unwrap();
        for key in key_vars {
            sum = sum.add_unchecked(&key).unwrap();
        }
        println!("summing {} emulated points: {:?}", n, tracker.update(&cs));
        assert_eq!(sum.value().unwrap(), keys.iter().sum::<ark_bls12_381::G1Projective>().into_affine());
        assert!(cs.is_satisfied().unwrap());
    }
}