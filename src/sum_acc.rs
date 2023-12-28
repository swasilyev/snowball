use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::Field;

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
    use ark_std::{test_rng, UniformRand};

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
}