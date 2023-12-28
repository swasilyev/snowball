mod affine_gen;
mod apk_circuits;
mod sum_acc;

#[cfg(test)]
mod tests {
    use ark_ff::Field;
    use ark_relations::r1cs::ConstraintSystemRef;
    use derivative::Derivative;

    #[derive(Derivative)]
    #[derivative(Debug, Clone)]
    pub struct Tracker {
        num_constraints: usize,
        num_witness_variables: usize,
        num_instance_variables: usize,
    }

    impl Tracker {
        pub fn new<F: Field>(cs: &ConstraintSystemRef<F>) -> Self {
            Self {
                num_constraints: cs.num_constraints(),
                num_witness_variables: cs.num_witness_variables(),
                num_instance_variables: cs.num_instance_variables(),
            }
        }

        pub fn update<F: Field>(&mut self, cs: &ConstraintSystemRef<F>) -> Self {
            let new = Self::new(cs);
            let delta = Self {
                num_constraints: new.num_constraints - self.num_constraints,
                num_witness_variables: new.num_witness_variables - self.num_witness_variables,
                num_instance_variables: new.num_instance_variables - self.num_instance_variables,
            };
            *self = new;
            delta
        }
    }
}