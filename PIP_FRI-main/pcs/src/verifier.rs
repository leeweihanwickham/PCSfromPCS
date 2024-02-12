use util::merkle_tree::MERKLE_ROOT_SIZE;
use util::random_oracle::RandomOracle;
use util::{
    algebra::{coset::Coset, field::Field},
    merkle_tree::MerkleTreeVerifier,
    query_result::QueryResult,
};

#[derive(Clone)]
pub struct Verifier<T: Field> {
    total_round: usize,
    interpolate_cosets: Vec<Coset<T>>,
    polynomial_roots: Vec<MerkleTreeVerifier>,
    function_root: Vec<MerkleTreeVerifier>,
    folding_root: Vec<MerkleTreeVerifier>,
    oracle: RandomOracle<T>,
    final_value: Option<T>,
    evaluation: Option<T>,
    open_point: Vec<T>,
    combination: Vec<T>,
}

impl<T: Field> Verifier<T> {
    pub fn new(
        total_round: usize,
        combination_length: usize,
        coset: &Vec<Coset<T>>,
        commits: Vec<[u8; MERKLE_ROOT_SIZE]>,
        oracle: &RandomOracle<T>,
    ) -> Self {
        Verifier {
            total_round,
            interpolate_cosets: coset.clone(),
            function_root: vec![],
            folding_root: vec![],
            oracle: oracle.clone(),
            polynomial_roots: commits
                .iter()
                .map(|x| MerkleTreeVerifier::new(coset[0].size() / 2, x))
                .collect(),
            final_value: None,
            evaluation: None,
            open_point: (0..total_round)
                .into_iter()
                .map(|_| T::random_element())
                .collect(),
            combination: (0..combination_length)
                .into_iter()
                .map(|_| T::random_element())
                .collect(),
        }
    }

    pub fn get_open_point(&self) -> (Vec<T>, Vec<T>) {
        (self.open_point.clone(), self.combination.clone())
    }

    pub fn set_evaluation(&mut self, evaluation: T) {
        self.evaluation = Some(evaluation);
    }

    pub fn set_function(&mut self, leave_number: usize, function_root: &[u8; MERKLE_ROOT_SIZE]) {
        self.function_root.push(MerkleTreeVerifier {
            merkle_root: function_root.clone(),
            leave_number,
        });
    }

    pub fn receive_folding_root(
        &mut self,
        leave_number: usize,
        folding_root: [u8; MERKLE_ROOT_SIZE],
    ) {
        self.folding_root.push(MerkleTreeVerifier {
            leave_number,
            merkle_root: folding_root,
        });
    }

    pub fn set_final_value(&mut self, value: T) {
        self.final_value = Some(value);
    }

    pub fn verify(
        &self,
        polynomial_proof: &Vec<QueryResult<T>>,
        folding_proof: &Vec<QueryResult<T>>,
        function_proof: &Vec<QueryResult<T>>,
    ) -> bool {
        let mut leaf_indices = self.oracle.query_list.clone();
        for i in 0..self.total_round {
            let domain_size = self.interpolate_cosets[i].size();
            leaf_indices = leaf_indices
                .iter_mut()
                .map(|v| *v % (domain_size >> 1))
                .collect();
            leaf_indices.sort();
            leaf_indices.dedup();

            if i == 0 {
                polynomial_proof
                    .iter()
                    .zip(self.polynomial_roots.iter())
                    .all(|(x, v)| x.verify_merkle_tree(&leaf_indices, v));
            } else {
                function_proof[i - 1].verify_merkle_tree(&leaf_indices, &self.function_root[i - 1]);
                folding_proof[i - 1].verify_merkle_tree(&leaf_indices, &self.folding_root[i - 1]);
            }

            let challenge = self.oracle.folding_challenges[i];
            let get_folding_value: Box<dyn Fn(&usize) -> T> = if i == 0 {
                Box::new(|x| {
                    let mut res = polynomial_proof[0].proof_values[x];
                    for poly in polynomial_proof.iter().skip(1) {
                        res *= self.oracle.rlc;
                        res += poly.proof_values[x];
                    }
                    res
                })
            } else {
                Box::new(|x| folding_proof[i - 1].proof_values[x])
            };

            let get_function_value: Box<dyn Fn(&usize) -> T> = if i == 0 {
                Box::new(|x| {
                    let mut res = T::from_int(0);
                    for v in polynomial_proof.iter().zip(self.combination.iter()) {
                        res += v.0.proof_values[x] * v.1.clone();
                    }
                    res
                })
            } else {
                Box::new(|x| function_proof[i - 1].proof_values[x])
            };
            for j in &leaf_indices {
                let x = (*get_folding_value)(j);
                let nx = (*get_folding_value)(&(j + domain_size / 2));
                let v =
                    x + nx + challenge * (x - nx) * self.interpolate_cosets[i].element_inv_at(*j);
                let x = (*get_function_value)(j);
                let nx = (*get_function_value)(&(j + domain_size / 2));
                let v = (v * challenge + (x + nx)) * challenge
                    + (x - nx) * self.interpolate_cosets[i].element_inv_at(*j);
                if i == self.total_round - 1 {
                    assert_eq!(v, self.final_value.unwrap());
                } else {
                    assert_eq!(v, folding_proof[i].proof_values[j]);
                }
                let x = (*get_function_value)(j);
                let nx = (*get_function_value)(&(j + domain_size / 2));
                let v = x
                    + nx
                    + self.open_point[i] * (x - nx) * self.interpolate_cosets[i].element_inv_at(*j);
                if i < self.total_round - 1 {
                    assert_eq!(v, function_proof[i].proof_values[j] * T::from_int(2));
                } else {
                    assert_eq!(v, self.evaluation.unwrap() * T::from_int(2));
                }
            }
        }
        true
    }
}
