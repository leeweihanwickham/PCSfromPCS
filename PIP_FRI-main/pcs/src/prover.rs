use super::verifier::Verifier;
use util::algebra::polynomial::MultilinearPolynomial;

use util::merkle_tree::MERKLE_ROOT_SIZE;
use util::query_result::QueryResult;
use util::{
    algebra::{coset::Coset, field::Field},
    interpolation::InterpolateValue,
    random_oracle::RandomOracle,
};

#[derive(Clone)]
pub struct Prover<T: Field> {
    total_round: usize,
    combination: Option<Vec<T>>,
    interpolate_cosets: Vec<Coset<T>>,
    interpolate_polynomials: Vec<InterpolateValue<T>>,
    rlc_polynomial: Vec<T>,
    combined_function: Option<Vec<T>>,
    functions: Vec<InterpolateValue<T>>,
    foldings: Vec<InterpolateValue<T>>,
    oracle: RandomOracle<T>,
    final_value: Option<T>,
}

use std::sync::mpsc;
use std::thread;
impl<T: Field> Prover<T> {
    pub fn new_parallel(
        total_round: usize,
        interpolate_coset: &Vec<Coset<T>>,
        polynomials: Vec<MultilinearPolynomial<T>>,
        oracle: &RandomOracle<T>,
    ) -> Prover<T> {
        let (tx, rx) = mpsc::channel();
        for i in 0..polynomials.len() {
            let tx_clone = tx.clone();
            let coset = interpolate_coset[0].clone();
            let coeff = polynomials[i].coefficients().clone();
            thread::spawn(move || {
                tx_clone
                    .send((i, InterpolateValue::new(coset.fft(coeff))))
                    .unwrap();
            });
        }
        drop(tx);
        let mut data = vec![None; polynomials.len()];
        for received in rx {
            data[received.0] = Some(received.1);
        }
        let interpolate_polynomials = data.into_iter().map(|x| x.unwrap()).collect::<Vec<_>>();

        let mut rlc_polynomial = interpolate_polynomials[0].value.clone();
        for i in interpolate_polynomials.iter().skip(1) {
            for j in 0..rlc_polynomial.len() {
                rlc_polynomial[j] *= oracle.rlc;
                rlc_polynomial[j] += i.value[j];
            }
        }

        Prover {
            total_round,
            combination: None,
            interpolate_cosets: interpolate_coset.clone(),
            interpolate_polynomials,
            rlc_polynomial,
            combined_function: None,
            functions: vec![],
            foldings: vec![],
            oracle: oracle.clone(),
            final_value: None,
        }
    }

    pub fn new(
        total_round: usize,
        interpolate_coset: &Vec<Coset<T>>,
        polynomials: Vec<MultilinearPolynomial<T>>,
        oracle: &RandomOracle<T>,
    ) -> Prover<T> {
        let interpolate_polynomials = polynomials
            .iter()
            .map(|x| InterpolateValue::new(interpolate_coset[0].fft(x.coefficients().clone())))
            .collect::<Vec<_>>();
        let mut rlc_polynomial = interpolate_polynomials[0].value.clone();
        for i in interpolate_polynomials.iter().skip(1) {
            for j in 0..rlc_polynomial.len() {
                rlc_polynomial[j] *= oracle.rlc;
                rlc_polynomial[j] += i.value[j];
            }
        }

        Prover {
            total_round,
            combination: None,
            interpolate_cosets: interpolate_coset.clone(),
            interpolate_polynomials,
            rlc_polynomial,
            combined_function: None,
            functions: vec![],
            foldings: vec![],
            oracle: oracle.clone(),
            final_value: None,
        }
    }

    pub fn commit_polynomial(&self) -> Vec<[u8; MERKLE_ROOT_SIZE]> {
        self.interpolate_polynomials
            .iter()
            .map(|x| x.commit())
            .collect()
    }

    fn fold(values: &Vec<T>, parameter: T, coset: &Coset<T>) -> Vec<T> {
        let len = values.len() / 2;
        let res = (0..len)
            .into_iter()
            .map(|i| {
                let x = values[i];
                let nx = values[i + len];
                let new_v = (x + nx) + parameter * (x - nx) * coset.element_inv_at(i);
                new_v * T::INVERSE_2
            })
            .collect();
        res
    }

    pub fn commit_functions(
        &mut self,
        open_point: &Vec<T>,
        verifier: &mut Verifier<T>,
        combination: &Vec<T>,
    ) {
        let mut evaluation = None;
        let mut combined_function = (0..self.interpolate_cosets[0].size())
            .into_iter()
            .map(|i| combination[0] * self.interpolate_polynomials[0].value[i])
            .collect::<Vec<T>>();
        assert_eq!(combination.len(), self.interpolate_polynomials.len());
        for (i, poly) in combination
            .iter()
            .zip(self.interpolate_polynomials.iter())
            .skip(1)
        {
            for j in 0..combined_function.len() {
                combined_function[j] += i.clone() * poly.value[j];
            }
        }
        self.combined_function = Some(combined_function);
        self.combination = Some(combination.clone());
        for round in 0..self.total_round {
            let next_evaluation = Self::fold(
                if round == 0 {
                    self.combined_function.as_mut().unwrap()
                } else {
                    &self.functions[round - 1].value
                },
                open_point[round],
                &self.interpolate_cosets[round],
            );
            if round < self.total_round - 1 {
                self.functions.push(InterpolateValue::new(next_evaluation));
            } else {
                evaluation = Some(next_evaluation[0]);
            }
        }
        for i in 0..(self.total_round - 1) {
            let function = &self.functions[i];
            verifier.set_function(function.leave_num(), &function.commit());
        }
        verifier.set_evaluation(evaluation.unwrap());
    }

    pub fn commit_foldings(&self, verifier: &mut Verifier<T>) {
        for i in 0..(self.total_round - 1) {
            let interpolation = &self.foldings[i];
            verifier.receive_folding_root(interpolation.leave_num(), interpolation.commit());
        }
        verifier.set_final_value(self.final_value.unwrap());
    }

    fn evaluation_next_domain(&self, round: usize, challenge: T) -> Vec<T> {
        let mut res = vec![];
        let len = self.interpolate_cosets[round].size();
        let get_folding_value = if round == 0 {
            &self.rlc_polynomial
        } else {
            &self.foldings[round - 1].value
        };
        let coset = &self.interpolate_cosets[round];
        for i in 0..(len / 2) {
            let x = get_folding_value[i];
            let nx = get_folding_value[i + len / 2];
            let new_v = (x + nx) + challenge * (x - nx) * coset.element_inv_at(i);
            let fv = if round == 0 {
                self.combined_function.as_ref().unwrap()
            } else {
                &self.functions[round - 1].value
            };
            let x = fv[i];
            let nx = fv[i + len / 2];
            let new_v =
                (new_v * challenge + (x + nx)) * challenge + (x - nx) * coset.element_inv_at(i);
            res.push(new_v);
        }
        res
    }

    pub fn prove(&mut self) {
        for i in 0..self.total_round {
            let challenge = self.oracle.folding_challenges[i];
            let next_evalutation = self.evaluation_next_domain(i, challenge);
            if i < self.total_round - 1 {
                self.foldings.push(InterpolateValue::new(next_evalutation));
            } else {
                self.final_value = Some(next_evalutation[0]);
            }
        }
    }

    pub fn query(
        &self,
    ) -> (
        Vec<QueryResult<T>>,
        Vec<QueryResult<T>>,
        Vec<QueryResult<T>>,
    ) {
        let mut folding_res = vec![];
        let mut functions_res = vec![];
        let mut polynomial_res = None;
        let mut leaf_indices = self.oracle.query_list.clone();

        for i in 0..self.total_round {
            let len = self.interpolate_cosets[i].size();
            leaf_indices = leaf_indices.iter_mut().map(|v| *v % (len >> 1)).collect();
            leaf_indices.sort();
            leaf_indices.dedup();

            if i == 0 {
                polynomial_res = Some(
                    self.interpolate_polynomials
                        .iter()
                        .map(|x| x.query(&leaf_indices))
                        .collect::<Vec<_>>(),
                );
            } else {
                functions_res.push(self.functions[i - 1].query(&leaf_indices));
                folding_res.push(self.foldings[i - 1].query(&leaf_indices));
            }
        }
        (polynomial_res.unwrap(), folding_res, functions_res)
    }
}
