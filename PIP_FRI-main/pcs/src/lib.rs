pub mod prover;
pub mod verifier;

#[cfg(test)]
mod tests {
    use crate::{prover::Prover, verifier::Verifier};
    use util::{
        algebra::{
            coset::Coset,
            field::{ft255::Ft255, mersenne61_ext::Mersenne61Ext, Field},
            polynomial::MultilinearPolynomial,
        },
        merkle_tree::MERKLE_ROOT_SIZE,
        random_oracle::RandomOracle,
    };
    use util::{CODE_RATE, SECURITY_BITS};

    fn output_proof_size<T: Field>(variable_num: usize, poly_num: usize) -> usize {
        let polynomial = (0..poly_num)
            .into_iter()
            .map(|_| MultilinearPolynomial::random_polynomial(variable_num))
            .collect::<Vec<_>>();
        let mut interpolate_cosets = vec![Coset::new(
            1 << (variable_num + CODE_RATE),
            T::random_element(),
        )];
        for i in 1..variable_num {
            interpolate_cosets.push(interpolate_cosets[i - 1].pow(2));
        }
        let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
        let mut prover = Prover::new(variable_num, &interpolate_cosets, polynomial, &oracle);
        let commits = prover.commit_polynomial();
        let mut verifier = Verifier::new(
            variable_num,
            poly_num,
            &interpolate_cosets,
            commits,
            &oracle,
        );
        let (open_point, combination) = verifier.get_open_point();

        prover.commit_functions(&open_point, &mut verifier, &combination);
        prover.prove();
        prover.commit_foldings(&mut verifier);
        let (polynomial_proof, folding_proof, function_proof) = prover.query();
        assert!(verifier.verify(&polynomial_proof, &folding_proof, &function_proof));
        folding_proof.iter().map(|x| x.proof_size()).sum::<usize>()
            + polynomial_proof
                .iter()
                .map(|x| x.proof_size())
                .sum::<usize>()
            + function_proof.iter().map(|x| x.proof_size()).sum::<usize>()
            + variable_num * MERKLE_ROOT_SIZE * 2
    }

    // fn output_proof_size(variable_num: usize, poly_num: usize) -> usize {
    //     let polynomial = (0..poly_num)
    //         .into_iter()
    //         .map(|_| MultilinearPolynomial::random_polynomial(variable_num))
    //         .collect::<Vec<_>>();
    //     let mut interpolate_cosets = vec![Coset::new(
    //         1 << (variable_num + CODE_RATE),
    //         Mersenne61Ext::random_element(),
    //     )];
    //     for i in 1..variable_num {
    //         interpolate_cosets.push(interpolate_cosets[i - 1].pow(2));
    //     }
    //     let oracle = RandomOracle::new(variable_num, SECURITY_BITS / CODE_RATE);
    //     let mut prover = Prover::new(variable_num, &interpolate_cosets, polynomial, &oracle);
    //     let commits = prover.commit_polynomial();
    //     let mut verifier = Verifier::new(
    //         variable_num,
    //         poly_num,
    //         &interpolate_cosets,
    //         commits,
    //         &oracle,
    //     );
    //     let (open_point, combination) = verifier.get_open_point();

    //     prover.commit_functions(&open_point, &mut verifier, &combination);
    //     prover.prove();
    //     prover.commit_foldings(&mut verifier);
    //     let (polynomial_proof, folding_proof, function_proof) = prover.query();
    //     assert!(verifier.verify(&polynomial_proof, &folding_proof, &function_proof));
    //     folding_proof.iter().map(|x| x.proof_size()).sum::<usize>()
    //         + polynomial_proof
    //             .iter()
    //             .map(|x| x.proof_size())
    //             .sum::<usize>()
    //         + function_proof.iter().map(|x| x.proof_size()).sum::<usize>()
    //         + variable_num * MERKLE_ROOT_SIZE * 2
    // }

    fn nearest_power_of_two(num: usize) -> usize {
        if num.is_power_of_two(){
            return num;
        }
    
        let mut power_of_two = 1;
        while power_of_two < num {
            power_of_two <<= 1;
        }
    
        let lower_power_of_two = power_of_two >> 1;
        if num - lower_power_of_two < power_of_two - num {
            return  lower_power_of_two;
        }
        else{
            return power_of_two;
        }
    }

    #[test]
    fn test_proof_size() {
        for i in 5..25 {
            let j = nearest_power_of_two(i);
            println!(
                "(1<< i )/ j is {}, j is {}",
                (((i as f64) - ((j/4) as f64).log2()) as usize), j/4
            );
            let proof_size = output_proof_size::<Mersenne61Ext>((((i as f64) - ((j/4) as f64).log2()) as usize) + 1, j/4 + 1);
            // let proof_size = output_proof_size(i ,1);
            println!(
                "namefri pcs proof size of {} variables is {} bytes",
                i, proof_size
            );
        }
    }
}
