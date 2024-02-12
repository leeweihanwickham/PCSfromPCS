extern crate criterion;
use criterion::*;

use pcs::{prover::Prover, verifier::Verifier};
use util::{
    algebra::{
        coset::Coset,
        field::{ft255::Ft255, mersenne61_ext::Mersenne61Ext, Field},
        polynomial::MultilinearPolynomial,
    },
    random_oracle::RandomOracle,
};

use util::{CODE_RATE, SECURITY_BITS};
fn commit<T: Field>(criterion: &mut Criterion, variable_num: usize, poly_num: usize) {
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

    criterion.bench_function(
        &format!("newly {} commit {}", T::FIELD_NAME, variable_num),
        move |b| {
            b.iter_batched(
                || polynomial.clone(),
                |p| {
                    let prover = Prover::new(variable_num, &interpolate_cosets, p, &oracle);
                    prover.commit_polynomial();
                },
                BatchSize::SmallInput,
            )
        },
    );
}

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
        lower_power_of_two
    }
    else{
        power_of_two
    }
}


fn bench_commit(c: &mut Criterion) {
    for i in (5..=5).step_by(1) {
        let j = nearest_power_of_two(i);
        println!(
            " poly_num is: {}", j
        );
        println!(
            "vara_num is: {}", ((i as f64) - ((j) as f64).log2()) as usize
        );
        commit::<Mersenne61Ext>(c, (((i as f64) - ((j) as f64).log2()) as usize), j);
        // commit::<Ft255>(c, ((i as f64) - ((j/4) as f64).log2()) as usize, j/4);
        // commit::<Mersenne61Ext>(c, i, 1);
        // commit::<Ft255>(c, i, 2);
    }
}

fn para_commit<T: Field>(criterion: &mut Criterion, variable_num: usize, poly_num: usize) {
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

    criterion.bench_function(
        &format!("newly {} para commit {}", T::FIELD_NAME, variable_num),
        move |b| {
            b.iter_batched(
                || polynomial.clone(),
                |p| {
                    let prover =
                        Prover::new_parallel(variable_num, &interpolate_cosets, p, &oracle);
                    prover.commit_polynomial();
                },
                BatchSize::SmallInput,
            )
        },
    );
}

fn bench_para_commit(c: &mut Criterion) {
    for i in (5..=25).step_by(1){
        let j = nearest_power_of_two(i);
        //para_commit::<Mersenne61Ext>(c, i, 1);
        para_commit::<Mersenne61Ext>(c, (((i as f64) - ((j/4) as f64).log2()) as usize) + 1, j/4 + 1);
        // para_commit::<Ft255>(c, ((i as f64) - ((j/4) as f64).log2()) as usize, j/4);
        // para_commit::<Ft255>(c, i, 2);
    }
}

fn open<T: Field>(criterion: &mut Criterion, variable_num: usize, poly_num: usize) {
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
    let prover = Prover::new(variable_num, &interpolate_cosets, polynomial, &oracle);
    let commits = prover.commit_polynomial();
    let verifier = Verifier::new(
        variable_num,
        poly_num,
        &interpolate_cosets,
        commits,
        &oracle,
    );
    let (open_point, combination) = verifier.get_open_point();

    criterion.bench_function(
        &format!("newly {} open {}", T::FIELD_NAME, variable_num),
        move |b| {
            b.iter_batched(
                || (prover.clone(), verifier.clone()),
                |(mut p, mut v)| {
                    p.commit_functions(&open_point, &mut v, &combination);
                    p.prove();
                    p.commit_foldings(&mut v);
                    p.query();
                },
                BatchSize::SmallInput,
            )
        },
    );
}

fn bench_open(c: &mut Criterion) {
    for i in (5..=5).step_by(1) {
        let j = nearest_power_of_two(i);
        // open::<Mersenne61Ext>(c, i, 1);
        open::<Mersenne61Ext>(c, (((i as f64) - ((j/4) as f64).log2()) as usize) + 1, j/4 + 1);
        // open::<Ft255>(c, ((i as f64) - ((j/4) as f64).log2()) as usize, j/4);
        // open::<Ft255>(c, i, 2);
    }
}

fn verify<T: Field>(criterion: &mut Criterion, variable_num: usize, poly_num: usize) {
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

    criterion.bench_function(
        &format!("newly {} verify {}", T::FIELD_NAME, variable_num),
        move |b| {
            b.iter(|| {
                verifier.verify(&polynomial_proof, &folding_proof, &function_proof);
            })
        },
    );
}

fn bench_verify(c: &mut Criterion) {
    for i in (5..=5).step_by(1) {
        let j = nearest_power_of_two(i);
        // verify::<Mersenne61Ext>(c, i, 1);
        // verify::<Mersenne61Ext>(c, ((i as f64) - ((j/4) as f64).log2()) as usize, j/4);
        verify::<Ft255>(c, (((i as f64) - ((j/4) as f64).log2()) as usize) + 1, j/4 + 1);
        // verify::<Ft255>(c, i, 2);
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = bench_commit, bench_para_commit, bench_open, bench_verify
}

criterion_main!(benches);
