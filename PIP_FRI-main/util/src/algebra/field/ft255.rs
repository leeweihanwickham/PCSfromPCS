use ff::{Field as Fd, PrimeField};
use ff_derive_num::Num;
use serde::{Deserialize, Serialize};

use super::Field;

#[derive(PrimeField, Num, Deserialize, Serialize)]
#[PrimeFieldModulus = "46242760681095663677370860714659204618859642560429202607213929836750194081793"]
#[PrimeFieldGenerator = "5"]
#[PrimeFieldReprEndianness = "little"]
pub struct Ft255([u64; 4]);

impl std::fmt::Display for Ft255 {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl Field for Ft255 {
    const FIELD_NAME: &'static str = "Ft255";
    const LOG_ORDER: u64 = 41;
    const ROOT_OF_UNITY: Ft255 = Ft255([
        11273735707518656615,
        10803742158212994690,
        9604558309451741198,
        1652257763144146550,
    ]);
    const INVERSE_2: Self = Ft255([
        18256200907639226367,
        1192390052779827407,
        168358299667310230,
        1856475237906044671,
    ]);

    #[inline]
    fn from_int(x: u64) -> Self {
        x.into()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        for i in self.0 {
            if i != 0 {
                return false;
            }
        }
        true
    }

    #[inline]
    fn random_element() -> Self {
        Ft255::random(rand::thread_rng())
    }

    fn inverse(&self) -> Self {
        self.invert().unwrap()
    }

    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let x = self
            .0
            .iter()
            .flat_map(|x| x.to_le_bytes().to_vec())
            .collect();
        x
    }
}

#[cfg(test)]
mod tests {
    use super::super::field_tests::*;
    use super::*;

    #[test]
    fn test() {
        add_and_sub::<Ft255>();
        mult_and_inverse::<Ft255>();
        assigns::<Ft255>();
        pow_and_generator::<Ft255>();
    }
}
