use crate::EllipticCurve;
use crate::FiniteField;
use crate::Point;
use num_bigint::BigUint;
use num_bigint::RandBigInt;

pub struct ECDSA {
    elliptic_curve: EllipticCurve,
    a_gen: Point,
    //order of the group
    q_order: BigUint,
}

impl ECDSA {
    // Generates: d, B where B = d*A; A - generator point
    pub fn generate_key_pair(&self) -> (BigUint, Point) {
        let priv_key = self.generate_private_key();
        let pub_key = self.generate_pub_key(&priv_key);

        (priv_key, pub_key)
    }

    pub fn generate_private_key(&self) -> BigUint {
        self.generate_random_number_in_range(&self.q_order)
    }

    // Generates random number in range [1, max)
    fn generate_random_number_in_range(&self, max: &BigUint) -> BigUint {
        let mut rnd = rand::thread_rng();
        let num = rnd.gen_biguint_range(&BigUint::from(1u8), max);
        num
    }

    pub fn generate_pub_key(&self, priv_key: &BigUint) -> Point {
        self.elliptic_curve.scalar_mul(&self.a_gen, priv_key)
    }

    /// R = k*A -> take r = x coordinate of R
    /// s = (hash(m) + d*r) * k^(-1) mod q
    /// Returns signature (r, s)
    ///
    pub fn sign(&self, hash: &BigUint, priv_key: &BigUint, k_rand: &BigUint) -> (BigUint, BigUint) {
        assert!(
            hash < &self.q_order,
            "Hash is bigger than order of the group q"
        );
        assert!(
            priv_key < &self.q_order,
            "Private key is bigger than order of the group q"
        );
        assert!(
            k_rand < &self.q_order,
            "Random number is bigger than order of the group q"
        );

        let r_point = self.elliptic_curve.scalar_mul(&self.a_gen, &k_rand);
        if let Point::Coordinate(r, _) = r_point {
            let s = FiniteField::mult(&r, &priv_key, &self.q_order);
            let s = FiniteField::add(&s, &hash, &self.q_order);
            let k_inv = FiniteField::inv_mult_prime(&k_rand, &self.q_order);
            let s = FiniteField::mult(&s, &k_inv, &self.q_order);

            (r, s)
        } else {
            panic!("r_point is identity");
        }
    }

    /// u1 = s^(-1) * hash(m) mod q
    /// u2 = s^(-1) * r mod q
    /// P = u1 A + u2 B mod q
    /// if r == P.x then signature is valid
    pub fn verify(&self, hash: &BigUint, pub_key: &Point, signature: &(BigUint, BigUint)) -> bool {
        let (r, s) = signature;
        let s_inv = FiniteField::inv_mult_prime(&s, &self.q_order);
        let u1 = FiniteField::mult(&s_inv, &hash, &self.q_order);
        let u2 = FiniteField::mult(&s_inv, &r, &self.q_order);
        let p = self.elliptic_curve.add(
            &self.elliptic_curve.scalar_mul(&self.a_gen, &u1),
            &self.elliptic_curve.scalar_mul(pub_key, &u2),
        );

        if let Point::Coordinate(x, _) = p {
            x == *r
        } else {
            panic!("p is identity");
        }
    }

    pub fn generate_hash_less_than(message: &str, max: &BigUint) -> BigUint {
        let digest = sha256::digest(message);
        let hash_bytes = hex::decode(digest).expect("Decoding failed");
        let hash = BigUint::from_bytes_be(&hash_bytes);
        let hash = hash.modpow(&BigUint::from(1u32), &(max - BigUint::from(1u32)));
        hash + BigUint::from(1u32)
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use crate::{ecdsa::ECDSA, EllipticCurve};

    #[test]
    fn test_sign_verify() {
        let elliptic_curve = crate::EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        let q_order = BigUint::from(19u32);
        let a_gen = crate::Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let ecdsa = super::ECDSA {
            elliptic_curve,
            a_gen,
            q_order,
        };

        let priv_key = BigUint::from(5u32);
        let pub_key = ecdsa.generate_pub_key(&priv_key);

        let message = "Bob -> 1 BTC -> Alice";
        let hash = ECDSA::generate_hash_less_than(message, &ecdsa.q_order);
        let k_rand = BigUint::from(18u32);
        let signature = ecdsa.sign(&hash, &priv_key, &k_rand);

        assert!(ecdsa.verify(&hash, &pub_key, &signature));

        println!("Signature: {:?}", signature);
    }

    #[test]
    fn test_sign_verify_fail() {
        let elliptic_curve = crate::EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        let q_order = BigUint::from(19u32);
        let a_gen = crate::Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let ecdsa = super::ECDSA {
            elliptic_curve,
            a_gen,
            q_order,
        };

        let priv_key = BigUint::from(5u32);
        let pub_key = ecdsa.generate_pub_key(&priv_key);

        let wrong_priv_key = BigUint::from(6u32);
        let wrong_pub_key = ecdsa.generate_pub_key(&wrong_priv_key);

        let message = "Bob -> 1 BTC -> Alice";
        let wrong_message = "Bob -> 0.9 BTC -> Alice";
        let hash = ECDSA::generate_hash_less_than(message, &ecdsa.q_order);
        let wrong_hash = ECDSA::generate_hash_less_than(wrong_message, &ecdsa.q_order);
        let k_rand = BigUint::from(18u32);
        let signature = ecdsa.sign(&hash, &priv_key, &k_rand);

        assert!(!ecdsa.verify(&wrong_hash, &pub_key, &signature));
        assert!(!ecdsa.verify(&hash, &wrong_pub_key, &signature));

        println!("Signature: {:?}", signature);
    }

    #[test]
    fn test_secp256_sign_verify() {
        let p = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .expect("could not convert p");

        let q_order = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .expect("could not convert n");

        let gx = BigUint::parse_bytes(
            b"79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("could not convert gx");

        let gy = BigUint::parse_bytes(
            b"483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .expect("could not convert gy");

        let elliptic_curve = EllipticCurve {
            a: BigUint::from(0u32),
            b: BigUint::from(7u32),
            p,
        };

        let a_gen = crate::Point::Coordinate(gx, gy);
        let ecdsa = super::ECDSA {
            elliptic_curve,
            a_gen,
            q_order,
        };

        let priv_key = BigUint::parse_bytes(
            b"483BBB7726A3C4655DA4FBFC0E1108A8FD17B448A61111199C47D08FFB10D412",
            16,
        )
        .expect("could not convert priv_key");
        let pub_key = ecdsa.generate_pub_key(&priv_key);

        let message = "Bob -> 1 BTC -> Alice";
        let hash = ECDSA::generate_hash_less_than(message, &ecdsa.q_order);
        let k_rand = BigUint::parse_bytes(
            b"1122337EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("could not convert k_rand");
        let signature = ecdsa.sign(&hash, &priv_key, &k_rand);

        assert!(ecdsa.verify(&hash, &pub_key, &signature));

        println!("Signature: {:?}", signature);
    }

    #[test]
    fn test_secp256_sign_verify_tempered_message() {
        let p = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .expect("could not convert p");

        let q_order = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .expect("could not convert n");

        let gx = BigUint::parse_bytes(
            b"79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("could not convert gx");

        let gy = BigUint::parse_bytes(
            b"483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .expect("could not convert gy");

        let elliptic_curve = EllipticCurve {
            a: BigUint::from(0u32),
            b: BigUint::from(7u32),
            p,
        };

        let a_gen = crate::Point::Coordinate(gx, gy);
        let ecdsa = super::ECDSA {
            elliptic_curve,
            a_gen,
            q_order,
        };

        let priv_key = BigUint::parse_bytes(
            b"483BBB7726A3C4655DA4FBFC0E1108A8FD17B448A61111199C47D08FFB10D412",
            16,
        )
        .expect("could not convert priv_key");
        let pub_key = ecdsa.generate_pub_key(&priv_key);

        let message = "Bob -> 1 BTC -> Alice";
        let hash = ECDSA::generate_hash_less_than(message, &ecdsa.q_order);
        let k_rand = BigUint::parse_bytes(
            b"1122337EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("could not convert k_rand");
        let signature = ecdsa.sign(&hash, &priv_key, &k_rand);

        let message = "Bob -> 2 BTC -> Alice";
        let hash = ECDSA::generate_hash_less_than(message, &ecdsa.q_order);
        assert!(!ecdsa.verify(&hash, &pub_key, &signature));

        println!("Signature: {:?}", signature);
    }

    #[test]
    fn test_secp256_sign_verify_tempered_signature() {
        let p = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .expect("could not convert p");

        let q_order = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .expect("could not convert n");

        let gx = BigUint::parse_bytes(
            b"79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("could not convert gx");

        let gy = BigUint::parse_bytes(
            b"483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .expect("could not convert gy");

        let elliptic_curve = EllipticCurve {
            a: BigUint::from(0u32),
            b: BigUint::from(7u32),
            p,
        };

        let a_gen = crate::Point::Coordinate(gx, gy);
        let ecdsa = super::ECDSA {
            elliptic_curve,
            a_gen,
            q_order,
        };

        let priv_key = BigUint::parse_bytes(
            b"483BBB7726A3C4655DA4FBFC0E1108A8FD17B448A61111199C47D08FFB10D412",
            16,
        )
        .expect("could not convert priv_key");
        let pub_key = ecdsa.generate_pub_key(&priv_key);

        let message = "Bob -> 1 BTC -> Alice";
        let hash = ECDSA::generate_hash_less_than(message, &ecdsa.q_order);
        let k_rand = BigUint::parse_bytes(
            b"1122337EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .expect("could not convert k_rand");
        let signature = ecdsa.sign(&hash, &priv_key, &k_rand);
        let (r, s) = signature;
        let tempered_signature = (
            (r + BigUint::from(1u32)).modpow(&BigUint::from(1u32), &ecdsa.q_order),
            s,
        );
        assert!(!ecdsa.verify(&hash, &pub_key, &tempered_signature));

        println!("Signature: {:?}", tempered_signature);
    }
}
