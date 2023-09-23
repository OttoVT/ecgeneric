mod ecdsa;

use num_bigint::BigUint;

#[derive(PartialEq, Debug, Clone)]
pub enum Point {
    Coordinate(BigUint, BigUint),
    Identity,
}

pub struct EllipticCurve {
    a: BigUint,
    b: BigUint,
    p: BigUint,
}

impl EllipticCurve {
    pub fn add(&self, c: &Point, d: &Point) -> Point {
        assert!(self.is_on_curve(c), "c is not on the curve");
        assert!(self.is_on_curve(d), "d is not on the curve");
        
        if c == d {
            return self.double(c);
        }

        match (c, d) {
            (Point::Coordinate(x1, y1), Point::Coordinate(x2, y2)) => {
                //let s = (y2 - y1) / (x2 - x1) mod p
                //let x3 = s ^ 2 - x1 - x2 mod p
                //let y3 = s * (x1 - x3) - y1 mod p
                let y1plusy2 = FiniteField::add(y1, y2, &self.p);

                if x1 == x2 && y1plusy2 == BigUint::from(0u32) {
                    return Point::Identity;
                }

                // s = (y2 - y1) / (x2 - x1) mod p
                let numerator = FiniteField::subtract(y2, y1, &self.p);
                let denominator = FiniteField::subtract(x2, x1, &self.p);

                let s = FiniteField::divide(&numerator, &denominator, &self.p);

                let (x3, y3) = self.compute_x3_y3(x1, y1, x2, &s);

                Point::Coordinate(x3, y3)
            }
            (Point::Coordinate(x, y), Point::Identity) => Point::Coordinate(x.clone(), y.clone()),
            (Point::Identity, Point::Coordinate(x, y)) => Point::Coordinate(x.clone(), y.clone()),
            (Point::Identity, Point::Identity) => Point::Identity,
        }
    }

    pub fn double(&self, c: &Point) -> Point {
        assert!(self.is_on_curve(c), "c is not on the curve");

        match c {
            Point::Coordinate(x1, y1) => {
                //let s = (3 * x1^2 + a) / (2 * y1) mod p
                //let x3 = s ^ 2 - 2 * x1 mod p
                //let y3 = s * (x1 - x3) - y1 mod p
                if *y1 == BigUint::from(0u32) {
                    return Point::Identity;
                }

                // s = (3 * x1^2 + a) / (2 * y1) mod p
                let numerator = x1.modpow(&BigUint::from(2u32), &self.p);
                let numerator = FiniteField::mult(&BigUint::from(3u32), &numerator, &self.p);
                let numerator = FiniteField::add(&self.a, &numerator, &self.p);

                let denominator = FiniteField::mult(&BigUint::from(2u32), y1, &self.p);
                let s = FiniteField::divide(&numerator, &denominator, &self.p);

                let (x3, y3) = self.compute_x3_y3(x1, y1, x1, &s);

                Point::Coordinate(x3, y3)
            }
            Point::Identity => Point::Identity,
        }
    }

    pub fn scalar_mul(&self, c: &Point, d: &BigUint) -> Point {
        let mut t = c.clone();
        for i in (0..(d.bits() - 1)).rev() {
            t = self.double(&t);
            if d.bit(i) {
                t = self.add(&t, c);
            }
        }

        t
    }

    pub fn is_on_curve(&self, c: &Point) -> bool {
        // y^2 = x^3 + a * x + b
        match c {
            Point::Coordinate(x, y) => {
                let y2 = y.modpow(&BigUint::from(2u32), &self.p);
                let x3 = x.modpow(&BigUint::from(3u32), &self.p);
                let ax = FiniteField::mult(&self.a, x, &self.p);
                let x3plusax = FiniteField::add(&x3, &ax, &self.p);
                y2 == FiniteField::add(&x3plusax, &self.b, &self.p)
            }
            Point::Identity => true,
        }
    }

    fn compute_x3_y3(
        &self,
        x1: &BigUint,
        y1: &BigUint,
        x2: &BigUint,
        s: &BigUint,
    ) -> (BigUint, BigUint) {
        let s2 = s.modpow(&BigUint::from(2u32), &self.p);
        let x3 = FiniteField::subtract(&s2, x1, &self.p);
        let x3 = FiniteField::subtract(&x3, x2, &self.p);

        let y3 = FiniteField::subtract(x1, &x3, &self.p);
        let y3 = FiniteField::mult(s, &y3, &self.p);
        let y3 = FiniteField::subtract(&y3, y1, &self.p);

        (x3, y3)
    }
}

pub struct FiniteField {}

impl FiniteField {
    pub fn add(c: &BigUint, d: &BigUint, p: &BigUint) -> BigUint {
        let r = c + d;
        r.modpow(&BigUint::from(1u32), p)
    }

    pub fn mult(c: &BigUint, d: &BigUint, p: &BigUint) -> BigUint {
        let r = c * d;
        r.modpow(&BigUint::from(1u32), p)
    }

    pub fn inv_addition(c: &BigUint, p: &BigUint) -> BigUint {
        assert!(
            c < p,
            //format!("c: {} must be less than or equal p: {}", c, p);
        );

        p - c
    }

    pub fn subtract(c: &BigUint, d: &BigUint, p: &BigUint) -> BigUint {
        let d_inv = FiniteField::inv_addition(d, p);

        FiniteField::add(c, &d_inv, p)
    }

    pub fn inv_multiplication(c: &BigUint, p: &BigUint) -> BigUint {
        // TODO: this function uses Fermat's little theoreme
        // only valid for p prime
        //only for p prime
        //c^(-1) mod p = c^(p-2) mod p
        c.modpow(&(p - BigUint::from(2u32)), p)
    }

    pub fn divide(c: &BigUint, d: &BigUint, p: &BigUint) -> BigUint {
        let d_inv = FiniteField::inv_multiplication(d, p);

        FiniteField::mult(c, &d_inv, p)
    }

    ///
    /// Finds the multiplicative inverse of an element in the set if p is a
    /// prime number using Fermat's Little Theorem:
    ///
    /// `a^(-1) mod p = a^(p-2) mod p`
    ///
    /// Such that:
    /// `a * a^(-1) = 1 mod p`
    ///
    pub fn inv_mult_prime(a: &BigUint, p: &BigUint) -> BigUint {
        assert!(
            a < p,
            //format!("c: {} must be less than or equal p: {}", c, p);
        );

        a.modpow(&(p - BigUint::from(2u32)), p)
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;

    use crate::{EllipticCurve, FiniteField, Point};

    #[test]
    fn test_add_1() {
        let c = BigUint::from(4u32);
        let d = BigUint::from(10u32);
        let p = BigUint::from(11u32);

        let r = FiniteField::add(&c, &d, &p);
        assert_eq!(r, BigUint::from(3u32))
    }

    #[test]
    fn test_add_2() {
        let c = BigUint::from(4u32);
        let d = BigUint::from(10u32);
        let p = BigUint::from(31u32);

        let r = FiniteField::add(&c, &d, &p);
        assert_eq!(r, BigUint::from(14u32))
    }

    #[test]
    fn test_mult_1() {
        let c = BigUint::from(4u32);
        let d = BigUint::from(10u32);
        let p = BigUint::from(11u32);

        let r = FiniteField::mult(&c, &d, &p);
        assert_eq!(r, BigUint::from(7u32))
    }

    #[test]
    fn test_mult_2() {
        let c = BigUint::from(4u32);
        let d = BigUint::from(10u32);
        let p = BigUint::from(51u32);

        let r = FiniteField::mult(&c, &d, &p);
        assert_eq!(r, BigUint::from(40u32))
    }

    #[test]
    fn test_inv_addittion_1() {
        let c = BigUint::from(4u32);
        let p = BigUint::from(51u32);

        let r = FiniteField::inv_addition(&c, &p);
        assert_eq!(r, BigUint::from(47u32))
    }

    #[test]
    #[should_panic]
    fn test_inv_addittion_2() {
        let c = BigUint::from(52u32);
        let p = BigUint::from(51u32);

        let r = FiniteField::inv_addition(&c, &p);
        assert_eq!(r, BigUint::from(47u32))
    }

    #[test]
    fn test_inv_addittion_identity() {
        let c = BigUint::from(4u32);
        let p = BigUint::from(51u32);

        let r = FiniteField::inv_addition(&c, &p);
        assert_eq!(FiniteField::add(&c, &r, &p), BigUint::from(0u32))
    }

    #[test]
    fn test_inv_multiplication() {
        let c = BigUint::from(4u32);
        let p = BigUint::from(11u32);

        let c_inv = FiniteField::inv_multiplication(&c, &p);

        assert_eq!(c_inv, BigUint::from(3u32));
        assert_eq!(FiniteField::mult(&c, &c_inv, &p), BigUint::from(1u32));
    }

    #[test]
    fn test_divide() {
        let c = BigUint::from(4u32);
        let d = BigUint::from(4u32);
        let p = BigUint::from(11u32);

        let r = FiniteField::divide(&c, &d, &p);
        assert_eq!(r, BigUint::from(1u32))
    }

    #[test]
    fn tets_ec_point_addition() {
        //y^2 = x^3 + 2x + 2 mod 17
        let ec = EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        // (5,1) + (6,3) = (10,6)
        let p1 = Point::Coordinate(BigUint::from(6u32), BigUint::from(3u32));
        let p2 = Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let pr = ec.add(&p1, &p2);

        let is_on_curve = ec.is_on_curve(&pr);
        assert!(is_on_curve);
        assert_eq!(
            pr,
            Point::Coordinate(BigUint::from(10u32), BigUint::from(6u32))
        );
    }

    #[test]
    fn tets_ec_point_addition_identity() {
        //y^2 = x^3 + 2x + 2 mod 17
        let ec = EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        // (5,1) + (6,3) = (10,6)
        let p1 = Point::Coordinate(BigUint::from(6u32), BigUint::from(3u32));
        let p2 = Point::Identity;
        let pr = p1.clone();

        assert_eq!(pr, ec.add(&p1, &p2));
        assert_eq!(pr, ec.add(&p2, &p1));
    }

    #[test]
    fn tets_ec_point_addition_reflection() {
        //y^2 = x^3 + 2x + 2 mod 17
        let ec = EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        // (5,1) + (6,3) = (10,6)
        let p1 = Point::Coordinate(BigUint::from(5u32), BigUint::from(16u32));
        let p2 = Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let pr = ec.add(&p1, &p2);

        let is_on_curve = ec.is_on_curve(&pr);
        assert!(is_on_curve);
        assert_eq!(pr, Point::Identity);
    }

    #[test]
    fn test_point_doubling() {
        // y^2 = x^3 + 2x + 2 mod 17
        let ec = EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        // (5,1) + (5,1) = 2 (5, 1) = (6,3)
        let p1 = Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let pr = Point::Coordinate(BigUint::from(6u32), BigUint::from(3u32));

        let res = ec.double(&p1);
        assert_eq!(res, pr);

        // I + I = 2 * I = I
        let res = ec.double(&Point::Identity);
        assert_eq!(res, Point::Identity);
    }

    #[test]
    fn test_ec_scalar_mul() {
        // y^2 = x^3 + 2x + 2 mod 17 |6| = 19; 19 * A = I
        let ec = EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        let c = Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let pr = Point::Coordinate(BigUint::from(6u32), BigUint::from(3u32));
        let res = ec.scalar_mul(&c, &BigUint::from(2u32));
        assert_eq!(res, pr);

        let pr = Point::Coordinate(BigUint::from(7u32), BigUint::from(11u32));
        let res = ec.scalar_mul(&c, &BigUint::from(10u32));
        assert_eq!(res, pr);

        let pr = Point::Identity;
        let res = ec.scalar_mul(&c, &BigUint::from(19u32));
        assert_eq!(res, pr);
    }

    #[test]
    fn test_ec_scalar_mul_identity() {
        // y^2 = x^3 + 2x + 2 mod 17 |6| = 19; 19 * A = I
        let ec = EllipticCurve {
            a: BigUint::from(2u32),
            b: BigUint::from(2u32),
            p: BigUint::from(17u32),
        };

        let c = Point::Coordinate(BigUint::from(5u32), BigUint::from(1u32));
        let pr = Point::Coordinate(BigUint::from(6u32), BigUint::from(3u32));
        let res = ec.scalar_mul(&c, &BigUint::from(2u32));
        assert_eq!(res, pr);

        let pr = Point::Coordinate(BigUint::from(7u32), BigUint::from(11u32));
        let res = ec.scalar_mul(&c, &BigUint::from(10u32));
        assert_eq!(res, pr);

        let pr = Point::Identity;
        let res = ec.scalar_mul(&c, &BigUint::from(19u32));
        assert_eq!(res, pr);
    }

    #[test]
    fn test_ec_secp256k1() {
        /*
          y^2 = x^3 + 7 mod p (large)

          p = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F
          n = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141
        G = (
            x = 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798,
            y = 483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8
        )
        a = 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000000
        b = 00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000007
        */

        // n * G = I
        let p = BigUint::parse_bytes(
            b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .expect("could not convert p");

        let n = BigUint::parse_bytes(
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

        let ec = EllipticCurve {
            a: BigUint::from(0u32),
            b: BigUint::from(7u32),
            p,
        };

        let g = Point::Coordinate(gx, gy);

        let res = ec.scalar_mul(&g, &n); // n * G
        assert_eq!(res, Point::Identity);

        // p = 1201 * G -> it is also a generator
        let p = ec.scalar_mul(&g, &BigUint::from(1201u32));

        let res = ec.scalar_mul(&p, &n); // n * p
        assert_eq!(res, Point::Identity);
    }
}
