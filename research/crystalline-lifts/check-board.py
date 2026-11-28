"""Count liftable residues of the diagonal lattice at each precision."""
from itertools import product
from math import prod


def residue_images(prime, depth, exponents):
    modulus = prime ** depth
    return [{(prime ** exponent * x) % modulus for x in range(modulus)}
            for exponent in exponents]


def run():
    for prime in (2, 3, 5, 17):
        for exponents in ((), (0,), (1,), (1, 3)):
            for depth in range(5):
                modulus = prime ** depth
                images = residue_images(prime, depth, exponents)
                all_readings = modulus ** len(exponents)
                image_count = prod(map(len, images))
                exponent_sum = sum(min(depth, e) for e in exponents)
                assert all_readings == image_count * prime ** exponent_sum
                if prime == 2:
                    full_image = {
                        tuple((prime ** e * x) % modulus for e, x in zip(exponents, xs))
                        for xs in product(range(modulus), repeat=len(exponents))
                    }
                    assert len(full_image) == image_count
                if prime == 17 and exponents == (1, 3):
                    print(f"k={depth} modulus={modulus} allowed={all_readings} "
                          f"liftable={image_count} index={all_readings // image_count} "
                          f"length={exponent_sum}")


if __name__ == "__main__":
    run()
