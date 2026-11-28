# What the pole remembers

Chris Pang and Hearthline · 28 November 2026

At level 1806, one reading of the regularized principal Dirichlet $L$-function is $12/43$. Four distinct primes went into that reading. Only 43 is printed in the denominator. Here is how to read all four back out. [Exact level-1806 calculation and general proofs](EulerReadings.lean).

| Current fraction | Largest prime in its reduced denominator | Undo that prime's factor | Next fraction |
| --- | --- | --- | --- |
| $12/43$ | 43 | multiply by $43/42$ | $2/7$ |
| $2/7$ | 7 | multiply by $7/6$ | $1/3$ |
| $1/3$ | 3 | multiply by $3/2$ | $1/2$ |
| $1/2$ | 2 | multiply by $2$ | $1$ |

For a positive level $N$ the reading at the regularized pole $s=1$ is the exact rational number
$$
E_{1,N}(1)=\prod_{p\mid N}(p-1)/p=\varphi(N)/N,
$$
with one factor for each distinct prime. If $P$ is the largest prime present, each numerator factor $p-1$ is smaller than $P$. None can cancel $P$. Every denominator prime comes from the support, so $P$ is the largest prime in the reduced denominator. Removing its factor leaves exactly the same problem with one fewer prime. The empty product gives 1. This decoding of the totient ratio appears in Paul Erdős, Florian Luca and Carl Pomerance, *On the proportion of numbers coprime to a given integer*, §2, proof of Lemma 1 and Algorithm A. Their manuscript is dated 2006 and the volume appeared in 2008. [Author manuscript](https://math.dartmouth.edu/`carlp/PDF/gcdnphin14.pdf#page=4) · [Published paper](https://doi.org/10.1090/crmp/046/03).

The exact reading matters. The method acts on a reduced rational and assumes it really arose from a level. For instance $1/5$ would force 5 and then leave $1/4$. A reduced denominator of a genuine reading divides a product of distinct primes, so $1/4$ is impossible. The reading records which primes occur. The levels 6 and 12 give the *same entire principal function at every point*. The extra power of 2 is invisible even if we keep the whole function. [Theorems `same_pole_iff` and `same_function_iff`](EulerReadings.lean).

## Why the direction of transport matters

Let $N\mid L$ and let $\chi$ be a Dirichlet character at $N$. In the community project's normalization, write $E_\chi$ for the entire function equal to the usual $L$-function for a nonprincipal character and obtained by removing the pole for a principal one. Inducing $\chi$ to $L$ gives
$$
E_{\chi^{(L)}}(s)=E_\chi(s)\prod_{p\mid L}(1-\chi(p)p^{-s}).
$$
A prime already dividing $N$ contributes 1 to this product. Away from $s=1$ the formula follows by change of level for the ordinary functions. At one it follows by continuity of both entire sides. [All-point identity](EulerReadings.lean).

A vanishing Euler factor satisfies $\chi(p)p^{-s}=1$. Its derivative at that point is $\log p$, so it contributes exactly one to the order of vanishing. The character value at a prime away from its modulus has absolute value one. Taking absolute values forces $\Re s=0$. At every point of the complex plane the new order is the old order plus the number of distinct Euler factors that vanish there. In particular raising the level preserves the exact order on either side of the imaginary axis. [Order formula and the location of every added zero](EulerReadings.lean).

At $s=0$, the level-one principal function has value $(0-1)\zeta(0)=1/2$. Raising to level 2 adds $1-2^{-s}$ and gives a simple zero there. At general principal level $L$ the order at zero counts the distinct prime factors of $L$. For 1806 this order says **four**. The reading at one says **which four**. [Level-one, level-two and level-1806 controls](EulerReadings.lean).

The class-seven selection proof starts with a *nonzero* value at the larger level. A nonzero product ensures its original factor was nonzero, at any complex point. The example at zero shows exactly what can go wrong when the implication is reversed. The arithmetic decoding above has a separate role. It explains how much the principal function remembers about its level and is independent of the proof of the selector. [Back to the same-prime construction](README.md).
