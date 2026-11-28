# Where eleven goes

Christopher Daniel Pang and Hearthline · 28 November 2026

The geometric construction in the readable RH proof carries a modulus divisible by $18{,}480=16\cdot3\cdot5\cdot7\cdot11$. Look at two primes on the same row of a smaller modulus. Both $839$ and $7{,}559$ are $839\bmod1680$. At 11 their quadratic characters give opposite readings. The smaller prime gives $-1$, the larger $+1$. The argument needs the second reading to rule out a nonsplitting prime below 13.

A geometric level of **1,680** and a prime search modulo **18,480** supply the actual one-sided estimate in the conductor-one case. At the same tower scale the factor $\varphi(q_0)$ counting cyclotomic directions falls from 3,840 to 384. Eleven remains in the search. The complete follow-up uses the separate search and character moduli from the community contribution. [Broader analytic criterion #9873](https://github.com/leanprover-community/riemann-hypothesis/pull/9873) · [Geometric parameter conditions](../../src/New/Reduction/Data/PrimeConditions.lean) · [Actual final caller](../../src/New/Reduction/OneSidedBound.lean)

## The readings the geometry uses

Write $N$ for the geometric base level, $d$ for the odd auxiliary prime, and $D=d+1$. We retained the following arithmetic inputs.

| What the construction reads | How it is supplied |
| --- | --- |
| Each prime $p$ of $N$ divides the norm $(d+1)/4$ of $(1+\sqrt{-d})/2$ | $4p\mid D$ for each prime $p\mid N$. |
| No power of $d$ equals $-1$ modulo $N$ | A divisor $m\mid N$ has $m\mid 2D$ and $m\nmid D$. |
| Every nonsplitting prime is at least 13 | The norm conditions cover $2,3,5,7$. The remaining reading is $(11/d)=1$. |

In the original construction $N$ itself served as the separating divisor. That forced $d^2=1\bmod N$. To exclude $-1$, it suffices that **one divisor** sees $d$ as an involution and distinguishes both $1$ and $d$ from $-1$. For example, powers of $7\bmod16$ alternate between 7 and 1. They can never equal 15, whatever the powers are doing on the odd factors of the full level. [The separating-divisor argument](../../src/New/Reduction/Data/FieldsAndPlaces.lean)

The binary condition is exact under the retained norm conditions. Write $N=2^e v$ with $v$ odd. A separating divisor exists exactly when $e>v_2(D)$. Indeed, if $m\mid2D$ but $m\nmid D$, then $2D/m$ is odd, so $m$ contains the first power of two missing from $D$. In the reverse direction that very power is a witness. If instead $2^e\mid D$, then **the odd exponent $v$ takes $d$ back to $-1$**. For each odd $p^a\mid v$, write $-d=1+pc$ using $p\mid D$. The binomial theorem gives $(1+pc)^{p^j}\equiv1\bmod p^{j+1}$. It follows that $(-d)^v=1\bmod v$, and the same power is one modulo $2^e$. This proves the claimed return modulo $N$. [Both directions and the explicit return exponent](SharpLevels.lean)

## Two minimum moduli

First consider the geometric level. The construction keeps the prime-seven-modulo-eight condition, so $8\mid D$. Avoiding the return to $-1$ therefore forces $16\mid N$. At a tower scale $s$ the cyclotomic order is $q_1=N\,3^a2^s$, with $a>0$. The field contains a primitive 5,040th root, and every field root of unity is a power of the chosen $q_1$th root. Thus $5040\mid q_1$. Since 35 is coprime to the tower multiplier, $35\mid N$. Finally $q_1d\mid (Nd)^{s+6}$ forces $3\mid N$ because $3\mid q_1$ and $d\ne3$. Together these give $16\cdot35\cdot3=1680\mid N$. The lower-bound proof takes the root, conductor and local conditions as inputs. It does not assume $1680\mid N$ in its premises. The level $N=1680$ is attained. [Tower roots and field degrees](../../src/New/Derivatives/Field/PrimeDecomposition.lean) · [Divisibility proof](SharpLevels.lean) · [A geometric datum at the minimum](PrimeClasses.lean)

For a positive $N$ divisible by 1,680, put

$$
R=\prod_{\substack{p\mid11N\\p\ \mathrm{odd\ prime}}}p,\qquad Q=16R .
$$

Each odd prime occurs once. Choose $d\equiv8R-1\bmod Q$. This is a reduced class. Every prime in it has $d+1\equiv8\bmod16$, has the required norm divisors, and has $d\equiv-1\bmod44$, giving $(11/d)=1$.

There is a precise sense in which this search modulus is minimal. For any positive $M$, **there exists a reduced residue class modulo $M$ whose sufficiently large primes all meet these geometric conditions if and only if $Q\mid M$**. Here the requirement applies to every sufficiently large prime of the one chosen class.

* If an odd prime $p\mid N$ is absent from $M$, the Chinese remainder theorem and Dirichlet's theorem supply arbitrarily large primes in the class that are $1\bmod p$. Then $p\nmid d+1$.
* If 11 is absent, the same argument supplies primes that are $3\bmod11$. A successful prime must be $7\bmod8$. Quadratic reciprocity then gives $(11/d)=(-d/11)=-1$ for those primes.
* If $16\nmid M$, its binary part divides eight. Starting with one successful prime shows that the class is $-1$ on that smaller binary part. Its odd part can be kept fixed while forcing $d=-1$ on the entire binary part of $N$. This produces arbitrarily large primes with no separating divisor.
* Conversely, when $Q\mid M$, choose a prime in the canonical class modulo $Q$ larger than $M$. Its residue is a unit modulo $M$, and every prime in that refined class inherits the three readings.

At $N=1680$, the norm and binary tests leave $d\equiv839\bmod1680$. The nonzero squares modulo 11 are $1,3,4,5,9$, so the acceptable residues of $d$ modulo 11 are $2,6,7,8,10$. There are five possible successful classes modulo 18,480. The canonical one is $9{,}239\bmod18{,}480$. The separate example $d=7{,}559$ also works. At $d=839$ the obstruction is the reading at 11. This rejects a geometric parameter choice, without deciding the asymptotic estimate at that prime. [Exact search theorem](SharpLevels.lean) · [Sign calculations](PrimeClasses.lean)

## Seventeen turns up again

For a character with primitive conductor $f$, the complete construction takes $N=\operatorname{lcm}(1680,f)$. At $f=17^2$ the geometric level is **485,520** and the search modulus is **314,160**. Neither divides the other. The repeated 17 belongs to the character. For an explicit example on units modulo 289, set $t(a)=(a^{16}-1)/17\bmod17$. Fermat's theorem makes the quotient integral, and multiplication gives $t(ab)=t(a)+t(b)\bmod17$. The character $\exp(2\pi i\,t(a)/17)$, extended by zero on nonunits, distinguishes 18 from 1, since $18^{16}\equiv273\bmod289$. Reduction modulo 17 identifies the two. Its conductor is therefore 289. The Lean witness also derives the existence of such a character by character separation. [Conductor witness](ConductorWitness.lean)

Keep one prime $d=1{,}099{,}559$. For every $k\ge1$ it satisfies the geometric conditions at $N_k=1680\cdot17^k$. The prime search stays at 314,160 while the orbit of $d$ modulo $N_k$ has exact length $2\cdot17^{k-1}$. To check this by hand, note that $17\mid d+1$ and $17^2\nmid d+1$. Hence $v_{17}(d^2-1)=1$, and $v_{17}((d^2)^m-1)=1+v_{17}(m)$ for $m>0$ by lifting the exponent. Modulo 1,680 the order is two. At $k=2$, the full orbit takes 34 steps to return to 1 and $d^2\bmod485520=228481$. The small divisor 16 still rules out $-1$ at every step.

The same prime gives the actual geometric remainder estimate separately at each $N_k$. Its starting cutoff may depend on the level and on the positive error allowance. The zero-free twist prime in the final analytic argument is separately chosen for the character level and the finite box. [Exact periods, no-return proof and geometric estimates](LongOrbit.lean)

## Public scope and provenance

The one-file contribution to the maintained repository takes $\operatorname{lcm}(18480,f)$ in the existing proof. It directly reuses Tau Ceti's change-of-level equivalences in the positive half-plane. For a principal character presented modulo 289, the old multiplication selected 5,340,720 and this refactor selects 18,480. Its public theorem statements agree with the parent. The larger research branch on top of #9873 takes the additional step down to 1,680 and separates the search modulus. Its final geometric application uses the modulus independence and still chooses $d\equiv7\bmod8$. [One-file PR #9901](https://github.com/leanprover-community/riemann-hypothesis/pull/9901) · [Review of the broader criterion](https://github.com/leanprover-community/riemann-hypothesis/pull/9873#pullrequestreview-6097262874)

Chris Pang's PAL, PECAN and APCI work motivated the distinction between the level carrying a character and the test that selects a prime. The community proof supplies the geometric inequalities and the original tower. Tau Ceti's existing parameter package and the community proposal to reuse it describe the original 18,480 datum. The reduced parameter system changes that interface. The minimum proved here is relative to the retained root-of-unity, conductor-absorption, norm and no-return requirements. [Original geometric parameters](https://github.com/leanprover-community/riemann-hypothesis/blob/38dc5337b9244e83d252781133df8c4871f7d0f4/src/New/Reduction/Data/FieldsAndPlaces.lean#L73) · [Tau Ceti parameter migration #9071](https://github.com/leanprover-community/riemann-hypothesis/pull/9071) · [Pinned zero-transport lemmas](https://github.com/TauCetiProject/TauCeti/blob/2a9233e5be32675476ae438bef6f6dd4ba93eb64/TauCeti/NumberTheory/DirichletCharacter/LFunction/ChangeLevel.lean#L140)

From the root of this research revision run `lake build`, then `lake env lean research/geometric-levels/SharpLevels.lean`, and likewise for `PrimeClasses.lean`, `LongOrbit.lean` and `ConductorWitness.lean`. The clean-room copy on Dust also elaborates the geometric proof up to its estimate with both terminal RH and GRH proof declarations absent.
