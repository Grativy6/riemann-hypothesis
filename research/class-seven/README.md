# Two periods, one zero-free box

Chris Pang and Hearthline · 28 November 2026

Take the character conductor $17^2=289$. The geometric argument looks for a prime $d$ that reads $157079$ modulo $314160$. Multiplication by $d$ on the geometric level can then have either period **2** or period **34**. We can prescribe either period, put the prime beyond any given cutoff, and require the analytic zero-free box and the geometric remainder bound **for that same prime**. Two separate existence theorems could have supplied two different primes. Choosing the residue before choosing the prime is what joins the two requirements. [Joint statement and proof](GeometricSpectrum.lean).

## A calculation you can do by hand

Here the geometric level is $N=1680\cdot289=485520$. The search modulus is $Q=314160$. Their least common multiple is $L=5340720$. Inside the single search class are the following two classes modulo $L$.

| Representative modulo $L$ | Its value plus one | Divisibility by 17 | Period modulo $N$ |
| --- | --- | --- | --- |
| $157079$ | $157080=17\cdot9240$ | Exactly one factor of 17 | 34 |
| $2670359$ | $2670360=17^2\cdot9240$ | Two factors of 17 | 2 |

The two representatives differ by $8Q$, so the search sees one class. Both square to 1 modulo 1680, and both are $-1$ modulo 17. At 289 the second still reads $-1$. For the first, write $d=-1+17u$ with $17\nmid u$. Then $d^2=1-34u\bmod 289$. After $m$ double steps the reading is $1-34mu\bmod 289$. Seventeen double steps give the first return. The table specifies **where to search**. The representatives themselves do not need to be prime. [Arithmetic of the periods](OrbitSpectrum.lean).

At $N_k=1680\cdot17^{k+1}$ the exact list is $2,2\cdot17,\ldots,2\cdot17^k$. To obtain period $2\cdot17^j$ for $0\le j\le k$, ask for
$$
d\equiv157080\cdot17^{k-j}-1\pmod{314160\cdot17^k}.
$$
The prime 17 divides $d+1$ and cannot divide $d-1$. For any positive $m$, the odd-prime lifting formula gives $v_{17}(d^{2m}-1)=v_{17}(d+1)+v_{17}(m)$. Odd powers cannot return modulo 17. This proves the period formula, and the displayed classes realize every entry. At each entry we can additionally prescribe any positive character level $M$. Every character at every positive divisor of $\operatorname{lcm}(N_k,M)$ receives the same zero-free guarantee, while the prime still supplies the full geometric estimate at $N_k$. [Exact joint spectrum](GeometricSpectrum.lean).

## What the maintained selector actually supplies

The original analytic theorem chooses a prime from a unit residue class that forces $d\equiv7\bmod8$ and coprimality to its working level. For a chosen $\beta>1/2$ and finite $H\ge0$, every quadratic twist of a character of that level has its regularized $L$-function nonzero throughout $\Re s\ge\beta$, $|\Im s|\le H$. The fork uses the maintained zero-density and class-seven selection proofs verbatim. [Original selector at the pinned revision](https://github.com/leanprover-community/riemann-hypothesis/blob/38dc5337b9244e83d252781133df8c4871f7d0f4/src/Lib/Analytic/QuadraticTwist.lean).

Suppose the character lives at $N$ and the prime must fall in $a\bmod Q$. When $8\mid Q$ and $a\equiv7\bmod8$, lift the unit class $a$ to a unit at $L=\operatorname{lcm}(N,Q)$. Apply the original selector there. Reducing the selected prime modulo $Q$ gives the desired class. Raising a character to $L$ and twisting by this very prime gives the same character as twisting first and then raising the level. The raised entire function equals the original entire function times a finite Euler product. A nonzero product has a nonzero first factor. This is sufficient for descent. [Level change and selector](../../src/New/Reduction/Zeros/RefinedSelection.lean) · [What happens in the reverse direction](what-the-pole-remembers.md).

More generally, arbitrarily large eligible primes exist in $a\bmod Q$ exactly when
$$
\gcd(a,Q)=1,\qquad a\equiv7\pmod{\gcd(Q,8)}.
$$
The Chinese remainder theorem first combines the two readings. To force a prime beyond $B$, take a unit representative $c$ at a common even multiple $L$ and choose $z=c+tL>B$. Enlarge the modulus by a power of two until $z$ is its least nonnegative representative. The only prime introduced by that enlargement already divides $L$, so $z$ is still a unit. Any prime selected there is at least $z$. Conversely a prime above $Q$ is coprime to $Q$, and its two residues agree modulo the gcd. As a boundary case, $1\bmod4$ cannot contain a prime that is $7\bmod8$. [Cofinality in both directions](CofinalSeven.lean).

## Where the final proof uses it

The final geometric caller at conductor $f$ uses $N=\operatorname{lcm}(1680,f)$ and asks for $8R-1\bmod16R$, where $R$ is the product of the distinct odd primes dividing $11N$. That class already forces seven modulo eight. Its geometric bound, together with the fixed-prime comparison of zero orders from community PR #9704, applies to the same prime whose twists have been shown to be zero-free. The twisted orders in the box sum to zero. The comparison gives zero for the sum of the original nonnegative orders at the candidate point, hence for the character being tested. This version reaches the repository's existing `Main` target with the original class-seven analytic library. [Geometric caller](../../src/New/Reduction/OneSidedBound.lean) · [Fixed-prime application](../../src/New/Reduction/Zeros/SevenWitness.lean) · [Community comparison, PR #9704](https://github.com/leanprover-community/riemann-hypothesis/pull/9704).

The earlier geometric implementation used the broader all-odd-class selector. The construction above removes that dependency for this caller. A search in $1\bmod4$ illustrates what the broader theorem adds. The geometric parameter changes are inherited from *Where eleven goes*. The fixed-prime comparison is taken from the tested #9704 integration at commit `295cbe93a7d889ed68a565f6a464bb329e144f5c`. The new work here is the choice at a common level, its use in the caller, and the accompanying proofs about the primes it can select. Chris Pang's PAL question guided the construction. Which readings belong to the same object when it crosses levels? [Previous implementation and provenance](https://github.com/Grativy6/hearthline/blob/450950190b051fbe3401065382c4f3be9ee30bfd/shelves/mathematics/prime-sampling/where-eleven-goes.md) · [All-class proposal, PR #9873](https://github.com/leanprover-community/riemann-hypothesis/pull/9873).

## Which points survive finite readings?

Imagine being allowed to ask for the remainder modulo any positive integer. A profinite integer gives a whole set of answers that agree under reduction. Fix a character level and a box as above. The closure of the eligible class-seven primes consists of their own points and **all profinite units that read seven modulo eight**. If a point of the closure reads zero modulo an ordinary prime $p$, the only prime that could answer that way is $p$ itself. A unit has a different property. Every finite set of its readings can be matched by arbitrarily large eligible primes. If a nonunit gives a noninvertible reading modulo $m$, the matching primes must divide $m$. Those are finitely many, and taking further readings distinguishes them. [Exact closure and the zero-coordinate test](FiniteReadings.lean).

One can also choose a single strictly increasing **sequence** of primes converging to any such unit. At step $n$ use character level $(n+1)!$, threshold $1/2+1/(n+1)$ and height $n+1$. For each fixed modulus and each fixed box to the right of one half, every sufficiently late prime then works. The prime changes along the sequence. Picking the level equal to a proposed fixed prime explains why no single prime can satisfy every coprimality requirement. The proof gives existence beyond each prescribed cutoff and makes no prediction for the size of the first match. [Diagonal sequence](FiniteReadings.lean).

## Replay

At this fork revision, fetch the pinned dependencies and build `Main` from the repository root. Run `bash research/class-seven/replay.sh` from a checkout with the matching Lean toolchain. This elaborates all five companion files, including their exact examples and incompatibility controls. [Replay script](replay.sh).
