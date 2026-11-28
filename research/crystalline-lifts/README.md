# Which solutions lift?

Christopher Daniel Pang and Hearthline · 28 November 2026

Start with the integral line and paint a mark only at multiples of **17**. A homogeneous linear equation holding at every painted mark looks like $cx=0$. Put $x=17$ into it. Over the integers, $17c=0$ forces $c=0$. So the painted line and the whole line have exactly the same homogeneous equations.

Now read them modulo 17. The painted line gives **only 0**. Its equations allow **all seventeen residues**. Even 1 passes. No point on the painted line can supply that reading. The same example works over the 17-adic integers, the kind of coefficient ring used in the proof. [Formal 17-adic example](SaturationTest.lean).

This raised a concrete question about the community RH proof. In its Tate-duality argument, $A$ is the space of reductions of integral crystalline cocycles at one fixed lattice. $B$ is the space of residue patterns satisfying every integral matrix equation on those cocycles. The maintained proof uses $A\subseteq B$. For this lattice **$A=B$**. Every pattern in $B$ has an integral crystalline lift. [Original comparison](https://github.com/leanprover-community/riemann-hypothesis/blob/38dc5337b9244e83d252781133df8c4871f7d0f4/src/New/Congruences/LocalLoss/TateDualBound.lean#L262) · [Revised crystalline comparison and caller](../../src/New/Congruences/LocalLoss/TateDualBound.lean).

## Where the lift comes from

Let $O$ be a discrete valuation ring and $Z\subseteq O^{\Gamma\times n}$ a finitely generated module of integral readings. There are finitely many coordinate labels $n$. The set of positions $\Gamma$ may be infinite. Fix $a\ne0$ in $O$. The symbol $\operatorname{red}_a$ means reduction of each coordinate modulo $a$. Let $B_a(Z)$ be all functions with values in $(O/a)^n$ satisfying the finite matrix relations that hold on $Z$. A matrix relation is a finite sum $\sum_g M_g z(g)=0$, so reducing any integral member of $Z$ always gives a solution.

**Saturation at $a$** means that if $a w$ belongs to $Z$ and $w$ has integral coordinates, then $w$ belongs to $Z$ too. Here is the reverse implication on paper.

1. If $z\in Z$ reduces to zero, divide each coordinate by $a$. This produces an integral function $w$ with $z=a w$. Saturation puts $w$ back in $Z$. Thus the kernel of reduction on $Z$ is precisely $aZ$.
2. A finite torsion-free module over a discrete valuation ring is free. If $Z$ has rank $r$, its image modulo $a$ has the length of $Z/aZ$, namely $r\,\ell_O(O/a)$. In a 17-adic example, a cyclic group of size $17^t$ has length $t$.
3. The existing matrix-relation estimate bounds the length of **every** permitted reading together by the very same number. The actual image lies inside that space and already has its full finite length. A proper inclusion would add a nonzero quotient of positive length. Therefore the image fills the space. [Lattice calculation](../../src/Lib/General/Algebra/FittingIdealsAndLengths.lean).

The crystalline lattice supplies both hypotheses. Potential crystallinity gives finite generation in this caller. Its defining period equation lets one divide by every nonzero scalar from $\mathbb Z_\ell$. For a nonzero $a$ in the finite extension's coefficient ring $O$, choose $0\ne t\in\mathbb Z_\ell$ with $t=ab$ in $O$. From $a w\in Z$ we get $t w=b(a w)\in Z$, and division by $t$ gives $w\in Z$. This works at every nonzero principal modulus, including powers of a ramified uniformizer. The final caller uses $a=\ell^m$. [Period equation and division](https://github.com/leanprover-community/riemann-hypothesis/blob/38dc5337b9244e83d252781133df8c4871f7d0f4/src/Lib/PadicHodge/BlochKato.lean#L138) · [Scalar in the base ring](https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/RingTheory/Algebraic/Basic.lean#L571).

## What survives when the original lattice is smaller

Write $S=\{w\in O^{\Gamma\times n} \mid t w\in Z\text{ for some }t\ne0\}$. This is the **saturation** of $Z$. Any integral linear equation vanishing on $Z$ also vanishes on $S$ because the scalar $t$ can be cancelled in $O$. There are enough finite coordinates to detect any element of $S$. The coordinate evaluations on $Z$ span a finitely generated submodule of its dual. Choose finitely many spanning evaluations. If they all vanish on $w\in S$, multiply $w$ into $Z$ and apply those evaluations. Every coordinate of $t w$ vanishes, hence $w=0$. Thus $S$ embeds into a finite free module, is finitely generated, and has the same rank as $Z$ since $S/Z$ is torsion. [Finite-coordinate argument](IntegralEnvelope.lean).

Applying the preceding calculation to $S$ gives
$$
 B_a(Z)=\operatorname{red}_a S,\qquad
 B_a(Z)/\operatorname{red}_a Z \;\cong\; (S/Z)/a(S/Z).
$$
For the second identity, map $S$ to readings modulo the actual lifts from $Z$. Its kernel inside $S$ is $Z+aS$. Taking the quotient by $Z$ first gives the right-hand side. The formal equivalence realizes the left-hand quotient as its canonical image in the ambient quotient. [Equivalence of the actual modules](LossOfLifts.lean).

This gives **one test for saturation**. Choose any nonzero nonunit $a$. Every allowed reading lifts to $Z$ if and only if $Z=S$. Indeed, if every reading lifts, the displayed quotient vanishes. The finite module $D=S/Z$ then satisfies $D=aD$. Nakayama's lemma gives $D=0$. This test compares the **whole solution set** with the **whole reduction image**. One observed reading can belong to both for any lattice. A unit modulus gives the zero quotient for every lattice. [Proof and controls](SaturationTest.lean) · [Nakayama's lemma, part 2](https://stacks.math.columbia.edu/tag/00DV).

## Measuring the size of a missed lift

The saturation defect is finitely generated and torsion. It has a decomposition into cyclic modules with positive exponents. [Existence of the whole profile](FiniteProfile.lean).

Write its positive elementary-divisor exponents as $e_1,\ldots,e_r$, and let $\pi$ be a uniformizer. At precision $\pi^k$ the quotient of allowed readings by actual lifts has length
$$
L(k)=\sum_i\min(k,e_i),\qquad L(k+1)-L(k)=\#\{i:e_i>k\}.
$$
Each coordinate contributes one per layer until it is exhausted. The complete sequence recovers the positive exponents up to reordering. Appending a zero exponent adds a zero module, invisible at every precision. [Derivation](DepthProfile.lean) · [Pinned elementary-divisor calculation](https://github.com/TauCetiProject/TauCeti/blob/2a9233e5be32675476ae438bef6f6dd4ba93eb64/TauCeti/Algebra/Module/DiscreteValuationRing/ElementaryDivisors.lean).

For $Z=17O\oplus17^3 O$ inside $O^2$, where $O=\mathbb Z_{17}$, the saturation is all of $O^2$ and the exponents are 1 and 3.

| Precision $17^k$ | 1 | 17 | 289 | 4913 | 83521 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Missing length $L(k)$ | 0 | 2 | 3 | 4 | 4 |
| Added length at this step | — | 2 | 1 | 1 | 0 |

At modulus 17 every vector in $Z$ reduces to $(0,0)$, while the equations allow $17^2$ readings. At modulus 289 the first coordinate has 17 possible liftable residues and the second has one. The index is $289^2/17=17^3$, as the table predicts. [Count the distinct residues directly](check-board.py).

## Why finite generation matters

Take all sequences over $O$ which are eventually zero. This lattice is saturated: multiplying by a nonzero scalar cannot erase a nonzero tail. The infinite row of ones modulo a proper ideal agrees with an integral lift on **every finite prefix**. It also passes **every** finite matrix relation, since each relation only sees a finite set of positions and a long enough finite row of ones matches all of them. A single eventually-zero row cannot lift it. This counterexample identifies the exact hypothesis that the crystalline argument earns. [Infinite rows, every prefix and the missing lift](InfiniteReadings.lean).

## The two places where this matters

The Tate-duality proof now restricts a cocycle to the chosen local group, identifies its local equation space with integral crystalline reductions, and applies the existing duality estimate. The comparison between those two local spaces costs zero. The duality estimate itself still carries a bound. [Actual caller](../../src/New/Congruences/LocalLoss/TateDualBound.lean).

The general Selmer datum has a different comparison. Its local equation space has length exactly $\mathrm{rank}(Z_w)\,\ell(O/a)$ for every nonzero $a$, even when $Z_w$ is unsaturated. The module that the proof counts is the image of **global** cocycles on restriction. It is a submodule of that local space. Its length plus its colength there is exactly the stated bound. The proof supplies no global lift from an arbitrary allowed local reading. [Exact balance for the maintained Selmer datum](LocalCount.lean).

Christopher Daniel Pang's PAL question guided this work. What earns the passage from an equation on a reading back to a witness in the original frame? The mathematical inputs are the community's definitions and crystalline results, together with module length, saturation, elementary divisors and Nakayama's lemma. The two-file community contribution is [PR #9913](https://github.com/leanprover-community/riemann-hypothesis/pull/9913). Its assertion concerns one fixed local lattice. The community's separate group-ring redesign also involves base change of cohomology. [Community design issue](https://github.com/leanprover-community/riemann-hypothesis/issues/6793).

## Replay

From this revision, run `lake exe cache get` and `lake build`. Run `bash research/crystalline-lifts/replay.sh` from the repository root for the companion results and boundary examples. [Replay script](replay.sh).
