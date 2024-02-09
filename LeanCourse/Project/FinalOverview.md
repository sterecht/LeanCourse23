## Formalization
This project contains a mostly complete proof of the Mordell-Weil theorem for
Elliptic Curves over ℚ, i.e. the statement that if E is an elliptic curve over ℚ, then E(ℚ) is finitely generated. While in Lean Elliptic Curves are implemented as smooth equations of the form y^2+a1xy+a2y=x^3+a3x^2+a4x+a6, if the field has characteristic other than 2 or 3, any elliptic curve can be written as y^2=x^3+ax+b. Hence I made this assumption throughout the project.

The proof consists of three parts: In the folder HeightFunctions, the theory of heights on cubic curves is developed. Most of this can be done without assuming that the curve is elliptic, cf. `WeierstrassHeight.lean`. This assumption is only used for one inequality; in `EllipticHeight.lean`. `Helper.lean` is a collection of useful small lemmas, mostly about natural numbers and integers.

The second part is the weak Mordell-Weil theorem, stating that E(K)/mE(K) is finite, for K a number field and m a positive integer. In `GaloisReduction.lean` we show that this property is stable under finite field extensions, and develop properties of the Galois action on elliptic curves. The main proof of the weak Mordell-Weil theorem then is contained in `KummerParing.lean`.

Finally, we prove that any abelian group A such that A/mA is finite and which admits a suitable height function has to be finite. This is done in `Descent.lean`. All three parts are then combined for the main result.

The main reference for the proofs is
  Silverman, Joseph: The Arithmetic of Elliptic Curves, Springer 2009 (2nd edition). Chapter VIII

## Gaps in the proofs
Unfortunately, it was not possible to completely finish the formalization.
Mostly, this is because the proof of weak Mordell-Weil relies on some advanced theorems which have not yet been formalized in Lean, in particular Infinite Galois Theory, Kummer Theory, and Dirichlet's S-unit Theorem.
Also, I wasn't able to finish two of the later proofs (at the end of KummerPairing.lean). This was mostly because there were a lot of identifications, e.g. between elements of subfields, which I couldn't deal with in time. I broke everything down into very small gaps, which is why there are lots of sorrys.