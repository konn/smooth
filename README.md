# Smooth Infinitesimal Analysis, or Automatic Differentiation with higher infinitesimals
  ![Haskell CI](https://github.com/konn/smooth/workflows/Haskell%20CI/badge.svg)

## Background
A technique of [automatic differentiation][ad wiki] (AD) is in wide use in the realm of scientific computation and machine learning.
One prominent implementation of AD in Haskell is Edward Kmett's [ad][ad] package.

One method to implement AD is the forward mode, using the notion of dual numbers, $\mathbb{R}[\varepsilon] \cong \mathbb{R}[X]/X^2$.
Theoretically, the ring of dual numbers could be regarded as an example of *$C^\infty$-rings*, or more specifically *Weil algebras*, which are used in the area called *[Smooth Infinitesimal Analysis][SIA]* (*SIA*) and *[Synthetic Differential Geometry][SDG]* (*SDG*).
Weil algebras could be regarded as a real line with additional (higher) infinitesimal structures, in the sense we can regard $\mathcal{R}[\epsilon]$ as real line augmented with nilpotent infinitesimal of order two.
Weil algebras allow much more abundance of such infinitesimals; for example, we can consider nilpotent infinitesimals of order three, or mutually nilpotent infinitesimals, and so on.

In this package, we will explore the possibility to extend ADs with higher infinitesimals exploiting Weil algebra structure.

[ad wiki]: https://en.wikipedia.org/wiki/Automatic_differentiation
[ad]: https://hackage.haskell.org/package/ad
[SIA]: https://en.wikipedia.org/wiki/Smooth_infinitesimal_analysis
[SDG]: https://ncatlab.org/nlab/show/synthetic+differential+geometry