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

## Papers

* Hiromi ISHII, "*Automatic Differentiation With Higher Infinitesimals, or Computational Smooth Infinitesimal Analysis in Weil Algebra*", Computer Algebra in Scientific Computation 2021, 2021, to appear. ([arxiv:2106.14153](https://arxiv.org/abs/2106.14153))
* Hiromi Ishii, "*[A Succinct Multivariate Lazy Multivariate Tower AD for Weil Algebra Computation](RIMSca2021-rims)*", Computer Algebra – Theory and its Applications, RIMS Kôkyûroku No. 2185 (2021), pp. 104-112. ([arxiv:2103.11615](RIMSca2021-arxiv))

[RIMSca2021-rims]: https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/2185.html
[RIMSca2021-arxiv]: https://arxiv.org/abs/2103.11615

## How to Play with?
First, you need to setup Haskell environment.

There are two options:

* [Using local Haskell environment with REPL or HLS](#using-local-environment)
* [Using isolated Jupyter Notebook environment in Docker](#playing-with-docker)

### Using Local Environment
Although you can use `cabal-install`, we recommend to use [stack](https://haskellstack.com) as it is the tool we use officially to develop this project.

First, compile all the dependencies once:

```sh
$ cd smooth
$ stack build
```

Then, you have two options to play with: REPL and HLS.

#### Playing with REPL
If you want to run the examples in `app/Main.hs`, you can specify the target explicitly by:

```sh
$ stack ghci smooth:exe:smooth-exe
```

If you want to play directly with library, you can invoke:

```sh
$ stack ghci smooth:exe:smooth-exe --no-load
```

Then import and feed whatever you want:

```haskell
>>> import Numeric.Algebra.Smooth
>>> import Numeric.Algebra.Smooth.Weil

-- Setting needed extensions:
>>> :set -Wno-type-defaults -XDataKinds -XPolyKinds -XGADTs -XTypeOperators
>>> :set -XRankNTypes -XFlexibleContexts

>>> diffUpTo 5 (\x -> sin (x/2) * exp (x^2)) (pi/4)
fromList [(0,0.7091438342369428),(1,1.9699328611326816),(2,5.679986037666626),(3,19.85501973096302),(4,73.3133870997595),(5,299.9934189752827)]

>>> sin (pi/3 + di 0) * exp (pi/6 + di 1) :: Weil (DOrder 2 |*| DOrder 3) Double
0.42202294874111723 d(0) d(1)^2 + 0.8440458974822345 d(0) d(1) 
  + 0.7309651891796508 d(1)^2 + 0.8440458974822345 d(0)
  + 1.4619303783593016 d(1)   + 1.4619303783593016

-- Computing with general Weil algebra
>>> :m +Algebra.Ring.Polynomial Algebra.Ring.Ideal 
>>> import qualified Algebra.Prelude.Core as AP
>>> let [x,y] = vars :: [Polynomial AP.Rational 2]
>>> let theIdeal = toIdeal [x^3 - 2 * y^2, y^3, x^2*y]
>>> withWeil (toIdeal [x  ^ 3 - 2 * y^2, y^3, x^2*y]) (sin (pi/3 + di 0) * exp (pi/6 + di 1))
Just (0.5438504802710591*X_0*X_1^2 - 0.7309651891796508*X_0^2 + 0.8440458974822345*X_0*X_1 + 0.44961655668557265*X_1^2 + 0.8440458974822345*X_0 + 1.4619303783593016*X_1 + 1.4619303783593016)
```

#### Playing with Haskell Language Server
If you use LSP-supported editors, you can use haskell-language-server's Eval plugin.
It allows you to evaluate repl lines (comment string starting with `>>>`) embedded in Haskell code.
Due to the GHC's bug, it might fail with GHC >= 8.10.3, 8.10.4; so I recommend you to use GHC 8.10.5.
(If you don't get the meaning of this instruction, we recommend to use REPL.)

### Playing with Docker
We are providing the docker image containing the library and Jupyter Notebooks to play with: [`konn/smooth-jupyter`](https://hub.docker.com/r/konn/smooth-jupyter).
It contains all the dependencies and Jupyter Notebook environment to play with.

#### Notes on scattered notebook outputs
__NOTE__: Due to the current status of IHaskell (the Haskell Engine for Jupyter), the output of IHaskell get scattered with the superfluous warning like the following:

```haskell
<interactive>:1:5: warning: [-Wname-shadowing] This binding for ‘it_var_73669506452478438323’ shadows the existing binding defined at <interactive>:1:5
```

This warning is harmless, but it makes the output cell rather dirty and makes it harder to locate the evaluation results in the output cell.
If you don't like that, we recommend to use your local environment instead of Jupyter.

#### Procedure

You can run the following to download the appropriate docker image and run Jupyter Lab server in the isolated container:

```sh
$ docker run --rm -p 8888:8888 konn/smooth-jupyter:latest
```

Open `https://127.0.0.1:8888` in the browse and open `notebooks/demo.ipynb` to play with.
You can now evaluate cells in a top-down manner, re-edit cells, re-evaluate it, etc.
