# Flean

A Lean 4 formalization of IEEE 754 floating-point arithmetic with mixed-precision analysis, built on Mathlib.

261 theorems, zero `sorry`.

## Getting Started

```
lake build
```

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

## Structure

```
Flean/
├── Core/           Real-valued rounding models, error bounds, double rounding,
│                   cast chain composition, relative error, ULP, Sterbenz
├── Binary/         Bit-level IEEE 754 (BitVec packing, classification, special values)
├── Arith/          Arithmetic operations (add, mul, div, sqrt, FMA, comparisons)
├── Bridge.lean     Refinement connecting bit-level and real-valued models
└── Tactics/        Automation (flean_cast_safe, flean_chain_bound,
                    flean_numeric_bound, flean_quant_bound)
```

## Tactics

```lean
-- Cast chain exactness (widen-narrow, idempotence, absorption)
example {x : ℝ} (hx : isRepresentable binary16 x) :
    roundNNE binary16 (roundNNE binary32 x) = x := by
  flean_cast_safe

-- Error bounds for arbitrary-length chains
example (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainBpowSum fmts x := by
  flean_chain_bound

-- Concrete numeric bounds: f16 relative error ≤ 1/2048 ≈ 4.88e-4
example (x : ℝ) (hx : (2 : ℝ) ^ ((-14 : ℤ) + 11 - 1) ≤ |x|) :
    |x - roundNNE binary16 x| ≤ 1 / 2048 * |x| := by
  exact f16_relative_error x hx
```

## Comparison with Flocq

[Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) provides real-valued rounding models. Flean covers similar abstract theory and adds:

- Bit-level IEEE 754 representation with BitVec
- Bit-real refinement bridge
- Compositional cast chain error analysis
- Mixed-precision automation tactics
- Exception flags, comparisons, totalOrder
- Concrete IEEE 754 format instances (binary16/32/64/128)

## License

Apache-2.0
