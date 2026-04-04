# Flean Plan

## Paper Roadmap

- `CPP`: position Flean as a verified numerical-kernel framework.
  It is reasonable for the first paper to focus on `Flean` itself.
  Focus on reusable floating-point proof infrastructure plus one strong end-to-end case study.
  Core technical story: `IEEE 754` reconstruction / porting in Lean, plus reusable proof abstractions.
  Current backbone: `TwoSum -> Expansion -> AdaptiveExpansion -> Kahan/Neumaier -> chunked reduction`.
  Primary case study: stable `log-sum-exp` / `softmax` skeleton with chunked reduction safety.
  Working paper title:
  `Flean: A Lean Framework for Verified Numerics, from Rounding Theory to Stable Reductions`

- `CAV`: lift the CPP kernel story to a verified numerical pipeline / system story.
  Focus on compositional safety of mixed-precision reduction trees, blockwise kernels,
  and refinement from abstract numerical proofs to executable kernel models.
  Working paper title:
  `Verified Mixed-Precision Reduction Pipelines: Refinement from Numerical Proofs to Executable Kernels`

- `MLSys`: connect the verified kernels to ML compiler workflows and practical workloads.
  Focus on compiler-integrated verified reduction kernels, performance, robustness,
  and empirical impact in training / inference pipelines.
  Likely venue angle: ML compiler / TVM stack.
  Working paper title:
  `Compiler-Integrated Verified Reductions for Reliable ML Workloads`

## Current CPP Position

- Do not position the first paper as a full verified ML system.
- Position it as `Flean`: a verified numerical-kernel framework with a compelling applied kernel case study.
- It is fine for the paper to center `Flean` plus `IEEE 754` reconstruction / porting work.
- Use Kahan / Neumaier as infrastructure, not as the whole paper.
- Treat `stable log-sum-exp` / `softmax` as the flagship CPP case study, not just an optional application.
- The paper will feel too shallow only if the `IEEE 754` story looks like mechanical translation
  or the case study looks toy-sized.
- To avoid that, emphasize reusable abstractions, Lean-specific proof engineering,
  and one nontrivial end-to-end case study.

## Near-Term Priorities

1. Add one flagship safety case study: `log-sum-exp` / `softmax` safety.
   Prefer over stable reduction because (a) direct ML motivation reviewers understand immediately,
   (b) exercises both overflow avoidance and mixed-precision cast chains,
   (c) no Flocq/VCFloat2 precedent.
2. Strengthen the bridge from abstract proofs to implementation-facing kernels.
   This is the key step for turning the CPP case study into a later CAV refinement story.
3. Package existing summation results into a cleaner theorem/API surface for paper presentation.
   Do this after the kernel story is clearer; the cleanup process will expose remaining theorem gaps.
