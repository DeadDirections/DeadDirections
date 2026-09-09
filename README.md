# DeadDirections

Machine-checked results of *Dead Directions: Geometric Singular
Learning*, as a standalone Lean 4 package. The appendix "Machine-checked
results" of the paper maps every declaration here to its paper statement
and records what each proof establishes and what it takes as a
hypothesis.

## Building

The toolchain is pinned by `lean-toolchain` (Lean 4) and
`lake-manifest.json` (Mathlib). With [elan](https://github.com/leanprover/elan)
installed:

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the prebuilt Mathlib artifacts; without it
the first build compiles Mathlib from source.

## Layout

One module per paper result cluster, imported by `DeadDirections.lean`:
`GaussianFisher` (Gaussian and mixture anchors), `LnKernel`,
`DdcAdamEquivariance`, `FisherDecay`, `MixtureScore`,
`BridgeComposition`, `DeepLinearBridge`, `SliceRlct`,
`SliceRlctProduct`, `MultiCrossing`, `KlOrder`. No declaration uses
`sorry`.

## Provenance

These sources are the ancillary files of arXiv:2606.05957v2 (tag
`theory-arxiv-v2` of the paper's repository, commit `e777ef557`). The
DualConnections modules of the companion spoke are not included here.
