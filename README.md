# Call-by-name normalizability of λcapenv and intersection types (Isabelle/HOL)

An Isabelle/HOL formalization of the characterization of call-by-name
(weak-head) normalizability of **λcapenv**, the λ-calculus with first-class
environments and capture environments but without the identity environment
`id`, by an intersection type system.  The reduction is full σ (the environment
rules Hit/VarRef, Skip/VarSkip, DApp, DNil, DExt, Assoc) together with head β.

## Main results

| Statement | Isabelle name | Theory |
|---|---|---|
| `Typ M ⟷ CFWHN M` (typable iff it reaches a clash-free weak-head normal form) | `main_characterization` | `Main_Results` |
| `Typ M ⟷ CFWHN M ∧ CFWHSN M` (and then every weak-head reduction terminates) | `main_characterization_full` | `Uniform` |
| clashes are untypable | `clash_not_Typ` | `Main_Results` |
| classification of weak-head normal forms | `WHNF_iff_classes` | `WHNF_Classes` |
| subject expansion, completeness, soundness | `subject_expansion`, `completeness`, `soundness` | `Completeness`, `Soundness` |
| σ terminates and is confluent | `sig_SN`, `sig_confluent` | `Cap_Reduction`, `Sig_Confluence` |
| uniqueness of weak-head normal forms | `WHNF_unique` | `Uniform` |
| capture environments: typing, reduction, locality, non-retention | `cap_typed`, `cap_comp_sigma`, `cap_captured`, `cap_uncaptured`, `cap_locality`, `cap_nonretention` | `Capture` |
| relation to pure λ-terms (head normalization of the readback) | `Pure_Relation`, `Pure_FV_necessary` | `Readback` |
| bridge: the reduction of λcapenv (capI) is σ or full β; weak-head reduction is included in it | `bij_toI`, `red_iff_sig_or_beta`, `wh_sub_red` | `CapI_Bridge` (session `LambdaCapEnvWeakHead_CapI`) |

## Files

- `isabelle/ROOT`, `isabelle/*.thy`: session `LambdaCapEnvWeakHead`, 14 theories
  (about 3,900 lines): `ARS`, `Cap_Syntax`, `Cap_Reduction`, `Sig_Confluence`,
  `WHNF_Classes`, `Typing`, `Completeness`, `Soundness`, `Main_Results`,
  `Uniform`, `Capture`, `Examples`, `Lambda`, `Readback`.
- `bridge/ROOT`, `bridge/CapI_Bridge.thy`: session `LambdaCapEnvWeakHead_CapI`
  (one theory, about 70 lines) relating this calculus to the base calculus
  (capI) of `lambda-capenv-public`.

No theory contains `sorry`, `oops`, `axiomatization` or `ML` code.

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/).  Both sessions are checked
with `quick_and_dirty = false`.

The main session needs only HOL:

    isabelle build -d isabelle LambdaCapEnvWeakHead

The bridge session `LambdaCapEnvWeakHead_CapI` (directory `bridge/`) imports the theory
`Reduction` of the session `LambdaCapEnv` from the repository
[lambda-capenv-public](https://github.com/nisizaki/lambda-capenv-public).
Check out that repository next to this one and pass its `isabelle` directory
with `-d`:

    git clone https://github.com/nisizaki/lambda-capenv-public.git ../lambda-capenv-public
    isabelle build -d isabelle -d bridge -d ../lambda-capenv-public/isabelle LambdaCapEnvWeakHead_CapI

(this also builds the session `LambdaCapEnv`, which takes a few minutes or more
depending on the machine).

## Related repositories

- λcapenv core (terms, reduction, simple types, subject reduction, confluence,
  strong normalization, type inference), needed for the bridge:
  https://github.com/nisizaki/lambda-capenv-public
- Call-by-value termination of λcapenv and intersection types: https://github.com/nisizaki/lambda-capenv-call-by-value-termination-intersection-types-public
- PCF_env interpreter (call-by-value λcapenv with PCF constructs):
  https://github.com/nisizaki/pcf-env-interpreter-public
- The same questions for λenv (with `id`):
  https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types,
  https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types

## Authors

Shin-ya Nishizaki and Shogo Murasaki

## How to cite

Shin-ya Nishizaki and Shogo Murasaki. *Call-by-Name Normalizability of λcapenv and its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

## License

MIT License (see [LICENSE](LICENSE)).
