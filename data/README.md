# Finite-certificate input data

These two captured finite examples are inputs to the certificate generators in `scripts/`. The generated Lean files are already included in the release, so Python generation is not required to check the proofs.

The JSON records are computational input, not trusted proof certificates. Lean checks the finite identities, counts, inequalities and subsequent deductions. These examples obstruct particular intermediate strategies; neither is a counterexample to Erdős #539. The generator scripts emit candidate source files and may overwrite generated modules when invoked. Run them in a separate working copy.
