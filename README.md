# mil-solutions
Solutions and tinkering with the [Mathematics in Lean4](https://github.com/leanprover-community/mathematics_in_lean) project.

## TODO

- [ ] finish set theoretic identities in C04 S02
- [ ] add upgrading instructions

## Development

### Setup

Assumptions:
- lake v5+
- elan v3.1+

To setup new repo from scratch, do:
```
git clone my-new-empty-repo
cd my-new-empty-repo

elan toolchain install leanprover/lean4:v4.10.0
echo 'leanprover/lean4:v4.10.0' > lean-toolchain
lake init
echo 'require "leanprover-community" / "mathlib"' >> lakefile.lean
lake update
lake build
```

### Upgrading Lean & Mathlib

TODO: This always bites me in the ass.