# mil-solutions
Solutions and tinkering with the [Mathematics in Lean4](https://github.com/leanprover-community/mathematics_in_lean) project.

## TODO

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

- Update `lean-toolchain` to latest stable version of Lean4
- Make sure mathlib require statement in `lakefile.lean` is:

```
require "leanprover-community" / "mathlib" @ git "v4.11.0"
```

- `lake update && lake build`