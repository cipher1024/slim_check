# slim_check #

[![Build Status](https://travis-ci.org/cipher1024/slim_check.svg?branch=master)](https://travis-ci.org/cipher1024/slim_check)

Port from the Haskell [QuickCheck](https://hackage.haskell.org/package/QuickCheck) library.

## Getting Started ##

Add to your project with:

```
leanpkg add https://github.com/cipher1024/slim_check
```

In a Lean file, write:

```
import test.slim_check

open slim_check

variables (α : Type) [has_add α] [has_one α]

example : (∀ (xs : list α) (x ∈ xs), x ≠ (10 : α)) :=
by slim_check

```

and you'll see the following error report:

```

===================
Found problems!

α := ℤ
xs := [-8, -13, -6, -9, -18, -22, 11, -14, -13, -6, -4, -7, 10, -10, 9, -5, -15, -16, -19, 17]
x := 10
-------------------
state:
α : Type,
_inst_1 : has_add α,
_inst_2 : has_one α
⊢ ∀ (xs : list α) (x : α), x ∈ xs → x ≠ 10
```

For more examples, see `test/slim_check/examples.lean`.
