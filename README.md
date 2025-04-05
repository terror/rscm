## rscm

**rscm** is an experimental scheme compiler written in Rust.

## Installation

Build the compiler from source:

```bash
git clone https://github.com/terror/rscm.git
cd rscm
cargo install --path .
```

**n.b.** You must have the [LLVM](https://llvm.org/) @ 18 installed on your machine.

## Usage

You can compile and run scheme programs by passing in a file:

```bash
rscm examples/factorial.scm
```

This command compiles and runs the factorial example under the
[`/examples`](https://github.com/terror/rscm/tree/master/examples) directory,
which looks like:

```scheme
(define (factorial n)
  (if (= n 0)
    1
    (* n (factorial (- n 1)))))

(display (factorial 5))
```

Which writes to standard output:

```bash
120
```

Check out the [integration test suite](https://github.com/terror/rscm/blob/master/tests/integration.rs)
for more example programs.

## Prior Art

The [scheme](https://en.wikipedia.org/wiki/Scheme_(programming_language)) programming language.
