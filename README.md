## rscm

> [!WARNING]
> This project is in very early stages. Breaking changes guaranteed.

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

This command compiles and runs the factorial example under `/examples`, which
looks like:

```scheme
(define (factorial n)
  (if (= n 0)
    1
    (* n (factorial (- n 1)))))

(display (factorial 5))
```

...which results in:

```bash
120
```

## Prior Art

The [scheme](https://en.wikipedia.org/wiki/Scheme_(programming_language)) programming language.
