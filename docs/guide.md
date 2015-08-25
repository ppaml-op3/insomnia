% Insomnia User's Guide - Modular Probabilistic Programming
% Aleksey Kliger
% August 2015

# Introduction #

*Insomnia* is a language in the ML-family of languages extended with
 syntax for probabilistic programming.

# Preliminaries #

Insomnia runs on Linux and Mac OS X (and perhaps Windows, though
that's untested).

## Prerequisites and Installation##

To install *Insomnia*, you need a recent version of
[GHC](http://haskell.org/ghc/) (>= 7.8) and
[cabal-install](http://haskell.org/cabal/) (> 1.22) .  The following
instructions set up a cabal sandbox (optional, but highly
recommended), download and install all upstream dependencies, build
the insomnia interpreter and compiler, run tests and (optionally)
install the binaries.

```bash
cabal sandbox init   # optional
cabal install --dependencies-only --enable-tests
cabal configure --enable-tests
cabal build
cabal test
cabal install        # optional
```

## Invoking the interpreter ##

To run the `insomnia` interpreter, if not using a sandbox:

```bash
insomnia examples/infer.ism
```

If using a sandbox:

```bash
cabal exec insomnia examples/infer.ism
```

## Invoking the compiler ##

The `insomniac` compiler compiles Insomnia programs to [Gamble](https://github.com/rmculpepper/gamble/)

```bash
insomniac examples/infer.ism
```

or

```bash
cabal exec insomniac examples/infer.ism
```

# Probabilistic modular programming #

Probabilistic programming is an approach to *inference* of the
distribution of the values of some hidden state (called a *latent
variable*) based on the values of some *observable variables* that
serve as evidence in a *generative model* that explains how the latent
variables give rise to the observed ones.

In *Insomnia*, generative models may be developed incrementally by
using a module system to separately describe logically separate pieces
of the latent or observed state of the world.

Some variables that are neither directly observed, nor interesting for
inference may be *marginalized out*.  Marginalization in *Insomnia* is
accomplished via *module sealing* by ascribing to a module a *module
type* that does not mention the uninteresting variable.

# Toplevels #

An *Insomnia* toplevel program is composed of a sequence of

1. Module- and model-type identifier definitions
2. Module and model identifier definitions
3. Imports of modules or module types from external files
4. Queries over models

Definitions and imports bring module type identifiers or module
identifiers into scope in the rest of a file but not in the body of
the definition.  Queries are executed for effect.

Module identifiers and module type identifiers live in different
logical namespaces, so it is possible for `X` to be the name of a
module and also the name of a module type.  But this is confusing and
this practice is discouraged.

## Imports from external files ##

An import has the form

```ocaml
import "directory/file.sim" (module MyModule
                             module type MY_SIG
                             module X using OtherModule)
```

That is, each import starts with the keyword **import** followed by
the name of the file that will provide zero or mode module or module
type identifiers. The list of imported module and module type
identifiers is mandatory; any identifiers not mentioned will not be
visible in the current file.

* The form `module M` imports a module called `M` from the file and
makes it available in subsequence definitions in the current file with
the name `M`.

* Likewise `module type MY_SIG` makes the name `MY_SIG` available in
the rest of the current file.

* Optionally, modules may be imported using a different name in the
external file: `module X using Y` lets the module identifier `X` stand
for the module `Y` in the specified file.

It is legal to import the same file more than once, but the imports
will refer to the same module and any effects (ie queries) will be
executed exactly once.

Import cycles are illegal and *Insomnia* will signal an error when
they are detected.

## Queries ##

A query has the form

```ocaml
query sample ModelIdentifier n
```

Where *n* is the number of samples to generate from the model given by `ModelIdentifier`.

The query form is deliberately impoverished.  Future versions of
insomnia will support a richer set of queries on models.

## Module- and Modele-type Identifier Definitions ##

A module type definition has the form

```ocaml
MY_SIG = ModuleTypeExpression
```

The identifier `MY_SIG` is bound in the rest of the current file to
the module-type expression on the right hand side.  The name `MY_SIG` is
not in scope in the right-hand side.

Whether `MY_SIG` is a model-type or a module-type depends on the
expression on the RHS.

By convention, module type identifiers are written `IN_ALL_CAPS` with
words separated by underscores.  This is merely a convention, the
*Insomnia* compiler merely requires that module type identifier start
with a capital letter.

## Module and Model Identifier Definitions ##

A module definiton has the form

```ocaml
MyModule = ModuleExpression
```

The identifier `MyModule` is bound in the rest of the current file to
the module expression on the right hand side.  The name `MyModule` is
not in scope in the right-hand side.

Whether `MyModule` is a module or a model depends on the expression on the RHS.

By convention, module identifiers are written `InMixedCaps`.  This is
merely a convention, the *Insomnia* compiler merely requires that
module identifiers start with a capital letter.

### Syntactic sugar ###

```ocaml
MyModule : ASCRIBED_SIG = ModuleExpression
```

The syntactic sugar above means the same as

```ocaml
MyModule = (ModuleExpression : ASCRIBED_SIG)
```

See signature ascription in the description of module expressions,
below.

# Model and Module Type Expressions#

A *module type* or *model type* provides the *interface* to a module or a model.

The module type expressions are

1. Module type identifiers
2. Literal module or model signatures
3. Functor signatures
4. Module types with a *where clause*

## Module type identifiers ##

If `MY_SIG` is a previously defined module- or model-type identifier,
it may be used as a module type expression.

## Module and model signatures ##

A literal module type signature has the form

```ocaml
module type {
  decls ...
}
```

A literal model type signature has the form

```ocaml
model type {
  decls ...
}
```

For example the toplevel expression below defines `SIG1` to be the
interface of models containing a single integer value named `x`:

```ocaml
SIG1 = model type {
  sig x : Int
}
```

The possible declarations are described below.

### Declarations ###

The declarations are zero or more submodule, type or value
declarations.  Submodule and type declaration each scope over the
remainded of the current sequence of declarations.

Declarations may either be separated by semicolons, or by *layout*.
With layout, each declaration must begin in the same column as the
first declaration which must be indented to the right of the enclosing
definition.

#### Value signature declarations ####

A value signature declaration declares the type of a value component.

```ocaml
sig ident : Type
```

This declares the value identifier `ident` to have the type `Type` in
the current signature.

In insomnia, value identifiers must begin with a lower-case letter.

#### Type declarations ####

Type declarations specify a type identifier component of the current
signature.  Types identifiers may be declared either as aliases for
existing types, manifest definitions of new types that will be visible
to clients of a module, or abstract types whose implementations are
only available to the implementation of a module but not its clients.

Type identifiers must begin with a capital letter.

##### Type alias declarations #####

A type alias declaration has the form

```ocaml
type TypeIdentifier = Type
```

Or for polymorphic aliases

```ocaml
type TypeIdentifier (tyVar1 : Kind1) ... (tyVarN : KindN) = Type
```

The first form makes `TypeIdentifier` an alias for the type on the
right hand side in the remainder of the current signature and in all
clients of a module.

The second form allows for type variables (that are in scope only in
the RHS of the alias declaration) to appear in the type on the RHS.

For example:

```ocaml
type MyArrow (a : *) (b : *) = a -> b
```

Declares `MyArrow` as an alias such that wherever the type `MyArrow X Y`
appears it is equivalent to `X -> Y`.

Polymorphic type aliases must appear fully-applied when they are used.
Given the example above, `MyArrow` and `MyArrow T` are both illegal,
but `MyArrow T S` is fine.

##### Manifest type definitions #####

Manifest type definitions expose the implementation of a type in a
signature to clients of a module having that signature.

```ocaml
data TypeIdentifier (tyVar1 : Kind1) ... (tyVarN : KindN) =
  Cons1 Type11 ... Type1K
  | Cons2 Type21 ... Type2K2
  ...
  | ConsM TypeM1 ... TypeMKM
```

Each data type declaration may be parametrized by a number of type
variables and specify zero or more value constructors each with zero
or more arguments (that may mention the type variables).

The value constructors each must begin with a capital letter.

Examples

```ocaml
data Bool = True | False
```

A module signature with the above manifest type definition must
provide a type called `Bool` with value constructors `True` and
`False`.

```ocaml
data Either (a : *) (b : *) = Left a | Right b
```

The above definition specifies that the type constructor `Either` (of
kind `* -> * -> *`) is available, as well as the value constructors
`Left` and `Right` with types `forall (a : *) (b : *) . a -> Either a
b` and `forall (a : *) (b : *) . b -> Either a b`, respectively.

Data type constructors may appear partially applied.  `Either` and
`Either Int` are both valid, in addition to `Either Int Bool`.  Value
constructors may aloso be used partially applied.

##### Abstract type declarations #####

The abstract type definitions specify that a module has a named type component
but hide the implementation of the type from clients of a module.

```ocaml
type TypeIdentifier : Kind
```

For example, the declaration below specifies that the signature
includes a type identifier `T` that stands for a type (of kind `*`)
whose implementation is hidden.

```ocaml
type T : *
```

Abstract type declarations may be used to define abstract types that
could be implemented by multiple modules.

```ocaml
EQ = module type {
  type T : *
  sig eq : T -> T -> Bool
}
```

The module type definition above defines `EQ` to be the signature of
modules that have two components: a type `T` and an operation `eq`
that takes two values of type `T` and returns a boolean indicating
whether the two values are equal.  This signature may be ascribed to
many modules that implement equality for various types.

Additionally asbtract types in signatures may be supplemented by
`where` clauses to produce new signatures that carry a manifest type
in place of the abstract one.  (See the section on where clauses).


#### Submodule declarations ####

A submodule declaration provides the model-type or module-type of a
nested module identifier within a signature.

```ocaml
ORD = module type {
  type T : *
  sig compare : T -> T -> Ordering
  Eq : EQ where type T = T
}
```

In the example above, the module signature `ORD` includes a type
component `T`, a value component `compare` and a nested module `Eq`
whose signature is `EQ where T = T` (the `where`-clauses specifies
that the `T` component of the signature EQ must now be refined to be
manifestly equal to the abstract type `T` of the overall `ORD`
signature).

Module identifier components of a signature are in scope in the
remainder of a signature.

If a module identifier refers to a submodule, then type and submodule
components of that type are accessible in the remainder of the
signature.  If a module identifier refers to a submodel, its types and
submodules aren't accessible.

## Functor signatures ##

Functor signatures specify the interface of modules that are
*parametrized* over one or more argument modules.

```ocaml
FUN_SIG = (X : X_SIG, Y : Y_SIG) -> RESULT_SIG
```

This declares that `FUN_SIG` is the interface to a functor that takes
an argument module or model called `X` having the given signature and
a second argument `Y` with its own signature and produces a module
that has the result signature.

Functor arguments are in scope over the rest of the argument list and
the functor result (that is, if `X_SIG` is a module signature, then
the `Y_SIG` and `RESULT_SIG` may both mention `X` - for example to
refer to some of its type components).

Functors in *Insomnia* are higher-order.  Both `RESULT_SIG` and
`X_SIG` and `Y_SIG` may themselves be functor signatures.

Functors in *Insomnia* are generative.  More discussion of this in the
functor module expression section.

## Where clauses ##

Where clauses allow the refinement of signatures to provide manifest
definitions for some abstract type components of a module type
expression.

```ocaml
INT_EQ = EQ where type T = Int
```

The above definition specifies that `INT_EQ` is a module type
identifier that stands for the following module type

```ocaml
module type {
  type T = Int
  sig eq : Int -> Int -> Bool
}
```

Note that: (1) the resulting signature still has a `T` component, but
now it is a manifest type alias for `Int`, (2) the types of all the
fields following the manifest type alias now refer to the RHS of the
`where` clause (namely, `Int`).

Where clauses may be stacked, they associate in the only sensible way:
`SIG where type T1 = S1 where type T2 = S2` means the signature just
like `SIG` except with `S1` and `S2` for `T1` and `T2`, respectively.

# Model and Module Expressions #

The *modules* and *models* provide the implementations of modules or models.

The module expressions are

1. Module identifier paths
2. Literal module or model structures
3. Functors
4. Model-*local* definitions
5. Sealing signature ascriptions
6. Model posterior observations

## Module identifier paths ##

## Module and model structures ##

### Definitions ###

#### Value definitons ####

#### Type definitions ####

#### Submodule definitons ####

## Functors ##

## Local modules ##

## Module sealing ##

## Model observations ##

# Types #

Insomnia's types include

1. Type constructor paths
2. The base types
3. Functions
4. Polymorphic Functions
5. Type variables
6. Records

# Value Expressions #

Insomnia's value expressions include

1. Value constructor paths
2. Literal values
3. Lambda expressions
4. Function application
5. Let-expressions
6. Point distribution
7. Record constructions
8. Case analysis by pattern matching

## Patterns ##



