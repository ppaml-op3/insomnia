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
will refer to the same module and any effects (i.e. queries) will be
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

## Module- and Model-type Identifier Definitions ##

A module type definition has the form

```ocaml
MY_SIG = ModuleTypeExpression
```

The identifier `MY_SIG` is bound in the rest of the current file to
the module-type expression on the right hand side.  The name `MY_SIG` is
not in scope in the right-hand side.

Whether `MY_SIG` is a model-type or a module-type depends on the
expression on the right-hand side.

By convention, module type identifiers are written `IN_ALL_CAPS` with
words separated by underscores.  This is merely a convention, the
*Insomnia* compiler merely requires that module type identifier start
with a capital letter.

## Module and Model Identifier Definitions ##

A module definition has the form

```ocaml
MyModule = ModuleExpression
```

The identifier `MyModule` is bound in the rest of the current file to
the module expression on the right hand side.  The name `MyModule` is
not in scope in the right-hand side (RHS).

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
remainder of the current sequence of declarations.

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
constructors may also be used partially applied.

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

Additionally abstract types in signatures may be supplemented by
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

If `M` is a module identifier and `F` is a submodule or submodel field
then `M.F` may be used to access the submodule from a scope where `M`
is visible.  Submodule paths may descend into several submodules
`M.F1.F2` selects the `F2` submodules from the `F1` submodule of the
module identified by `M`.

You cannot descend into submodules of models.  If `M` is a module and
its `F` component is a model, `M.F.X` is illegal for all `X`
components of `M.F`.

## Module and model structures ##

A literal module or model has the form `module { defns ... }` or
`model { defns ... }`, respectively.

Each module may contain zero or more definitions that provide the
components of a module.

### Definitions ###

There are three sorts of definitions: value definitions, type
definitions and submodule definitions.

#### Value definitions ####

Value definitions include: value signature specifications, value
definitions, function definitions, sampled value definitions and
tabulated function definitions.

##### Value type signature specifications #####

If `f` is a value field of type `T` a definition of the form

```ocaml
  sig f : T
```

May precede the actual definition of T.

In some situations type signatures are **required**:

1. Recursive functions and mutually recursive definitions:

    ```ocaml
      sig f : A -> B
      sig g : B -> A

      fun f x = ... g y ...
      fun g y = ....f x ...
    ```

    Note that the signatures for both mutually recursive functions were provided
    before their definitions.

2. Polymorphic functions:

    ```ocaml
      sig map :: forall (a : *) (b : *) . (a -> b) -> List a -> List b
      fun map f xs = ...
    ```

##### Value definitions #####

If `x` is a field of type `T` and `e` is an expression of type `T` then

```ocaml
  val x = e
```

Defines the field `x` to have the value that is the result of evaluating `e`.

Value definitions may occur in models and modules.

##### Function definitions #####

If `f` is a field of type `forall (a1 : k1) ... (aM : kM) . T1 -> ... -> TN -> S` then
provided that the expression `e` has type `S` given that each `xi` has type `Ti`, then the function can be defined by:

```ocaml
  fun f x1 ... xN = e
```

Function definitions may not occur in models.

##### Sampled value definitions #####

In models, if `x` is a field of type `T` and `e` is an expression of
type `Dist T`, the definition below defines `x` to be a sample from the
distribution denoted by `e`.

```ocaml
   val x ~ e
```

It is an error to write a sampled value definition in a module.

##### Tabulated function definition #####

In models, a field `f` of type `E1 -> ... Ek -> S` may be defined by
an expression `e` of type `Dist S` under the assumption that variables
`idx1` through `idxk` have the corresponding types `E1` through `Ek`.

```ocaml
  forall (idx1 : E1) ... (idxK : Ek) .
  fun f idx1 .... idxK ~ e
```

Note that each `idxi` variable must appear exactly once to the left of the `~`.

Tabulated function definitions are illegal in modules.

#### Type definitions ####

Type definitions are either type alias definitions or datatype definitions.

##### Type alias definitions #####

If `S` is a type, the field `T` may be declared as

```ocaml
  type T = S
```

In the scope of the rest of the module `T` may be used as an alias for `S`.  Aliases may be at higher kinds.

```ocaml
  type Exc = Either Int
```

Here `Either Int` has kind `* -> *` and so does `Exc`.

If `S` is a type mentioning variables `a1 : K1` through `aN : KN`, the
field `T` may be declared as

```ocaml
  type T (a1 : K1) ... (aN : KN) = S
```

In this case `T` must be used with at least *n* type arguments.

```ocaml
type Exc2 (a : *) = Either Int a
```

In this case `Exc2` is illegal, but `Exc2 Int` is okay.

##### Datatype definitions #####

Datatype definitions look exactly like datatype specifications in module types.

Datatype definitions in different *Insomnia* modules give rise to
different types.  Even if two modules declared the type `Bool` exactly
the same way, those types are completely distinct and unrelated.

Moreover, datatype definitions in *Insomnia* are generative.  Module
expressions such as sealing and functor application give rise to
distinct modules (and therefore any datatypes declared in such modules are distinct).

```ocaml
M1 = module {
  data Bool = True | False
}

M2 = module {
  data Bool = True | False
}

M3 = (M1 : module type { data Bool = True | False })

IdentityFunctor = (X : module type { type Bool : *}) -> { type Bool = X.Bool }

M4 = IdentityFunctor M1
```

Each of `M1`, `M2`, `M3`, `M4` have a distinct `Bool`
type that is not equal to any of the others.


However, the types `M1.Bool` and `Mnested.M1.Bool` are the same

```ocaml
Mnested = module {
  M5 = M1
}
```

#### Submodule definitions ####

Models and modules may contain submodule or submodel components.

For example

```ocaml
Outer = module {
  Inner = module {
    type T = Int
  }

  sig x : Inner.T
  val x = 3
}
```

Type and module components of `Inner` may be referenced by module
identifier paths and type paths in the rest of the outer module.

Submodels may also be defined.  However it is an error to access a
component of a submodel.

#### Submodule sampling ####

In models, submodules may be sampled from models:

```ocaml
model M1 {
  sig x : Bool
  val x ~ flip 0.5
}

model M2 {
  X ~ M1
  sig y : Bool
  val y = not X.x
}
```

Here `M1` is a model containing a field `x`.  `M2` is a model
containing two components: a module `X` that is sampled from `M1` and
a value field `y` equal to the negation of the `x` component of the
sampled submodule.

## Functors ##

Functor are parametrized modules or models.  That is, a functor takes one or more
other modules as arguments and generates a new module.

In Insomnia, functors are generative - each application of a functor
generates a new modules that is distinct from all others, even if
applied to the same types.

Functors allow for a dependency among their arguments and their results.

```ocaml
FDouble = (X : module { type T : * val x : T }) -> {
  type T = { fst : X.T ; snd : X. T }
  val x = {fst = X.x , snd = X.x }
}

M1 = module {
  type T = Int
  val x = 3
}

M2 = FDouble (M1)
```

In the example above, `M2.T` is the type `{fst : Int, snd : Int}` and
`M2.x` is the value `{fst = 3, snd = 3}`.

```ocaml
MakeTree = (X : module { type T : * }) -> {
  data TTree = Leaf T | Node TTree TTree

}

M1 = module {
  type T = Int
}

M2 = MakeTree (M1)
M3 = MakeTree (M1)
```

In the example above, `M1.TTree` and `M2.TTree` are distinct datatypes
that aren't equal to each other, even though both are trees that hold
`Int` leaves.

## Local models ##

Local models allow model identifiers to be bound locally in the scope
of a module definition.

```ocaml
Mflip = model {
  val x ~ flip 0.5
}

M = local
  X ~ Mflip
  in model {
    val y ~ case X.x of
      True -> flip 0.9
      False -> flip 0.1
  } : model type {
    sig y : Bool
    }
```

The general syntax is

```ocaml
local defns in ModelExpr : ModelType
```

Note that the model type is required and may not mention any of the local
definitions.

## Module sealing ##

Module sealing narrows the interface of a module or model by hiding
some components, or by hiding the manifest definition of some type
components behind an abstract type.

```ocaml
ABSTRACT_TREE = module type {
  type Element :: *
  type Tree :: *
  sig empty :: Tree
  sig insert :: Tree -> Element -> Tree
}

IntBinaryTree = module {
  type Element = Int
  data Tree = Leaf Int | Node Tree Tree
  sig insert :: Tree -> Element -> Tree
  fun insert t x = ...
}

SealedTree = IntBinaryTree : ABSTRACT_TREE
```

The type `SealedTree.Tree` is abstract and clients of the `SealedTree`
module do not get to see its implementation.

## Model observations ##

Observations in *Insomnia* allow models to construct posterior models
that incorporate evidence into prior models.

```ocaml
FullModel = model {
  val r ~ beta 1 1
  ObservationKernel = model {
    val x ~ flip r
  }
}

M = module { val x = True }

Mposterior = observe FullModel where ObservationKernel is M
```

The `observe` model expression draws a new sample `O` from the
`ObservationKernel` submodel of `FullModel` and conditions the
outcomes of its fields to the values of the fields of `M`.  This has
the effect of constructing `Mposterior` as a model whose distribution
for the `r` component is `beta 2 1`.  (In this case one may exploit
conjugacy to exactly characterize the posterior, but in general
*Insomnia* uses conditioning to reject samples from `Mposterior` in
which the observation does not hold.)

# Types and Kinds#

Types in *Insomnia* classify values.

Insomnia's types include:

1. Type constructor paths
2. The base types
3. Functions
4. Polymorphic Functions
5. Type variables
6. Records

Types are classified by kinds.  The base types, function types,
records and polymorphic functions have kind `*`.  Polymorphic type
variables must be annotated with their kind.  Plain inductive
datatypes have kind `*`.  Polymorphic datatypes of the form `data T
(a1 : k1) ... (aN : kN)` have kind `k1 -> ... -> kN -> *`.

## Constructor Paths ##

Types that are defined in modules or submodules visible from the current scope may be mentioned in types by separating the module path from the type with a `.`, for example:

```ocaml
  type T = Prelude.Bool
```

The local type alias `T` is defined to be equal to the type `Bool`
from the `Prelude` module.

## Base Types ##

The base types are `Int` and `Real`.

## Functions ##

Monomorphic functions that take an argument `T1` and return a result
`T2` have type `T1 -> T2`.

In Insomnia, monomorphic function types are inferred by the typechecker.

## Polymorphic Functions ##

Polymorphic functions have a type `forall (a : K) . T` where `T` may
mention the type variable `a`.  For example: `forall (a : *) . List a
-> Bool` is the type of a function that works on any list and returns
a boolean.

In Insomnia, polymorphic functions must be annotated with their type signature.

## Type variables ##

Type variables may appear in types.  For example

```ocaml
data Stream (a :: *) = SCons a ({} -> Stream a)
```

The `Stream` polymorphic datatype contains a value of type `a` and a
function from the unit type to another stream.

Type variables must begin with a lowercase letter.

The kind annotation on type variables is required.

## Records ##

A record type `{ f1 : T1; ...; fN : TN }` contains zero or more fields.
The fields must being with a lower case letter and a record type must
contain distinct field names.

The record type `{}` with zero fields is called the *unit type* and
contains a single value `{}`.

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

## Value constructor paths ##

If a data type definition is in scope with a constructor `C` , or if
`M` is a module identifier that has a datatype with a constructor `C`,
or if `M.F` is a submodule of a module and has a constructor C, then
`C`, `M.C` or `M.F.C`, respectively, may be used to construct values
of the corresponding data type.

Value constructors may also be used as functions that take some number
of arguments and then construct the corresponding datatype value (so
they can be passed around to higher-order functions, returned from
functions, stored in containers, etc.).

## Literal values ##

Literal decimal integer values are written using the digits 0-9 and optional
leading `+` and `-` signs.  Their range is not yet specified.

Literal decimal floating point values are written using the digits 0-9
with a required decimal point `.` and optional leading `+` and `-`
signs.  Exponential notation is also permitted: `5e-1` is the same as `0.5`

## Lambda expressions ##

Lambda expressions are written as `\x -> e` or `\(x:T) -> e` and denote (monomorphic, unless bound to a variable with a polymorphic type annotation) functions.

## Function application ##

Function application is written as juxtaposition `not True`, `flip 0.5`

## Let expressions ##

Let expressions allow the introduction of some local bindings in the
scope of a body expression.

Let expressions that have at least one sample binding must have a body
of type `Dist T` for some `T`.  Let expressions without any samples may
have a body of any type.

```ocaml
  let
    y ~ flip 0.5
    x = not y
  in
    return { fst = x, snd = y }
```

### Value bindings ###

```ocaml
let x = y + y
in x * x
```

Bound variables may be optionally annotated with a type: `let (x : Int) = y + y in x * x`

### Sample bindings ###

Sample bindings may be used to locally sample a value from a
distribution.  The let expression's body must have type `Dist T` for
some `T`.

```ocaml
let
  r ~ beta 1 1
in
  flip r
```

### Tabulated function bindings ###

Tabulated function bindings bind a variable to a function value of
type `Dist (E -> T)` by providing an expression `e` of type `Dist T` that
depends on a variable `idx` of type `E`:

```ocaml
  let
    forall (i : E) .
      f i ~ e
  in
    f
```

## Point distribution ##

The point distribution expression `return e` has type `Dist T` and
represents the point-mass distribution at the value `e` of type `T`.

## Record construction ##

Records may be constructed via the form `{ f1 = e1, ..., fN = eN }`.
If each `ei` has type `Ti` the whole record has type `{ f1 : T1; ...;
fN : TN }`

For example:

```ocaml
  type IntPair = { fst : Int; snd : Int }
  sig p : Int Pair
  val p = { fst = 3, snd = 4 }
```

All the fields of a record must be distinct.

## Case analysis by pattern matching ##

Case analysis may be used to work with record and value constructor values.

The general form is

```ocaml
  case e of
    pat1 -> e1
    ...
    patK -> eK
```

where each expression `ei` must have the same type `T` which is the
type of the whole expression.

Patterns are tried in order from first to last.  Redundant or
non-exhaustive patterns do not trigger a compile-time error or
warning.  Non-exhaustive patterns will cause a runtime error if a value is not matched.


## Patterns ##

The patterns are:

1. wildcard
2. variable binding
3. value constructor match
4. record field match

### Wildcard ###

The wildcard pattern `_` always matches:

```ocaml
  fun f x = case x of
    _ -> x
```

### Variable ###

The variable pattern always matches and binds the variable to the
value that is being matched in the expression.

```ocaml
  fun f x = case x of
    y -> y
```

### Value constructor match ###

If `C` is a value constructor of *K* arguments, then `C pat1 ... patK`
matches if the value being matched was constructed using `C` and the
corresponding arguments each match the corresponding subpattern.

```ocaml
  data Tree = Leaf Int | Node Tree Tree

  sig height :: Tree -> Int
  fun height t = case t of
    Leaf -> 0
    Node l r -> 1 + max (height l) (height r)
```

### Record Field Match ###

The pattern `{ f1 = pat1, ..., fK = patK }` matches provided that the
subpatterns `pati` each match the corresponding field of the value
being matched.

```ocaml
  sig swap : forall (a :: *) (b :: *)
             . { fst : a; snd : b } -> {fst : b; snd : a}
  fun swap p = case p of
    ({fst = x, snd = y}) -> { fst = y, snd = x }
```

Note that because of a parser ambiguity, if a record pattern is the
outermost pattern in a clause, it should be enclosed in parentheses,
as above.

# Builtins, Prelude, Libraries #

The boot file `examples/boot.ism` specifies the low-level primitives
provided by the *Insomnia* interpreter internally, and by the
*Insomnia* compiler via the Racket module `examples/boot.rkt`.
(Extending *Insomnia* beyond these primitives involves modifying the
compiler source code and is beyond the scope of this Guide.)

The file `examples/Prelude.ism` provides the "user-friendly" versions
of the various primitives as well as basic datatypes such as `Bool` and `List a`.

# Known Issues #

## Version 0.0.4 ##

* Tabulated functions typecheck, but are not yet fully supported by the
interpreter or the compiler.

* The compiler does not turn `query` toplevel operations into runnable
  Racket code.  The current best mode of use is to manually wrap calls
  to *Insomnia* modules in a sampler form:

    In Insomnia, `example/MyModel.ism`:

    ```ocaml
      MyModel = model {
        val f ~ flip 0.5
      }
    ```

    After compilation, in Gamble:

    ```scheme
    #lang gamble
    (require gamble/viz)
    (require "example/MyModel.rkt")

    (define s
      (mh-sampler (MyModel)))
 
    (hist (repeat s 100))
    ```
* The compiler and interpreter have debug output turned on by default,
  there is a lot of compilation noise.

