The Insomnia Programming Language
=================================

Insomnia is a strongly typed probabilistic programming language.

Slogans:

* A *model* is a distribution over *modules*.
* *Model sealing* is marginalization.

Building from source - installation instructions
------------------------------------------------

### Cabal sandbox workflow

1. Make sure you have a recent GHC (7.6+, but 7.8+ is better)

2. Make sure you have a recent cabal with support for sandboxes

        $ cabal --version
        cabal-install version 1.20.0.3
        using version 1.20.0.0 of the Cabal library

3. Setup a cabal sandbox in the current directory.

        $ cabal sandbox init

    This creates a sandbox for insomnia in the current directory.

4. Run the usual cabal build

        $ cabal install --only-dependencies
        $ cabal configure
        $ cabal build

    Note that installing the upstream dependencies may take a significant
    amount of time.

    Note 2: At the moment you may need to change the first command to

        $ cabal install --only-dependencies --constraint 'blaze-markup < 0.6.3'

    due to some upstream issues.

5. Try an example

        $ dist/build/Insomnia/insomnia examples/seismology0.ism

    The expected output is a message that the file typechecked okay,
    followed by a pretty-printing of the source code, followed by the
    state of the type unification algorithm at the end of typechecking,
    followed by something like:
    

        Demodularizing
        insomnia: src/Insomnia/Interp/ToLam.hs:(363,3)-(374,71): Non-exhaustive patterns in case

    (Sorry, the backend is a work in progress)
