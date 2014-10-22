The Insomnia Programming Language
=================================

Insomnia is a strongly typed probabilistic programming language.

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

5. Try an example

    $ dist/build/Insomnia/insomnia t.ism


    
