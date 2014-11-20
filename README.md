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

4. Install "indentation-0.2.0.1" from https://bitbucket.org/lambdageek/indentation/branch/fix-parsec-3.1.7

    (This is a version of the indentation package that works with recent versions of parsec).

        $ cd ..
        $ git clone git clone https://bitbucket.org/lambdageek/indentation.git
        $ cd indentation.git
        $ git checkout fix-parsec-3.1.7
        $ cd ..

        $ cd insomnia
        $ cabal sandbox add-source ../indentation.igt

    The first few lines checkout the fix-parsec-3.1.7 branch of
    indentation into a directory in the parent of the insomnia
    directory.  The last two lines tell the insomnia sandbox to use the git version of indentation.

4. Run the usual cabal build

        $ cabal install --only-dependencies
        $ cabal configure
        $ cabal build

    Note that installing the upstream dependencies may take a significant
    amount of time.

5. Try an example

        $ dist/build/Insomnia/insomnia u.ism

    The expected output is a message that the file typechecked okay,
    followed by a pretty-printing of the source code, followed by the
    state of the type unification algorithm at the end of typechecking.
    
