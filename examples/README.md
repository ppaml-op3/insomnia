# Examples/Tests

The files in this directory are meant to be examples of insomnia syntax, as well as tests of Insomnia.

Run the tests using `cabal test` from the toplevel directory.

## Test format

The test runner [InsomniaProvider](../tests/InsomniaProvider.hs) uses specially formatted comments
at the beginning of an `.ism` file to decide how to run the test.

An example:

```haskell
-- insomnia test flags:
-- eval: False

```

All flags begin with the line comment `-- insomnia test flags:` and consist of `name: value` pairs
until the next non-commented line (usually a blank line).

Flag names are case-sensitive.  Flag values are stripped of leading
and trailing whitespace and fed to the Haskell `Read` class.

### Test flags

The only flag currently available is

| Flag | Type / Allowed Values | Default Value if flag omitted | Description |
|:----:|:----------------------|:------------------------------|:------------|
| eval | Bool / True, False    | True                          | If True, evaluate the FOmega code after typechecking and elaboration, otherwise just typecheck. |

