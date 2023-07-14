Archive of a project I had worked on at around 2021 for several days in an attempt to create a language like idris2 with my own additions

\*\*\*Highly\*\*\* inspired by https://github.com/idris-lang/Idris2 and https://github.com/edwinb/SPLV20

Info:
- records & interfaces
- implicit arguments
- instance arguments, but i do not know how to properly implement instance resolution
- `Refl` can be used for proving
- user clauses -> Case Tree with an incorrect implementation of Jesper Cockx's 
- crude implementation of user-defined operators
- `Type : Type`
- working IO
- MANY poor design choices were made
  - adding `z` to `Term z` for something related to interpreting IO and passing objects around, it did not go well

Example IO program:
```
guessingGame : IO Unit
guessingGame = do
  putl_str stdout "Guess the number"
  ans <- random_int 0 100
  repeat_while do
    put_str stdout "Guess it: "
    flush stdout
    r <- getl_str stdin
    // putl_str stdout (show r)
    case parse_int r of
      None => do
        putl_str stdout "Invalid input, please try again"
        pure True
      Some input => do
        case compare input ans of
          EQ => do
            putl_str stdout "Correct"
            pure False
          LT => do
            putl_str stdout "Too small"
            pure True
          GT => do
            putl_str stdout "Too big"
            pure True
```
