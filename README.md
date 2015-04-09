# PTS

## Summary

A Haskell implementation of the Pure Type System


## Installation ##

Run the following commands at the top:

```
cabal sandbox init
make
```

## REPL

```
make repl
```

Following commands are available:

+ `:t expr`: show the type of `expr`
+ `:e expr`: evaluate expression `expr`
+ `:eq exp1 exp2`: definitional equality on `exp1` and `exp2`
+ `:env`: show the current environment
+ `:clr`: clear the current typing environment
+ `:add name expr`: Add (`name`, `expr`) binding to the current typing environment
+ `:let name expr`: Bind `expr` to `name` so that it can used later on
+ `:q`: quit gracefully


## Run Tests

```
make test
```
