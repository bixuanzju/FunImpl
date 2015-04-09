# PTS

## Summary

A Haskell implementation of the Pure Type System


## Installation ##

Run the following commands at the top:

```
cabal sandbox init
cabal install --only-dependencies --enable-tests
```

## REPL

```
make repl
```

Following commands are available:

+ `:t expr`: show the type of `expr`
+ `:e expr`: evaluate expression `expr`
+ `:env`: show the current typing environment
+ `:clr`: clear the current typing environment
+ `:add name expr`: Add (`name`, `expr`) binding to the current typing environment
+ `:q`: quit gracefully


## Run Tests

```
make test
```
