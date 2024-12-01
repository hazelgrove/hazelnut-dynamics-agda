from haskell:8.4.3
run cabal update
run cabal install alex
run cabal install happy
run cabal install Agda-2.5.4.2
# Warning: Agda version may be out of date
copy . .
cmd ["agda" , "-v", "2" , "all.agda"]
