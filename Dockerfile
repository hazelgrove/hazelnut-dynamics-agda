from haskell:7.10.3
run cabal update
run cabal install Agda-2.5.1
copy . .
cmd ["agda" , "all.agda"]
