#!/bin/bash
printf "Source code generation...\n\n"
bnfc --haskell -d -m Core.cf && make
printf "\nMove source code...\n\n"
rm ./Core/Test.hs
mv ./Core/*.hs ../app/Core/
printf "Done.\n"

