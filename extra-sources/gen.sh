#!/bin/bash
printf "generate Core syntax...\n\n"
bnfc --haskell -d -m Core.cf && make
mv ./Core/Test.hs ./
mv ./Core/*.hs ../app/Core/
printf "Done.\n"

