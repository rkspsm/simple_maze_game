#! /bin/bash

src="$PWD/../src/impl_web_1"
build="$PWD"
kotlinc-js $src/Main.kt -output main.js
cp -f $src/index.html $build/index.html
cp -f $src/supp.js $build/supp.js

