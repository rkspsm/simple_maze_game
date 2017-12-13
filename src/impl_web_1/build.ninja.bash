rule kotlin
  command = kotlinc-js $in -output $out

rule copy
  command = cp -f $in $out

rule clean
  command = ninja -t clean

build main.js : kotlin ../src/impl_web_1/Main.kt

build index.html : copy ../src/impl_web_1/index.html

build style.css : copy ../src/impl_web_1/style.css

build one_small_garden.js : copy ../src/impl_web_1/one_small_garden.js
# build supp.js : copy ../src/impl_web_1/supp.js

build clean : clean

#default main.js index.html style.css supp.js
default main.js index.html style.css one_small_garden.js

