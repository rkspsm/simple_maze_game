rule kotlin
  command = kotlinc-js $in -output $out

rule copy
  command = cp -f $in $out

rule clean
  command = ninja -t clean

build main.js : kotlin ../src/impl_web_1/Main.kt

build index.html : copy ../src/impl_web_1/index.html

build style.css : copy ../src/impl_web_1/style.css

build clean : clean

default main.js index.html style.css

