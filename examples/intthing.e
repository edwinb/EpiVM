include "Prelude.e"

-- main () -> Unit =
--    printInt(foo(10))

export "foo" foo (x:Int) -> Int =
    if x<=0 then 1 else x*foo(x-1)
