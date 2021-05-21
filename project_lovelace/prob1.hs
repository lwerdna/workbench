-- $ runhaskell ./prob1.hs

import Numeric

isclose :: Float -> Float -> Bool
isclose a b = abs (a-b) < 1e-4

fahrenheit_to_celsius :: Float -> Float
fahrenheit_to_celsius f = 5/9 * (f-32)

main = do
        if (isclose (fahrenheit_to_celsius 77.9) 25.5) then putStrLn "ok" else error ""
        if (isclose (fahrenheit_to_celsius 32) 0) then putStrLn "ok" else error ""
        putStrLn (showFloat (fahrenheit_to_celsius 77.9) "")
        putStrLn (showFloat (fahrenheit_to_celsius 32) "")
