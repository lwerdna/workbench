-- $ runhaskell ./prob2.hs

import Numeric

isclose :: Float -> Float -> Bool
isclose a b = abs (a-b) < 1e-4

-- speed of light, in m/s
c = 299792458

light_time :: Int -> Float
light_time distance = fromIntegral distance / c

main = do
        if (isclose (light_time 376291900) 1.255175) then putStrLn "ok" else error ""
        if (isclose (light_time 299792458) 1.0) then putStrLn "ok" else error ""
        putStrLn (showFloat (light_time 376291900) "")
        putStrLn (showFloat (light_time 299792458) "")
