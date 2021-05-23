-- $ runhaskell ./prob5.hs

-- TIL: ^ vs. ^^ vs. **
-- https://wiki.haskell.org/Power_function

isclose :: Float -> Float -> Bool
isclose a b = abs (a-b) < 1e-2

compound_interest :: Float -> Float -> Int -> Float
compound_interest amount rate years = amount * (1 + rate)**(fromIntegral years)

main = do
        if (isclose (compound_interest 1000 0.07 25) 5427.43) then putStrLn "ok" else error ""
