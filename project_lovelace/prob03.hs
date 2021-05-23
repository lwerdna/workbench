-- $ runhaskell ./prob3.hs

isclose :: Float -> Float -> Bool
isclose a b = abs (a-b) < 1e-4

a = 2.757
b = 16.793

moose_body_mass :: Float -> Float
moose_body_mass latitude = a*latitude + b

main = do
        if (isclose (moose_body_mass 60.5) 183.5915) then putStrLn "ok" else error ""
