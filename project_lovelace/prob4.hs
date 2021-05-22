-- $ runhaskell ./prob4.hs

nand :: Bool -> Bool -> Bool
nand a b = not (a && b)

main = do
        if (nand False False)==True then putStrLn "ok" else error ""
        if (nand False True)==True then putStrLn "ok" else error ""
        if (nand True False)==True then putStrLn "ok" else error ""
        if (nand True True)==False then putStrLn "ok" else error ""
