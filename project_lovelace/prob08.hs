-- TIL: cycle, take

isclose :: Float -> Float -> Bool
isclose a b = abs (a-b) < 1e-2

-- [1, -1/3, 1/5, -1/7, 1/9, -1/11, ...]
series = [(pos_neg k) / (fromIntegral (2*k)+1) | k<-[0..]]
            where
                pos_neg x = cycle [1,-1]!!x

almost_pi :: Int -> Float
almost_pi n = foldr (+) 0 (take n series) * 4

main = do
        if (isclose (almost_pi 25) 3.1815766854350325) then putStrLn "ok" else error ""
        if (isclose (almost_pi 10000) 3.1414926535900345) then putStrLn "ok" else error ""
