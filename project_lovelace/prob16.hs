transcribe_single :: Char -> Char
transcribe_single nucl
    | nucl == 'T' = 'U'
    | otherwise = nucl

transcribe :: String -> String
transcribe ([]) = []
transcribe (x:xs) = transcribe_single x : transcribe xs

rna :: String -> String
rna x = (reverse . transcribe) x
-- rna x = reverse (transcribe x)

main = do
        if rna "CCTAGGACCAGGTT" == "UUGGACCAGGAUCC" then putStrLn "ok" else error ""
