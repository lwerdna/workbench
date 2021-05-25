-- https://wiki.haskell.org/99_questions/1_to_10

-- run with:
-- $ runhaskell prob01_10.hs
-- or
-- ghci> :load prob01_10.hs
-- ghci> :main

-- prob1 --
myLast :: [a] -> a
myLast [] = error "last of empty list!"
myLast [x] = x
myLast (x:xs) = myLast xs

-- prob2 --
myButLast :: [a] -> a
myButLast [] = error "error"
myButLast [x] = error "error"
myButLast (x:y:[]) = x
myButLast (x:y:xs) = myButLast (y:xs)

-- prob3 --
elementAt :: [a] -> Int -> a
elementAt (x:xs) 1 = x
elementAt (x:xs) i = elementAt xs (i-1)

-- prob4 --
myLength' :: [a] -> Int -> Int
myLength' [] y = y
myLength' (x:xs) y = myLength' xs y+1

myLength :: [a] -> Int
myLength x = myLength' x 0

-- prob5 --
myReverse' :: [a] -> [a] -> [a]
myReverse' [] y = y
myReverse' (x:xs) y = myReverse' xs y++[x] -- TIL: cons only works at beginning of list

myReverse :: [a] -> [a]
myReverse x = myReverse' x []

-- prob6 --
isPalindrome :: Eq a => [a] -> Bool -- TIL: class constraint, a must be in Eq, else == won't work
isPalindrome [] = True
isPalindrome [x] = True
isPalindrome x = head x == last x && isPalindrome (init (tail x))

main = do
    print (myLast [1,2,3])
    print (myButLast ['a', 'b', 'c'])
    print (myButLast [1,2,3,4])
    print (myButLast ['a'..'z'])
    print (elementAt [1,2,3] 2)
    print (elementAt "haskell" 5)
    print (myLength [123, 456, 789])
    print (myLength "Hello, world!")
    print (myReverse "A man, a plan, a canal, panama!")
    print (myReverse [1,2,3,4])
    print (isPalindrome [1,2,3])
    print (isPalindrome "madamimadam")
    print (isPalindrome [1,2,4,8,16,8,4,2,1])
