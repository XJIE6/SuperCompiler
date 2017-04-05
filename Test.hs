import SuperCompiler
import Data.Tree

infixr 6 ->>
(->>) = Lambda
infix 6 |<
(|<)  = Pattern
infixr 6 >|
(>|) = Case
infix 6 <|
(<|)  = Constructor
infixl 4 ->-
(->-) p e = (p, e)
infixr 5 +++
(+++) s c = s <| [c]
infixr 5 +|
(+|) s1 s2 = s1 +++ s2 <| [] 

infixl 8 @@
(@@)  = Application
infixl 9 |@
(|@) s e = Application (Call s) e
infixl 7 @|
(@|) e1 e2 = Application e1 e2




n = Name
v = Variable

def = FunDef
prog = Program

sum' = def "sum" $
        "a" ->> 
        "b" ->> 
        v "a" >| [
            "Zero" |< []        ->- v "b",
            "Succ" |< [n "a\'"] ->- "Succ" <| ["sum" |@ v "a\'" @@ v "b"]
        ]

prod' = def "prod" $
        "a" ->> 
        "b" ->>
        v "a" >| [
            "Zero" |< []        ->- "Zero" <| [],
            "Succ" |< [n "a\'"] ->- "sum" |@ v "b" @| "prod" |@ v "a\'" @@ v "b"
        ]

fact' = def "fact" $
        "n" ->>
        v "n" >| [
            "Zero" |< []        ->- "Succ" +| "Zero",
            "Succ" |< [n "n\'"] ->- "prod" |@ v "n" @| "fact" |@ v "n"
        ]

v1 = v "n"
v2 = "Succ" +++ "Succ" +++ "Succ" +++ "Succ" +| "Zero"
v3 = "Succ" +| "Zero"
v4 = "Zero" <| []

p1 = prog [sum', prod', fact'] $ "fact" |@ v2
p2 = prog [sum'] $ "sum" |@ v4 @@ v4

main = putStrLn $ take 10000 $ drawTree $ pretty' $ build p1
--main = putStrLn $ take 10000 $ drawTree $ pretty' $ buildExpr [sum', prod', fact'] empty $ "prod" |@ v1 @@ v3