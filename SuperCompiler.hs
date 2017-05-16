module SuperCompiler where
import Data.Tree
import Data.Either
import Data.Maybe
import Control.Applicative hiding (empty)
import Control.Monad.State

data Program = Program [FunDef] Expr deriving (Show)

data FunDef = FunDef String Expr deriving (Show)

data Expr = 
      Variable Int
    | Unfold String Int Expr
    | Lambda Expr
    | Application Expr Expr
    | Call String
    | Constructor String [Expr]
    | Case Expr [(Pattern, Expr)]
    | Let Expr Expr 
    | Counted Expr deriving (Eq)

data Pattern = Var | Pattern String Int deriving (Eq)

data Step a = Transient a | Stop | Variants [a] | Decompose [a] | Fold (a, [(Int, Expr)]) deriving (Show)

data Node' a = Node' a [a] (Step (Node' a)) deriving (Show)

fmap'' :: (Expr -> Expr) -> Expr -> Expr
fmap'' f v@(Variable _)      = v
fmap'' f (Unfold s i e)      = Unfold s i $ f e
fmap'' f (Lambda e)          = Lambda $ f e
fmap'' f (Application e1 e2) = Application (f e1) (f e2)
fmap'' f c@(Call _)          = c
fmap'' f (Constructor n l)   = Constructor n $ map f l
fmap'' f (Case e l)          = Case (f e) $ map (fmap f) l
fmap'' f (Let l e)           = Let (f l) $ f e
fmap'' f (Counted e)         = Counted $ f e

shift :: Int -> Expr -> Expr
shift = shift' 0

shift' :: Int -> Int -> Expr -> Expr
shift' c d v@(Variable i)   = if i >= c then Variable (i + d) else v
shift' c d (Lambda e)       = Lambda $ shift' (c + 1) d e
shift' c d e                = fmap'' (shift' c d) e

context :: Expr -> Expr -> Expr
context new e = fmap'' (\e -> if e == empty then new else e) e

into :: Int -> Expr -> Expr -> Expr
into n new v@(Variable i) = if n == i then new else v
into n new (Lambda b)     = Lambda $ into (n + 1) (shift 1 new) b
into n new e              = fmap'' (into n new) e

findF :: String -> [FunDef] -> Maybe FunDef
findF name [] = Nothing
findF name (f@(FunDef fName _):xs) = if name == fName then Just f else findF name xs

goUp :: Int -> Expr -> [Expr] -> [Expr]
goUp i e []                = []
goUp i e (x@(Lambda _):xs) = (intoMatch i e x) : goUp (i + 1) e xs
goUp i e (x:xs)            = (intoMatch i e x) : goUp i e xs

intoMatch :: Int -> Expr -> Expr -> Expr
intoMatch _ _ u@(Unfold _ _ _) = u
intoMatch n new v@(Variable i) = if n == i then new else v
intoMatch n new (Lambda b)     = Lambda $ into (n + 1) (shift 1 new) b
intoMatch n new e              = fmap'' (intoMatch n new) e

match :: Expr -> [Expr] -> (Pattern, Expr) -> Maybe (Expr, [Expr])
match e1 g (Var, e2)                           = error ("think") --Just (Application e2 e1, g)
match (Variable i) g (Pattern n j, e2)         = let new = Constructor n $ map (\x -> Unfold n x $ Variable i) [0..(j - 1)] in Just (intoMatch i new e2, goUp i new g)
match c@(Constructor n1 p) g (Pattern n2 i, e) = if n1 /= n2 then Nothing else 
                                                  if length p /= i then error ("different params number" ++ (show $ (Constructor n1 p)) ++ (show $ (Pattern n2 i, e))) else Just (e, g)
match _ g (_, e)                               = Just (e, g)

next :: [Expr] -> Maybe (Expr, [Expr])
next []     = Nothing
next (x:xs) = case x of 
                Counted _ -> fmap (fmap ((:) x)) $ next xs
                e         -> Just (e, empty:xs)

empty  = Variable (-1)

--beta u@(Unfold _ _ _) e = error(show e)
beta e2 e = shift (-1) $ into 0 (shift 1 e2) e

--needy h g = Node' h g . Transient
needy _ _ = id

buildExpr :: [FunDef] -> [Expr] -> Expr -> Node' Expr

buildExpr f g h@(Variable _)                  = case g of
                                                    []     -> Node' h g Stop
                                                    (x:xs) -> needy h g $ buildExpr f xs $ context (Counted h) x

buildExpr f g h@(Lambda e)                    = case g of
                                                    []     -> case e of
                                                                Counted _ -> Node' h g Stop
                                                                _         -> needy h g $ buildExpr f [Lambda empty] $ e
                                                    (x@(Application (Variable n) _):xs) | n == (-1) -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                    (x:xs) -> case e of
                                                                Counted _ -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                                _         -> needy h g $ buildExpr f [Lambda empty] $ e

buildExpr f g h@(Application (Counted e1) e2) = case e1 of
                                                    Lambda e  -> Node' h g $ Transient $ buildExpr f g $ beta e2 e
                                                    Counted _ -> error ("double counted in Application")
                                                    _         -> case e2 of
                                                                    Counted e -> case g of
                                                                                    []     -> Node' h g Stop
                                                                                    (x:xs) -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                                    _         -> needy h g $ buildExpr f ((Application (Counted e1) $ empty):g) e2

buildExpr f g h@(Application e1 e2)           = needy h g $ buildExpr f ((Application empty $ e2):g) e1

buildExpr f g h@(Constructor n p)             = case g of
                                                    [] -> case next p of
                                                            Nothing     -> Node' h g Stop
                                                            Just (e, l) -> needy h g $ buildExpr f ((Constructor n l):g) e
                                                    (x@(Case _ _):xs)     -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                    (u@(Unfold _ _ _):xs) -> needy h g $ buildExpr f xs $ context (Counted h) u
                                                    (x:xs) -> case next p of
                                                            Nothing     -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                            Just (e, l) -> needy h g $ buildExpr f ((Constructor n l):g) e

buildExpr f g h@(Case e p)                    = case e of 
                                                    (Counted e) -> let res = catMaybes $ map (match e g) p in
                                                                        case length res of
                                                                            0 -> Node' h g Stop
                                                                            1 -> Node' h g $ Transient $ Node' h g $ Transient $ buildExpr f (snd $ head res) $ fst $ head res
                                                                            _ -> Node' h g $ Variants $ map (\(x, y) -> buildExpr f y x) res
                                                    _           -> needy h g $ buildExpr f ((Case empty p):g) e

buildExpr f g h@(Call n)                      = Node' h g $ Transient $ buildExpr f g $ case findF n f of
                                                                                                Just (FunDef _ e) -> e
                                                                                                _                 -> error "no such function"

buildExpr f g h@(Counted e)                   = needy h g $ buildExpr f g e

buildExpr f g h@(Let e1 e2)                   = Node' h g $ Decompose [buildExpr f g e1, buildExpr f g e2]

buildExpr f g h@(Unfold n i e)                = case e of
                                                    (Counted e') -> case e' of 
                                                                        (Constructor n' l) -> if n == n' then Node' h g $ Transient $ buildExpr f g $ l!!i else error ("unfold from different constructor")
                                                                        (Counted _)        -> error ("double Counted")
                                                                        _                  -> case g of
                                                                                                []     -> Node' h g Stop
                                                                                                (x:xs) -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                    _ -> needy h g $ buildExpr f ((Unfold n i empty):g) $ e


-- weakMatch (e1, e2) = weakMatch' (discount e1, discount e2)
-- weakMatch' :: (Expr, Expr) -> Maybe [(Int, Expr)]
-- weakMatch' (Variable i,        Variable j)        = if i == j then Just [] else Just [(j, Variable i)]
-- weakMatch' (e,                 Variable n)        = Just [(n, e)]
-- weakMatch' (Lambda e1,         Lambda e2)         = weakMatch (e2, e1)
-- weakMatch' (Application e1 e2, Application e3 e4) = (++) <$> weakMatch (e1, e3) <*> weakMatch (e2, e4)
-- weakMatch' (Constructor n1 p1, Constructor n2 p2) = if n1 == n2 then
--                                                      foldr (\a b -> (++) <$> a <*> b) (Just []) $ map weakMatch $ zip p1 p2
--                                                      else Nothing
-- weakMatch' (Call n1,           Call n2)           = if n1 == n2 then Just [] else Nothing
-- weakMatch' (Counted _,         _)                 = undefined
-- weakMatch' (_,                 Counted _)         = undefined
-- weakMatch' _                                      = Nothing

-- contextMatch :: [Expr] -> [Expr] -> Bool
-- contextMatch ()

-- strongMatch (e1, e2) = strongMatch' (discount e1, discount e2)
-- strongMatch' :: (Expr, Expr) -> Maybe Expr
-- strongMatch' _ = Nothing
-- strongMatch' (Application e1 e2, Application e3 e4) = Application <$> strongMatch (e1, e3) <*> strongMatch (e2, e4)
-- strongMatch' (Call n1,           Call n2)           = if n1 == n2 then Just $ Call n1 else Nothing
-- strongMatch' (Call _, _)                            = Nothing
-- strongMatch' (_, Call _)                            = Nothing
-- strongMatch' (_,                 Variable i)        = Just $ Variable i
-- strongMatch' _                                      = Just $ Variable 0

data Node'' a = Node'' Int a [a] (Step (Node'' a)) deriving (Show)

-- bigStrangeFunction i f e1 g1 node e2 g2 n ns =  case [(n, l) | n@(Node'' _ e3 g3 _) <- ns,  g2 == g3, Just l <- [weakMatch (e2, e3)]] of
--                                                   []       -> case [(j, e4) | n@(Node'' j e3 g3 _) <- ns,  g2 == g3, Just e4 <- [strongMatch (e2, e3)]] of
--                                                               []       -> case buildGraph (i + 1) f node $ (Node'' i e1 g1 Stop):ns of
--                                                                           Right node'    -> Right $ Node'' i e1 g1 (Transient $ node')
--                                                                           Left (k, expr) -> if i == k then 
--                                                                                             case weakMatch (e1, expr) of
--                                                                                                 Just l -> buildGraph i f (Node' (Let l expr) g1 $ Decompose ((buildExpr f g1 expr):(map (\(_, e) -> buildExpr f empty e) l))) ns
--                                                                                                 Nothing -> undefined
--                                                                                             else Left (k, expr)
--                                                               (j, e):_ -> Left (j, e)
--                                                   (n, l):_ -> Right $ Node'' i e1 g1 $ Fold l n

-- buildGraph :: Int -> [FunDef] -> Node' Expr -> [Node'' Expr] -> Either (Int, Expr) (Node'' Expr)
-- buildGraph i f (Node' e g Stop) ns                               = Right $ Node'' i e g Stop

-- buildGraph i f (Node' e1 g1 (Transient node@(Node' e2 g2 n))) ns = bigStrangeFunction i f e1 g1 node e2 g2 n ns

-- buildGraph i f (Node' e1 g1 (Decompose l)) ns                    = let res = map (\node@(Node' e2 g2 n) -> bigStrangeFunction (i + 1) f e1 g1 node e2 g2 n ns) l in
--                                                                     case lefts res of
--                                                                         [] -> Right $ Node'' i e1 g1 $ Decompose $ rights res
--                                                                         _  -> undefined

-- buildGraph i f (Node' e1 g1 (Variants l)) ns                     = let res = map (\node@(Node' e2 g2 n) -> bigStrangeFunction (i + 1) f e1 g1 node e2 g2 n ns) l in
--                                                                     case lefts res of
--                                                                         [] -> Right $ Node'' i e1 g1 $ Variants $ rights res
--                                                                         _  -> undefined


exactMatch :: Int -> Expr -> Expr -> Maybe [(Int, Expr)]
--exactMatch _ l@((Variable _)) a@(Unfold s j (Variable i)) = error (show $ a)
exactMatch n (Variable i) e                          = Just [(i - n, e)]
exactMatch n (Unfold s j (Variable i)) e             = Just [(i - n, Constructor s $ (take (j - 1) $ repeat empty) ++ [e])]
exactMatch n (Lambda e1) (Lambda e2)                 = exactMatch (n + 1) e1 e2
exactMatch n (Application e1 e2) (Application e3 e4) = (++) <$> exactMatch n e1 e3 <*> exactMatch n e2 e4
exactMatch n (Call s1) (Call s2)                     = if s1 == s2 then Just [] else Nothing
exactMatch n (Constructor s1 l1) (Constructor s2 l2) = if s1 == s2 then foldr (\a b -> (++) <$> a <*> b) (Just []) $ zipWith (exactMatch n) l1 l2 else Nothing
exactMatch _ _ _                                     = Nothing

dummyMatch' :: Expr -> Expr -> Maybe [(Int, Expr)]
--dummyMatch' l@(Application (Application (Call _) _) _) a@(Application (Application _ _) _) = error (show $ exactMatch 0 l a)
dummyMatch' l@(Lambda e1) e2 = case exactMatch 0 l e2 of
                                Just l  -> Just l
                                Nothing -> dummyMatch' e1 e2
dummyMatch' e1 e2            = exactMatch 0 e1 e2

weakMatch' :: Expr -> Expr -> Maybe (Expr, Expr)
--weakMatch' e1 l@(Lambda (Constructor _ _)) = error (show l)
weakMatch' e1 l@(Lambda e2)         = case dummyMatch' e1 l of
                                        Just _  -> Just (l, empty)
                                        Nothing -> fmap (fmap Lambda) $ weakMatch' e1 e2
weakMatch' e1 a@(Application e2 e3) = case dummyMatch' e1 a of
                                        Just _  -> Just (a, empty)
                                        Nothing -> case (weakMatch' e1 e2, weakMatch' e1 e3) of
                                                        (Just p1, Just p2) -> error ("That is incredible!")
                                                        (Just p1, Nothing) -> Just $ fmap (\x -> Application x e3) p1
                                                        (Nothing, Just p2) -> Just $ fmap (Application e2) p2
                                                        _                  -> Nothing
--weakMatch' e1 c@(Constructor n ((Application _ _):xs))   = error(show c)
weakMatch' e1 c@(Constructor n l)   = case dummyMatch' e1 c of 
                                        Just _  -> Just (c, empty)
                                        Nothing -> foldr (\(y, i) x -> x <|> fmap (fmap (\z -> Constructor n $ take i l ++ [z] ++ drop (i + 1) l)) (weakMatch' e1 y)) Nothing $ zip l [0..]
weakMatch' e1 e2                    = case dummyMatch' e1 e2 of 
                                        Just _  -> Just (e2, empty) 
                                        Nothing -> Nothing



weakMatch :: Node' Expr -> Node'' Expr -> Maybe (Expr, Expr)
--weakMatch _ _ = Nothing
weakMatch (Node' e' g' _) x@(Node'' i e g _) = weakMatch' (put' e g) (put' e' g')
dummyMatch :: Node' Expr -> Node'' Expr -> Maybe (Node'' Expr, [(Int, Expr)])
--dummyMatch _ _ = Nothing
dummyMatch (Node' e' g' _) x@(Node'' i e g _) = fmap (\y -> (x, y)) $ dummyMatch' (put' e g) (put' e' g')

return' :: Expr -> [Expr] -> Step (Node'' Expr) -> State Int (Node'' Expr)
return' a b c = do 
    i <- get
    return $ Node'' i a b c

tick :: State Int ()
tick = do 
    i <- get
    put $ i + 1

buildGraph :: [FunDef] -> [Node'' Expr] -> Node' Expr -> State Int (Node'' Expr)
buildGraph f ns (Node' e g Stop)             = return' e g Stop
buildGraph f ns node@(Node' e g (Transient node')) = case catMaybes $ map (dummyMatch node) ns of
                                                        x:xs -> return' e g $ Fold x
                                                        []   -> case catMaybes $ map (weakMatch node) ns of
                                                                (e, c):xs -> buildGraph f ns $ buildExpr f [] $ Let e c
                                                                []        -> do
                                                                                i <- get
                                                                                let n = Node'' i e g $ Transient $ evalState (tick >> buildGraph f (n:ns) node') i
                                                                                return n

buildGraph f ns (Node' e g (Decompose l))    = do 
                                                i <- get
                                                let n = Node'' i e g $ Decompose $ cycle' i $ map (\x -> tick >> buildGraph f (n:ns) x) l
                                                return n
buildGraph f ns (Node' e g (Variants l))     = do 
                                                i <- get
                                                let n = Node'' i e g $ Decompose $ cycle' i $ map (\x -> tick >> buildGraph f (n:ns) x) l
                                                return n

cycle' :: Int -> [State Int (Node'' Expr)] -> [Node'' Expr]
cycle' i [] = []
cycle' i (x:xs) = let (res, i') = runState x i in res:(cycle' i' xs)

discount :: Expr -> Expr
discount (Counted e)         = discount e
discount e                   = fmap'' discount e

build::Program -> Node' Expr
build (Program l e) = buildExpr l [] e

buildG::Program -> Node'' Expr
buildG p@(Program l e) = evalState (buildGraph l [] (build p)) 0

put' e []     = e
put' e (x:xs) = put' (context e x) xs

scope x = (Constructor "Scope" [x])

pretty':: Node' Expr -> Tree String
pretty' (Node' e g Stop)          = Node (show $ put' (scope e) g) []
pretty' (Node' e g (Transient n)) = Node (show $ put' (scope e) g) [pretty' n]
pretty' (Node' e g (Variants l))  = Node (show $ put' (scope e) g) $ map pretty' l
pretty' (Node' e g (Decompose l)) = Node (show $ put' (scope e) g) $ map pretty' l

instance Show (Expr) where
    show (Variable n)        = "v" ++ show n
    show (Lambda e)          = "l " ++ show e
    show (Application e1 e2) = "(" ++ show e1 ++ " @ " ++ show e2 ++ ")"
    show (Call n)            = "Call " ++ n
    show (Constructor n l)   = if n == "Scope" then " #< " ++ show (head l) ++ " ># " else n ++ show l
    show (Case e l)          = "Case " ++ show e ++ " of "++ show l
    show (Let l e)           = "Let " ++ show l ++ " in " ++ show e
    show (Counted e)         = "OK (" ++ show e ++ ")"
    show (Unfold n j e)      = "Unfold " ++ n ++ " " ++ show j ++ " " ++ show e

instance Show (Pattern) where
    show Var           = "v"
    show (Pattern n _) = n

pretty'':: Node'' Expr -> Tree String
pretty'' (Node'' i e g Stop)          = Node (show i ++ " " ++ (show $ put' (scope e) g)) []
pretty'' (Node'' i e g (Transient n)) = Node (show i ++ " " ++ (show $ put' (scope e) g)) [pretty'' n]
--pretty'' (Node'' i e g (Transient n)) = pretty'' n
pretty'' (Node'' i e g (Variants l))  = Node (show i ++ " CASE " ++ (show $ put' (scope e) g)) $ map pretty'' l
pretty'' (Node'' i e g (Decompose l)) = Node (show i ++ " " ++ (show $ put' (scope e) g)) $ map pretty'' l
pretty'' (Node'' i e g (Fold (Node'' i' e' g' _, l))) = Node (show i ++ " GO " ++ (show $ put' (scope e) g) ++ " TO " ++ show i' ++ " " ++ (show $ put' (scope e') g') ++ " " ++ (show l)) []
