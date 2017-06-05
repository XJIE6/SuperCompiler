module SuperCompiler where
import Data.Tree
import Data.Either
import Data.Maybe
import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Trans.Either
import Data.Foldable
import Debug.Trace

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
    | Let [Expr] Expr 
    | Counted Expr deriving (Eq)

data Pattern = Var | Pattern String Int deriving (Eq)

data Step a = Transient a | Stop | Variants Expr [(Pattern, a)] | Decompose [a] | Fold a [Expr] deriving (Show)

data Node' a = Node' a [a] (Step (Node' a)) deriving (Show)

fmap'' :: (Expr -> Expr) -> Expr -> Expr
fmap'' f v@(Variable _)      = v
fmap'' f (Unfold s i e)      = Unfold s i $ f e
fmap'' f (Lambda e)          = Lambda $ f e
fmap'' f (Application e1 e2) = Application (f e1) (f e2)
fmap'' f c@(Call _)          = c
fmap'' f (Constructor n l)   = Constructor n $ map f l
fmap'' f (Case e l)          = Case (f e) $ map (fmap f) l
fmap'' f (Let l e)           = Let (map f l) $ f e
fmap'' f (Counted e)         = Counted $ f e

shift :: Int -> Expr -> Expr
shift = shift' 0

shift' :: Int -> Int -> Expr -> Expr
shift' c d v@(Variable i)   = if i >= c then Variable (i + d) else v
shift' c d (Lambda e)       = Lambda $ shift' (c + 1) d e
shift' c d e                = fmap'' (shift' c d) e

context :: Expr -> Expr -> Expr
context new e = fmap'' (\e -> if e == empty then new else context new e) e

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

match :: Expr -> [Expr] -> (Pattern, Expr) -> Maybe (Pattern, Expr, [Expr])
match e1 g (Var, e2)                           = error ("think") --Just (Application e2 e1, g)
match (Variable i) g (p@(Pattern n j), e2)         = let new = Constructor n $ map (\x -> Unfold n x $ Variable i) [0..(j - 1)] in Just (p, intoMatch i new e2, goUp i new g)
match c@(Constructor n1 p) g (p'@(Pattern n2 i), e) = if n1 /= n2 then Nothing else 
                                                  if length p /= i then error ("different params number" ++ (show $ (Constructor n1 p)) ++ (show $ (Pattern n2 i, e))) else Just (p', e, g)
match _ g (p, e)                               = Just (p, e, g)

next :: [Expr] -> Maybe (Expr, [Expr])
next []     = Nothing
next (x:xs) = case x of 
                Counted _ -> fmap (fmap ((:) x)) $ next xs
                e         -> Just (e, empty:xs)

intoEmpty :: Int -> Expr -> Expr
intoEmpty i (Lambda e) = Lambda $ intoEmpty (i + 1) e
intoEmpty i e = if e == empty' then Variable i else fmap'' (intoEmpty i) e

empty  = Variable (-1)
empty' = Variable (-2)

beta i e2 e = shift (-1) $ into i (shift 1 e2) e
-- beta' e (Lambda e') = beta e e'
-- beta' e1 e2 = Application e2 e1

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
                                                    Lambda e  -> Node' h g $ Transient $ buildExpr f g $ beta 0 e2 e
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

buildExpr f g h@(Case e p)                    = case g of 
                                                (Case _ l):xs -> needy h g $ buildExpr f xs $ Case e $ map (\(p, e) -> (p, Case e l)) p
                                                _ -> case e of 
                                                        (Counted e) -> let res = catMaybes $ map (match e g) p in
                                                                            case length res of
                                                                                0 -> Node' h g Stop
                                                                                1 -> Node' h g $ Transient $ Node' h g $ Transient $ buildExpr f ((\(_, _, x) -> x) $ head res) $ (\(_, x, _) -> x) $ head res
                                                                                _ -> Node' h g $ Variants e $ map (\(p, x, y) -> (p, buildExpr f [] x)) res
                                                        _           -> needy h g $ buildExpr f ((Case empty p):g) e

buildExpr f g h@(Call n)                      = Node' h g $ Transient $ buildExpr f g $ case findF n f of
                                                                                                Just (FunDef _ e) -> e
                                                                                                _                 -> error "no such function"

buildExpr f g h@(Counted e)                   = needy h g $ buildExpr f g e

buildExpr f g h@(Let l e)                     = Node' h g $ Decompose $ (buildExpr f g e) : (map (buildExpr f g) l)

buildExpr f g h@(Unfold n i e)                = case e of
                                                    (Counted e') -> case e' of 
                                                                        (Constructor n' l) -> if n == n' then Node' h g $ Transient $ buildExpr f g $ l!!i else error ("unfold from different constructor")
                                                                        (Counted _)        -> error ("double Counted")
                                                                        _                  -> case g of
                                                                                                []     -> Node' h g Stop
                                                                                                (x:xs) -> needy h g $ buildExpr f xs $ context (Counted h) x
                                                    _ -> needy h g $ buildExpr f ((Unfold n i empty):g) $ e

data Node'' a = Node'' Int a [a] (Step (Node'' a)) deriving (Show)

exactMatch :: Int -> Expr -> Expr -> Maybe [(Int, Expr)]
exactMatch n (Variable i) e                          = Just [(i - n, e)]
exactMatch n (Unfold s j (Variable i)) e             = Just [(i - n, Constructor s $ (take (j - 1) $ repeat empty) ++ [e])]
exactMatch n (Lambda e1) (Lambda e2)                 = exactMatch (n + 1) e1 e2
exactMatch n (Application e1 e2) (Application e3 e4) = (++) <$> exactMatch n e1 e3 <*> exactMatch n e2 e4
exactMatch n (Call s1) (Call s2)                     = if s1 == s2 then Just [] else Nothing
exactMatch n (Constructor s1 l1) (Constructor s2 l2) = if s1 == s2 then foldr (\a b -> (++) <$> a <*> b) (Just []) $ zipWith (exactMatch n) l1 l2 else Nothing
exactMatch _ _ _                                     = Nothing

strongExactMatch :: Int -> Int -> Expr -> Expr -> Maybe (([(Int, Expr)], [(Int, Expr)], Int, Bool), Expr)
strongExactMatch i n (Lambda e1) (Lambda e2)                 = fmap (fmap Lambda) $ strongExactMatch i (n + 1) e1 e2
strongExactMatch i n (Application e1 e2) (Application e3 e4) = case (strongExactMatch i n e1 e3) of
                                                                Just ((l1, l2, i', b), e) -> case strongExactMatch i' n e2 e4 of
                                                                                            Just ((l1', l2', i'', b'), e') -> Just ((l1 ++ l1', l2 ++ l2', i'', b), Application e e')
                                                                                            Nothing -> Nothing
                                                                _ -> Nothing
strongExactMatch i n (Call s1) (Call s2)                     = if s1 == s2 then Just (([], [], 0, True), Call s1) else Nothing
--strongExactMatch n (Constructor s1 l1) (Constructor s2 l2) = if s1 == s2 then foldr (\a b -> (++) <$> a <*> b) (Just []) $ zipWith (exactMatch n) l1 l2 else Nothing
strongExactMatch i n e1 e2                                   = Just (([(i + n, e1)], [(i + n, e2)], 1, False), Variable $ i + n)

dummyMatch' :: Expr -> Expr -> Maybe [(Int, Expr)]
dummyMatch' l@(Lambda e1) e2 = case exactMatch 0 l e2 of
                                Just l  -> Just l
                                Nothing -> dummyMatch' e1 e2
dummyMatch' e1 e2            = exactMatch 0 e1 e2

weakMatch' e1 e2 = weakMatch'' 0 e1 e2

weakMatch'' :: Int -> Expr -> Expr -> Maybe (Expr, Expr)
weakMatch'' i e1 l@(Lambda e2)         = case dummyMatch' e1 l of
                                        Just _  -> Just (l, empty')
                                        Nothing -> fmap (fmap Lambda) $ weakMatch'' (i + 1) e1 e2
weakMatch'' i e1 a@(Application e2 e3) = case dummyMatch' e1 a of
                                        Just _  -> Just (a, empty')
                                        Nothing -> case (weakMatch' e1 e2, weakMatch'' i e1 e3) of
                                                        (Just p1, Just p2) -> error ("That is incredible!")
                                                        (Just p1, Nothing) -> Just $ fmap (\x -> Application x e3) p1
                                                        (Nothing, Just p2) -> Just $ fmap (Application e2) p2
                                                        _                  -> Nothing
weakMatch'' i e1 c@(Constructor n l)   = case dummyMatch' e1 c of 
                                        Just _  -> Just (c, empty')
                                        Nothing -> foldr (\(y, i) x -> x <|> fmap (fmap (\z -> Constructor n $ take i l ++ [z] ++ drop (i + 1) l)) (weakMatch'' i e1 y)) Nothing $ zip l [0..]
weakMatch'' i e1 e2                    = case dummyMatch' e1 e2 of 
                                        Just _  -> Just (e2, empty') 
                                        Nothing -> Nothing

strongMatchSubexpr :: Expr -> Expr -> Maybe (([(Int, Expr)], [(Int, Expr)], Int, Bool), Expr)
strongMatchSubexpr e1 l@(Lambda e2)         = case strongExactMatch 0 0 e1 l of
                                            Just x -> Just x
                                            Nothing -> strongMatchSubexpr e1 e2
strongMatchSubexpr e1 a@(Application e2 e3) = case strongExactMatch 0 0 e1 a of
                                            Just x -> Just x
                                            Nothing -> strongMatchSubexpr e1 e2 <|> strongMatchSubexpr e1 e3
strongMatchSubexpr e1 c@(Constructor n l) = case strongExactMatch 0 0 e1 c of
                                            Just x -> Just x
                                            Nothing -> foldr (\e2 x -> x <|> strongMatchSubexpr e1 e2) Nothing l
strongMatchSubexpr e1 e2 = case strongExactMatch 0 0 e1 e2 of
                                            Just x -> Just x
                                            Nothing -> Nothing

apply n f x = if n == 0 then x else apply (n - 1) f (f x)

strongMatch :: Node' Expr -> Node'' Expr -> Maybe (Int, Expr)
strongMatch (Node' e' g' _) x@(Node'' i e g _) = case strongMatchSubexpr (put' e g) (put' e' g') of
                                                    Just ((_, _, j, b), y) | b == True -> Just (i, apply j Lambda y)
                                                    _ -> Nothing

weakMatch :: Node' Expr -> Node'' Expr -> Maybe (Expr, Expr)
weakMatch (Node' e' g' _) x@(Node'' i e g _) = weakMatch' (put' e g) (put' e' g')
dummyMatch :: Node' Expr -> Node'' Expr -> Maybe (Node'' Expr, [(Int, Expr)])
dummyMatch (Node' e' g' _) x@(Node'' i e g _) = fmap (\y -> (x, y)) $ dummyMatch' (put' e g) (put' e' g')

return' :: Expr -> [Expr] -> Step (Node'' Expr) -> State Int (Node'' Expr)
return' a b c = do 
    i <- get
    return $ Node'' i a b c

normalise::[(Int, Expr)] -> Maybe [Expr]
normalise l = normalise' 0 (fst $ maximumBy (\(x, _) (y, _) -> compare x y) l) l
normalise' :: Int -> Int -> [(Int, Expr)] -> Maybe [Expr]
normalise' i n l = if i > n then Just [] else
                    case filter (\(i', _) -> i' == i) l of
                        []   -> normalise' (i + 1) n l
                        (_, e):[] -> (:) e <$> normalise' (i + 1) n l
                        (i', e):xs -> if all (\(i'', e') -> (i'' /= i') || (i'' == i' && e == e')) l then (:) e <$> normalise' (i + 1) n l else Nothing

catEithers :: [Either a b] -> Either a [b]
catEithers []     = Right []
catEithers (x:xs) = (:) <$> x <*> catEithers xs

upEither :: (a, Either b c) -> Either (a, b) (a, c)
upEither (x, Right y) = Right (x, y)
upEither (x, Left y)  = Left (x, y)

buildGraph :: [FunDef] -> [Node'' Expr] -> Node' Expr -> State Int (Either (Int, Expr) (Node'' Expr))
buildGraph f ns (Node' e g Stop)             = 
                                                trace ("Stop \n") $
                                                do
                                                i <- get
                                                return $ Right $ Node'' i e g Stop
buildGraph f ns node@(Node' e g (Transient node')) = 
                                                    trace ("Trans " ++ (show $ put' e g) ++ "\n") $
                                                    let ok = catMaybes $ map (dummyMatch node) ns in
                                                    trace (show ok) $
                                                    case catMaybes $ map (\(n, l) -> (\x -> (n, x)) <$> normalise l) $ ok of
                                                        (a, b):xs -> trace ("dummy ok\n") $ do
                                                                        i <- get
                                                                        return $ Right $ Node'' i e g $ Fold a b
                                                        []   -> trace ("dummy fail\n") $ case catMaybes $ map (weakMatch node) ns of
                                                                (e', c):xs -> trace ("weak ok\n" ++ (show $ put' e g) ++ "\n" ++ show e' ++ "\n" ++ show c ++ "\n END \n") $ buildGraph f ns $ buildExpr f [] $ Let [e'] $ intoEmpty 0 (shift 1 c)
                                                                []        -> trace ("weak fail\n") $ case catMaybes $ map (strongMatch node) ns of
                                                                                (j, e'):xs -> trace ("strong ok\n") $do
                                                                                                i <- get
                                                                                                trace ("OOOPS " ++ show e' ++ "\n") $ return $ Left (j, e')
                                                                                                --error (show j ++ " " ++ show e')
                                                                                                
                                                                                _ -> trace ("strong fail\n") $ do
                                                                                    i <- get
                                                                                    put $ i + 1
                                                                                    res <- buildGraph f (Node'' i e g Stop :ns) node'
                                                                                    case res of
                                                                                        Left (i', e') | i > i'  -> return $ Left (i', e')
                                                                                        Left (i', e') | i < i'  -> return $ error $ show (i', e') --let Node' e' g' _ = node' in error (show $ put' e g)
                                                                                        Left (i', e')           -> case dummyMatch' e' (put' e g) of
                                                                                                                    Just l  -> do {
                                                                                                                                put i;
                                                                                                                                buildGraph f ns $ buildExpr f [] $ Let (map snd l) e'}
                                                                                                                    Nothing -> error ("wtf") -- error (show e' ++ "\n" ++ (show $ put' e g))
                                                                                        Right (node)            -> return $ Right $ Node'' i e g $ Transient node


buildGraph f ns (Node' e g (Decompose l))    = 
                                                trace ("Decompose " ++ (show $ put' e g) ++ "\n") $
                                                do 
                                                i <- get
                                                res <- sequence $ map (\x -> modify ((+) 1) >> buildGraph f (ns) x) l
                                                case catEithers res of
                                                    Right nodes -> return $ Right $ Node'' i e g $ Decompose nodes
                                                    Left (i', _) | i == i' -> error (show $ put' e g )
                                                    Left err -> return $ Left err

buildGraph f ns (Node' e g (Variants e' l))     = 
                                                trace ("Variants " ++ (show $ put' e g) ++ "\n") $
                                                do 
                                                i <- get
                                                res <- sequence $ map (\(p, x) -> modify ((+) 1) >> buildGraph f (ns) x >>= \res -> return (p, res)) l
                                                case catEithers $ map upEither res of
                                                    Right nodes -> return $ Right $ Node'' i e g $ Variants e' nodes
                                                    Left (_, (i', _)) | i == i' -> error ("no way")
                                                    Left (p, err) -> return $ Left err

put'' :: Int -> Int -> [Expr] -> Expr -> Expr
put'' j i l (Variable x) = if (x - j < i) then l !! (x - j) else Variable (x - i)
put'' j i l (Lambda e) = put'' (j + 1) i l e
put'' j i l e = fmap'' (put'' j i l) e


buildProgram :: Node'' Expr -> State ([String], [(Int, String, Int)], [FunDef]) Expr

buildProgram (Node'' i e g Stop) = trace ("just stop\n") $ return $ put' e g

buildProgram (Node'' i e g (Variants e' l)) = do
                                                res <- sequence $ map (buildProgram . snd) l
                                                let res' = zipWith (\(p, _) r -> (p, r)) l res
                                                trace ("variants " ++ show g ++ "\n"++ show e' ++ "\n" ++ show res' ++ "\n") $ return $ put' (Case e' res') g

buildProgram (Node'' i e g (Decompose (x:l))) = do
                                                    x' <- buildProgram x
                                                    res <- sequence $ map buildProgram l
                                                    trace ("decompose " ++ show x' ++ "\n" ++ show res ++ "\n") $ return $ put'' 0 (length res) res x'

buildProgram (Node'' i e g (Fold (Node'' i' e' g' _) l)) = do
                                                            (name:names, f, def) <- get
                                                            case find (\(i'', _, _) -> i'' == i') f of
                                                                Just (i'', name, _) -> trace ("fold" ++ name ++ "\n") $ return $ foldl Application (Call name) l
                                                                Nothing -> 
                                                                           do { put (names, (i', name, length l):f, def);
                                                                           trace ("fold " ++ name ++ "\n") $ return $ foldl Application (Call name) l}
buildProgram (Node'' i e g (Transient n)) = do
                                                e' <- buildProgram n
                                                (names, f, def) <- get
                                                case find (\(i', _, _) -> i' == i) f of
                                                    Just (i', name, params) -> do {
                                                                        put (names, f, (FunDef name $ discount e'):def);
                                                                        trace ("I function " ++ name ++ "\n") $ return $ foldl Application (Call name) $ map Variable [0..(params - 1)] }
                                                    Nothing -> trace ("go next\n") $ return e'


discount :: Expr -> Expr
discount (Counted e)         = discount e
discount e                   = fmap'' discount e

build::Program -> Node' Expr
build (Program l e) = buildExpr l [] e

buildG::Program -> Node'' Expr
buildG p@(Program l e) = case evalState (buildGraph l [] (build p)) 0 of
                            Right x -> x
                            Left y -> error $ show y

buildP::Program -> Program
buildP p = case length $ take 1000000 $ drawTree $ pretty''$ buildG p of
                1000000 -> error $ "infinite"
                _ -> let (res, (_, _, funs)) = runState (buildProgram $ buildG p) (["a", "b", "c"], [], []) in Program funs $ discount res

put' e []     = e
put' e (x:xs) = put' (context e x) xs

scope x = (Constructor "Scope" [x])

pretty':: Node' Expr -> Tree String
pretty' (Node' e g Stop)          = Node (show $ put' (scope e) g) []
pretty' (Node' e g (Transient n)) = Node (show $ put' (scope e) g) [pretty' n]
pretty' (Node' e g (Variants e' l)) = Node (show $ put' (scope e) g) $ map (pretty'.snd) l
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
pretty'' (Node'' i e g (Variants e' l))  = Node (show i ++ " CASE " ++ (show $ put' (scope e) g)) $ map (pretty''.snd) l
pretty'' (Node'' i e g (Decompose l)) = Node (show i ++ " " ++ (show $ put' (scope e) g)) $ map pretty'' l
pretty'' (Node'' i e g (Fold (Node'' i' e' g' _) l)) = Node (show i ++ " GO " ++ (show $ put' (scope e) g) ++ " TO " ++ show i' ++ " " ++ (show $ put' (scope e') g') ++ " " ++ (show l)) []
