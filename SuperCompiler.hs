module SuperCompiler where
import Data.Tree
import Data.Either
import Data.Maybe

data Program = Program [FunDef] Expr deriving (Show)

data FunDef = FunDef String Expr deriving (Show)

data Expr = 
    Variable Int
    | Lambda Expr
    | Application Expr Expr
    | Call String
    | Constructor String [Expr]
    | Case Expr [(Pattern, Expr)]
    | Let Expr Expr 
    | Counted Expr deriving (Eq)

data Pattern = Var | Pattern String Int deriving (Eq)

data Step a = Transient a | Stop | Variants [a] | Decompose [a] | Fold a deriving (Show)

data Node' a = Node' a [a] (Step (Node' a)) deriving (Show)

fmap'' :: (Expr -> Expr) -> Expr -> Expr
fmap'' f v@(Variable _)      = v
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
shift' c d (Variable k) = if k >= c then Variable (k + d) else Variable k
shift' c d (Lambda e)   = Lambda $ shift' (c + 1) d e
--shift' c d (Let l e)    = Let (map (shift' c d) l) $ shift' (c + (length l)) d e
shift' c d e            = fmap'' (shift' c d) e

context :: Expr -> Expr -> Expr
context new e = fmap'' (\e -> if e == Variable (-1) then new else e) e

justInto :: Int -> Expr -> Expr -> Expr
justInto n new v@(Variable i) = if n == i then new else v
justInto n new (Lambda b)     = Lambda $ justInto (n + 1) new b
justInto n new e              = fmap'' (justInto n new) e

into :: Int -> Expr -> Expr -> Expr
into n new v@(Variable i) = if n == i then new else v
into n new (Lambda b)     = Lambda $ into (n + 1) (shift 1 new) b
--into n new (Let l e)      = Let (map (into n new) l) $ into (n + len) (shift (len) new) e where len = length l
--into n new (Counted e)    = into n new e
into n new e              = fmap'' (into n new) e

findF :: String -> [FunDef] -> Maybe FunDef
findF name [] = Nothing
findF name (f@(FunDef fName _):xs) = if name == fName then Just f else findF name xs

goUp :: Int -> Expr -> [Expr] -> [Expr]
goUp i e []                = []
goUp i e (x@(Lambda _):xs) = (into i e x) : goUp (i+1) e xs
goUp i e (x:xs)            = (into i e x) : goUp i e xs

match :: Expr -> [Expr] -> (Pattern, Expr) -> Maybe (Expr, [Expr])
match e1 g (Var, e2)                         = Just (Application e2 e1, g)
--match (Variable i) g (Pattern n j, e2)       = Just $ let new = (Constructor n $ map Variable [0..(j - 1)]) in
--                                                (fmap'' (into i new) e2, goUp i new g)
--match (Variable i) g (Pattern n j, e2)       = Just $ (justInto i (Constructor n $ map Variable [0..(j - 1)]) e2, g)
match (Variable i) g (Pattern n j, e2)       = case j of
                                                0 -> let new = Constructor n []           in Just (into i new e2, goUp i new g)
                                                1 -> let new = Constructor n [Variable i] in Just (into 0 (Variable i) $ into (i + 1) new e2', goUp i new g) where Lambda e2' = e2
                                                --let new = Constructor n [Variable i] in Just (show $ into 0 (Variable i) $ into (i + 1) new e2', goUp i new g)
                                                _ -> error ("to many args in pattern")
match (Constructor n1 p) g (Pattern n2 i, e) = if n1 /= n2 then Nothing else 
                                                if length p /= i then error ("different params number" ++ (show $ (Constructor n1 p)) ++ (show $ (Pattern n2 i, e))) else
                                                    Just $ (foldr (flip Application) e p, g)
match _ g (_, e)                             = Just (e, g)

next :: [Expr] -> Maybe (Expr, [Expr])
next []     = Nothing
next (x:xs) = case x of 
                Counted _ -> fmap (fmap ((:) x)) $ next xs
                e         -> Just (e, empty:xs)

empty  = Variable (-1)

beta e2 e = shift (-1) $ into 0 (shift 1 e2) e

buildExpr :: [FunDef] -> [Expr] -> Expr -> Node' Expr

buildExpr f g h@(Variable _)                  = Node' h g $ case g of
                                                            []     -> Stop
                                                            (x:xs) -> Transient $ buildExpr f xs $ context (Counted h) x

buildExpr f g h@(Lambda e)                    = Node' h g $ case g of
                                                            []     -> case e of
                                                                        Counted _ -> Stop
                                                                        _         -> Transient $ buildExpr f [Lambda empty] $ e --shift (-1) e
                                                            (x@(Application (Variable n) _):xs) | n == (-1) -> Transient $ buildExpr f xs $ context (Counted h) x
                                                            (x:xs) -> case e of
                                                                        Counted _ -> Transient $ buildExpr f xs $ context (Counted h) x
                                                                        _         -> Transient $ buildExpr f [Lambda empty] $ e --shift (-1) e

buildExpr f g h@(Application (Counted e1) e2) = Node' h g $ case e1 of
                                                            Lambda e  -> Transient $ buildExpr f g $ beta e2 e
                                                            Counted _ -> error ("double counted in Application")
                                                            _         -> case e2 of
                                                                            Counted e -> case g of
                                                                                            []     -> Stop
                                                                                            (x:xs) -> Transient $ buildExpr f xs $ context (Counted h) x
                                                                            _         -> Transient $ buildExpr f ((Application (Counted e1) $ empty):g) e2

buildExpr f g h@(Application e1 e2)           = Node' h g $ Transient $ buildExpr f ((Application empty $ e2):g) e1

buildExpr f g h@(Constructor n p)             = Node' h g $ case g of
                                                            [] -> case next p of
                                                                    Nothing     -> Stop
                                                                    Just (e, l) -> Transient $ buildExpr f ((Constructor n l):g) e
                                                            (x@(Case _ _):xs) -> Transient $ buildExpr f xs $ context (Counted h) x
                                                            (x:xs) -> case next p of
                                                                    Nothing     -> Transient $ buildExpr f xs $ context (Counted h) x
                                                                    Just (e, l) -> Transient $ buildExpr f ((Constructor n l):g) e

buildExpr f g h@(Case e p)                    = Node' h g $ case e of 
                                                            (Counted e) -> let res = catMaybes $ map (match e g) p in
                                                                                case length res of
                                                                                    0 -> Stop
                                                                                    1 -> Transient $ buildExpr f (snd $ head res) $ fst $ head res
                                                                                    _ -> Variants $ map (\(x, y) -> buildExpr f y x) res
                                                            _           -> Transient $ buildExpr f ((Case empty p):g) e

buildExpr f g h@(Call n)                      = Node' h g $ Transient $ buildExpr f g $ case findF n f of
                                                                                                Just (FunDef _ e) -> e
                                                                                                _                 -> error "no such function"

buildExpr f g h@(Counted e)                   = buildExpr f g e

buildExpr f g h@(Let e1 e2)                   = Node' h g $ Decompose [buildExpr f g e1, buildExpr f g e2]

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

weakMatch :: Node' Expr -> Node'' Expr -> Maybe Expr
weakMatch (Node' e' g' _) x@(Node'' i e g _) = if e == e' && length g <= length g' && g == take (length g) g'
                                                then let (g'', c) = splitAt (length g) g' in
                                                        Just $ Let (put e g'') $ put (Variable 0) c
                                                else Nothing

dummyMatch :: Node' Expr -> Node'' Expr -> Maybe (Node'' Expr)
dummyMatch (Node' e' g' _) x@(Node'' i e g _) = if e == e' && g == g' then Just x else Nothing


buildGraph :: Int -> [FunDef] -> [Node'' Expr] -> Node' Expr -> Node'' Expr
buildGraph i f ns (Node' e g Stop)             = Node'' i e g Stop
buildGraph i f ns (Node' e g (Transient node)) = case catMaybes $ map (dummyMatch node) ns of
                                                x:xs -> Node'' i e g $ Fold x
                                                []   -> case catMaybes $ map (weakMatch node) ns of
                                                            x:xs -> buildGraph i f ns $ buildExpr f [] x
                                                            []   -> Node'' i e g $ Transient $ buildGraph (i + 1) f (Node'' i e g Stop :ns) node
buildGraph i f ns (Node' e g (Decompose l))    = Node'' i e g $ Decompose $ map (buildGraph (i + 1) f (Node'' i e g Stop :ns)) l
buildGraph i f ns (Node' e g (Variants l))     = Node'' i e g $ Variants $ map (buildGraph (i + 1) f (Node'' i e g Stop :ns)) l

discount :: Expr -> Expr
discount (Counted e)         = discount e
discount e                   = fmap'' discount e

build::Program -> Node' Expr
build (Program l e) = buildExpr l [] e

buildG::Program -> Node'' Expr
buildG p@(Program l e) = buildGraph 0 l [] (build p)

put e []     = e
put e (x:xs) = put (context e x) xs

scope x = (Constructor "Scope" [x])

pretty':: Node' Expr -> Tree String
pretty' (Node' e g Stop)          = Node (show $ put (scope e) g) []
pretty' (Node' e g (Transient n)) = Node (show $ put (scope e) g) [pretty' n]
pretty' (Node' e g (Variants l))  = Node (show $ put (scope e) g) $ map pretty' l
pretty' (Node' e g (Decompose l)) = Node (show $ put (scope e) g) $ map pretty' l

instance Show (Expr) where
    show (Variable n)        = "v" ++ show n
    show (Lambda e)          = "l " ++ show e
    show (Application e1 e2) = "(" ++ show e1 ++ " @ " ++ show e2 ++ ")"
    show (Call n)            = "Call " ++ n
    show (Constructor n l)   = if n == "Scope" then " #< " ++ show (head l) ++ " ># " else n ++ show l
    show (Case e l)          = "Case " ++ show e ++ " of "++ show l
    show (Let l e)           = "Let " ++ show l ++ " in " ++ show e
    show (Counted e)         = "OK (" ++ show e ++ ")"

instance Show (Pattern) where
    show Var           = "v"
    show (Pattern n _) = n

pretty'':: Node'' Expr -> Tree String
pretty'' (Node'' i e g Stop)          = Node (show i ++ " " ++ (show $ put (scope e) g)) []
--pretty'' (Node'' i e g (Transient n)) = Node (show i ++ " " ++ (show $ put (scope e) g)) [pretty'' n]
pretty'' (Node'' i e g (Transient n)) = pretty'' n
pretty'' (Node'' i e g (Variants l))  = Node (show i ++ " CASE " ++ (show $ put (scope e) g)) $ map pretty'' l
pretty'' (Node'' i e g (Decompose l)) = Node (show i ++ " " ++ (show $ put (scope e) g)) $ map pretty'' l
pretty'' (Node'' i e g (Fold l))      = Node (show i ++ " GO " ++ (show $ put (scope e) g) ++ " TO " ++ (show l)) []
