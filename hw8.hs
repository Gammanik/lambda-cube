import Control.Monad (guard)

type Symb = String

infixl 2 :@:
infixr 3 >-> -- теперь просто функция

data Expr = Idx Int          -- переменная как индекс Де Брауна
          | Ast              -- константа, базовый атом для кайндов
          | Box              -- константа высшего уровня
          | Expr :@: Expr    -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr    -- абстракция терма или типа
          | Pi  Decl Expr    -- расширенный функциональный тип
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  Pi d1 u3    == Pi d2 u4    = d1 == d2 && u3 == u4
  _           == _           = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE, pE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
pE v = Pi  . EDecl v

(>->) :: Expr -> Expr -> Expr
a >-> b = pE "_" a (shift 1 b)

----------------------

isSort :: Expr -> Bool
isSort e = e `elem` [Ast, Box]

isNF :: Expr -> Bool
isNF (Lmb (EDecl _ ex) body) = isNF ex && isNF body
isNF x = isNANF x

isNANF :: Expr -> Bool
isNANF (Idx _)   = True
isNANF (a :@: b) = isNANF a && isNF b
isNANF (Pi (EDecl _ a) b) = isNF a   && isNF b
isNANF e         = isSort e

isNA :: Expr -> Bool
isNA (Idx{})    = True
isNA (_ :@: _)  = True
isNA (Pi{})     = True
isNA _          = False

----------------------

validEnv :: Env -> Bool
validEnv [] = True
validEnv ((EDecl _ expr):ctx)
  = maybe False isSort (infer ctx expr) && validEnv ctx


shift :: Int -> Expr -> Expr
shift vg expr = h 0 expr
  where h v Ast             = Ast
        h v Box             = Box
        h v (Idx i) | i < v = Idx $ i
        h v (Idx i)         = Idx $ i + vg
        h v (t1 :@: t2)     = (h v t1) :@: (h v t2)
        h v (Lmb (EDecl n e) t)
            = Lmb (EDecl n $ h v e) $ h (v + 1) t
        h v ((EDecl n t1) `Pi` t2)
          = (EDecl n $ h v t1) `Pi` (h (v + 1) t2)


subst :: Int -> Expr -> Expr -> Expr
subst _ _ Ast = Ast
subst _ _ Box = Box
subst i s (Idx k) | k == i  = s
subst i s (Idx k)           = Idx k
subst i s (t1 :@: t2)       = (subst i s t1) :@: (subst i s t2)
subst i s (Lmb (EDecl n e) t)
  = Lmb (EDecl n $ subst i s e) $ subst (i + 1) (shift 1 s) t
subst i s (Pi (EDecl n t1) t2)
  = Pi (EDecl n $ subst i s t1) $ subst (i + 1) (shift 1 s) t2

(!!?) :: Env -> Int -> Maybe Decl
e !!? i = if (0 <= i && i < length e)
          then Just (e !! i)
          else Nothing

infer :: Env -> Expr -> Maybe Expr
infer env expr | validEnv env = infer' env expr
    where infer' _ Ast = Just Box

          infer' env (Idx i) = do
            (EDecl _ e) <- env !!? i
            return $ shift (i + 1) e

          infer' env (m :@: n) = do
            (Pi (EDecl _ a) b) <- nf <$> infer' env m
            a' <- infer' env n
            guard $ nf a == nf a'
            return $ shift (-1) $ subst 0 (shift 1 n) b

          infer' env (Pi decl@(EDecl x a) b) = do
            Ast <- infer' env a
            s   <- infer' (decl : env) b
            guard $ isSort s
            return $ s

          infer' env (Lmb d@(EDecl x a) m) = do
            Ast <- infer' env a
            b   <- infer (d : env) m
            return $ Pi d b

          infer' _ _ = Nothing
infer env expr = Nothing

infer0 :: Expr -> Maybe Expr
infer0 = infer []



oneStep :: Expr -> Maybe Expr
oneStep (m :@: n) | isNANF m  = do n' <- oneStep n
                                   return $ m  :@: n'
oneStep (m :@: n) | isNA m    = do m' <- oneStep m
                                   return $ m' :@: n

oneStep ((EDecl x a) `Pi` b) | isNF a = do
    b' <- oneStep b
    return $ (EDecl x a) `Pi` b'
oneStep ((EDecl x a) `Pi` b)  = do a' <- oneStep a
                                   return $ (EDecl x a') `Pi` b

oneStep (Lmb (EDecl name a) m) | isNF a = do
     m' <- oneStep m
     return $ Lmb (EDecl name a)  m'
oneStep (Lmb (EDecl name a) m) = do
    a' <- oneStep a
    return $ Lmb (EDecl name a') m

oneStep ((Lmb (EDecl name a) m) :@: n)
  = Just $ shift (-1) $ subst 0 (shift 1 n) m

oneStep _ = Nothing


nf :: Expr -> Expr
nf term | Just term' <- oneStep term = nf term'
        | otherwise                  = term



gamma  = [EDecl "phi" (Idx 0 >-> Ast),EDecl "alpha" Ast]
gamma0 = EDecl "a" (Idx 1) : gamma
test11 = infer gamma0 (lE "x" (Idx 1 :@: Idx 0) (Idx 0)) == Just (Pi (EDecl "x" (Idx 1 :@: Idx 0)) (Idx 2 :@: Idx 1))
test12 = infer gamma (lE "a" (Idx 1) $ lE "x" (Idx 1 :@: Idx 0) (Idx 0)) == Just (Pi (EDecl "a" (Idx 1)) (Pi (EDecl "x" (Idx 1 :@: Idx 0)) (Idx 2 :@: Idx 1)))
