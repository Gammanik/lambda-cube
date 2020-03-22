import Data.Maybe (maybe)
import Control.Applicative ((<|>))
import Control.Monad (guard)


type Symb = String

infixl 2 :@:
infixr 3 :->

data Expr = Idx Int          -- переменная как индекс Де Брауна
          | Ast              -- константа, базовый атом для кайндов
          | Box              -- константа высшего уровня
          | Expr :@: Expr    -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr    -- абстракция терма или типа
          | Expr :-> Expr    -- стрелочный тип или кайнд
          | ForAll Symb Expr Expr -- полиморфный тип, второй аргумент - кайнд типовой переменной
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ s1 t3 == ForAll _ s2 t4 = s1 == s2 && t3 == t4
  _           == _           = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
----------------------


isNF :: Expr -> Bool
isNF (Lmb (EDecl _ ex) body) = isNF ex && isNF body
isNF x = isNANF x

isSort :: Expr -> Bool
isSort e = e `elem` [Ast, Box]

isNANF :: Expr -> Bool
isNANF (Idx _)   = True
isNANF (a :@: b) = isNANF a && isNF b
isNANF (a :-> b) = isNF a   && isNF b
isNANF (ForAll _ ty t) = isNF ty && isNF t
isNANF e         = isSort e

isNA :: Expr -> Bool
isNA (Idx _)   = True
isNA (_ :@: _) = True
isNA (_ :-> _) = True
isNA (ForAll _ _ _) = True
isNA _         = False

validEnv :: Env -> Bool
validEnv [] = True
validEnv ((EDecl _ e):c) = maybe False isSort (infer c e) && (validEnv c)


shift :: Int -> Expr -> Expr
shift vg expr = h 0 expr
  where h v Ast             = Ast
        h v Box             = Box
        h v (Idx i) | i < v = Idx $ i
        h v (Idx i)         = Idx $ i + vg
        h v (t1 :@: t2)     = (h v t1) :@: (h v t2)
        h v (t1 :-> t2)     = (h v t1) :-> (h v t2)
        h v (Lmb (EDecl n e) t)
            = Lmb (EDecl n $ h v e) $ h (v + 1) t
        h v (ForAll n ty b)
            = ForAll n (h v ty) (h (v + 1) b)


subst :: Int -> Expr -> Expr -> Expr
subst _ _ Ast = Ast
subst _ _ Box = Box
subst j s (Idx k) | k == j  = s
subst j s (Idx k)           = Idx k
subst j s (t1 :@: t2)       = (subst j s t1) :@: (subst j s t2)
subst j s (t1 :-> t2)       = (subst j s t1) :-> (subst j s t2)
subst j s (Lmb (EDecl n e) t)
  = Lmb (EDecl n $ subst j s e) $ subst (j + 1) (shift 1 s) t
subst j s (ForAll n ty b)
  = ForAll n (subst j s ty) $ subst (j + 1) (shift 1 s) b


(!!?) :: Env -> Int -> Maybe Decl
e !!? i = if (0 <= i && i < length e && validEnv e)
          then Just (e !! i)
          else Nothing

infer :: Env -> Expr -> Maybe Expr
infer env expr | validEnv env = infer' env expr
    where infer' _ Ast = Just Box
          infer' env (Idx i) = do
            (EDecl _ e) <- env !!? i
            return $ shift (i + 1) e

          infer' env (ForAll name s b) = do
            Box <- infer' env s
            Ast <- infer (EDecl name s : env) b
            return $ Ast


          infer' env (t1 :-> t2) = do
              s1 <- infer' env t1
              s2 <- infer' env t2
              guard $ s1 == s2 && s1 `elem` [Ast, Box]
              return s1

          infer' env (m :@: n) = do
            e <- nf <$> infer' env m
            a' <- infer' env n
            case e of
                (a :-> b) -> do
                    guard $ nf a == nf a'
                    return $ b
                (ForAll x s b) -> do
                    guard $ nf a' == nf s
                    return $ shift (-1) $ subst 0 (shift 1 n) b
                _ -> Nothing

          infer' env (Lmb (EDecl x a) m) = do
            b    <- infer (EDecl x a : env) m
            case (isSort <$> infer (EDecl x a : env) (shift 1 a :-> b)) of
                Just True -> return $ a :-> shift (-1) b
                _ -> do
                    Ast <- infer' env (ForAll x (shift 1 a) b)
                    return $ ForAll x a b

          infer' _ _ = Nothing
infer env expr = Nothing

infer0 :: Expr -> Maybe Expr
infer0 = infer []



oneStep :: Expr -> Maybe Expr
oneStep (m :@: n) | isNANF m  = do n' <- oneStep n
                                   return $ m  :@: n'
oneStep (m :@: n) | isNA m    = do m' <- oneStep m
                                   return $ m' :@: n

oneStep (a :-> b) = case (oneStep a) of
                (Just a') -> Just $ a' :-> b
                Nothing -> case (oneStep b) of
                    (Just b') -> Just $ a  :-> b'
                    Nothing -> Nothing

oneStep (Lmb (EDecl name a) m) | isNF a = do
     m' <- oneStep m
     return $ Lmb (EDecl name a)  m'
oneStep (Lmb (EDecl name a) m) = do
    a' <- oneStep a
    return $ Lmb (EDecl name a') m
oneStep ((Lmb (EDecl name a) m) :@: n)
  = Just $ shift (-1) $ subst 0 (shift 1 n) m

oneStep (ForAll name s b) = do
    guard $ isSort s
    b' <- oneStep b
    return $ ForAll name s b'

oneStep _ = Nothing



nf :: Expr -> Expr
nf term | Just term' <- oneStep term = nf term'
        | otherwise                  = term





test21 = Just (ForAll "a" Ast (Idx 0 :-> Idx 0)) == infer0 (lE "a" Ast $ lE "z" (Idx 0) $ Idx 0)
listNatT = nf $ tListFo :@: natT
test22 = (nf <$> infer0 (nilFo :@: natT)) == Just listNatT
test23 = (nf <$> infer0 (consFo :@: natT)) == Just (natT :-> listNatT :-> listNatT)
list12 = consFo :@: natT :@: one :@: (consFo :@: natT :@: two :@: (nilFo :@: natT))
test24 = (nf <$> infer0 list12) == Just listNatT


cD = lE "beta" Ast (Idx 0 :-> Idx 0)
test11 = infer0 cD
test12 = infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0) == Just ((cD :@: Idx 0) :-> (cD :@: Idx 0))
test13 = (nf <$> infer [EDecl "alpha" Ast] (lE "x" (cD :@: Idx 0) $ Idx 0)) == (nf <$> Just (cD :@: (cD :@: Idx 0)))
test14 = infer0 (lE "a" Ast $ lE "z" (Idx 0) $ Idx 0)





---------------------

-- Кодирование булевых значений в System F
boolT = ForAll "a" Ast $ Idx 0 :-> Idx 0 :-> Idx 0
fls = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 0
tru = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 1

ifThenElse = lE "a" Ast $ lE "v" boolT $ lE "x" (Idx 1) $ lE "y" (Idx 2) $ Idx 2 :@: Idx 3 :@: Idx 1 :@: Idx 0
notF = lE "v" boolT $ lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 3 :@: Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" Ast $ (Idx 0 :-> Idx 0) :-> Idx 0 :-> Idx 0
natAbs body = lE "a" Ast $ lE "s" (Idx 0 :-> Idx 0) $ lE "z" (Idx 1) body
zero  = natAbs $ Idx 0
one   = natAbs $ Idx 1 :@: Idx 0
two   = natAbs $ Idx 1 :@: (Idx 1 :@: Idx 0)
three = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))
four  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))
five  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))
six   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))
seven = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))
eight = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))
nine  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))))
ten   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))))

-- Кодирование списков в System F omega
tListFo = lE "sigma" Ast $ ForAll "alpha" Ast $ (Idx 1 :-> Idx 0 :-> Idx 0) :-> Idx 0 :-> Idx 0

nilFo = lE "sigma" Ast
      $ lE "alpha" Ast
      $ lE "c" (Idx 1 :-> Idx 0 :-> Idx 0)
      $ lE "n" (Idx 1)
      $ (Idx 0)

consFo = lE "sigma" Ast
       $ lE "e" (Idx 0)
       $ lE "l" (tListFo :@: Idx 1)
       $ lE "alpha" Ast
       $ lE "c" (Idx 3 :-> Idx 0 :-> Idx 0)
       $ lE "n" (Idx 1)
       $ Idx 1 :@: Idx 4 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)
---------------------