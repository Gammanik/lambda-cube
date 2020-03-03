import Control.Applicative
import Control.Monad
import Data.List (findIndex)


type Symb = String
infixl 4 :@: 
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)] 
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PRcd [(Symb,Pat)] 
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb,Term)]
          | Prj Symb Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Rcd xs    == Rcd xs1      =  xs == xs1
  Prj l u   == Prj l1 u1    =  l == l1 && u == u1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)
------------------------------------

shift :: Int -> Term -> Term
shift n tg = hlp 0 tg
  where hlp v Fls           = Fls
        hlp v Tru           = Tru
        hlp v (If t1 t2 t3) = If (hlp v t1) (hlp v t2) (hlp v t3)
        hlp v (t1 :@: t2)   = (hlp v t1) :@: (hlp v t2)
        hlp v (Idx num) | v <= num = Idx (num + n)
        hlp v (Idx num)     = Idx num
        hlp v (Lmb s tp t)  = Lmb s tp (hlp (v + 1) t)
        hlp v (Let p t1 t2) = Let p (hlp v t1) (hlp (v + getSize p) t2)
          where getSize (PVar v) = 1
                getSize (PRcd ((s,p):ps)) = getSize p + getSize (PRcd ps)

        hlp v (Rcd ts)      = Rcd $ fmap (hlp v) <$> ts
        hlp v (Prj s t)     = Prj s $ (hlp v t)
--        hlp v (Rcd ((s,t):ts)) = Rcd $ [(s, hlp v t)] ++ (h' (v + 1) (Rcd ts))
--          where h' v' (Rcd []) = []
--                h' v' (Rcd ((s',t'): ts')) = [(s',t')] ++ (h' (v' + 1) ts')




substDB :: Int -> Term -> Term -> Term
substDB j st t = h t
  where h Fls               = Fls
        h Tru               = Tru
        h (If t1 t2 t3)     = If (h t1) (h t2) (h t3)
        h (Idx n) | n == j  = st
        h (Idx n)           = Idx n
        h (t1 :@: t2)       = (h t1) :@: (h t2)
        h (Lmb s tp t)      = Lmb s tp (substDB (j + 1) (shift 1 st) t)
        h (Let p t u)       = Let p (h t) $ substDB (j + getSize p) (shift (getSize p) st) u
          where getSize (PVar v) = 1
                getSize (PRcd ((s,p):ps)) = getSize p + getSize (PRcd ps)

        h (Rcd l)           = Rcd $ fmap h <$> l
        h (Prj s t)     = Prj s $ (h t)
        --h t                = t



isValue :: Term -> Bool
isValue Fls   = True
isValue Tru   = True
isValue Lmb{} = True
isValue (Rcd ((s,v):vs)) = isValue v && isValue (Rcd vs)
isValue _     = False


match :: Pat -> Term -> Maybe [(Symb,Term)]
match xg tg = h [] xg tg
  where h l (PVar v) t  | isValue t     = Just $ (v, t) : l
        h l (PRcd []) (Rcd []) = Just []
        h l (PRcd ((s,p):ps)) (Rcd ((s',v):vs)) | isValue v = do
            l1 <- match p v
            l2 <- match (PRcd ps) (Rcd vs)
            guard $ s == s'
            return (l1 ++ l2)
        h l _ _ = Nothing




betaRuleDB :: Term -> Term
betaRuleDB (Lmb s tp t :@: t1) = shift (-1) (substDB 0 (shift 1 t1) t)



oneStep :: Term -> Maybe Term
oneStep (If Tru t1 t2)          = Just t1
oneStep (If Fls t1 t2)          = Just t2
oneStep (If tb t1 t2)           = case (oneStep tb) of
                                  Nothing -> Nothing
                                  Just x -> Just $ If x t1 t2

oneStep t@((Lmb s tp t1) :@: x) | isValue x = Just $ betaRuleDB t
oneStep t@((Lmb s tp t1) :@: x) = case (oneStep x) of
                                  Nothing -> Nothing
                                  Just x1 -> Just $ Lmb s tp t1 :@: x1

oneStep tr@(Let p v t) | isValue v = makeMatch t <$> match p v
  where makeMatch = foldr (\(s,v) t -> shift (-1) $ substDB 0 (shift 1 v) t)
oneStep (Let s t1 t2)           = case (oneStep t1) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Let s x t2

oneStep (t1 :@: t2)             =  fmap (:@: t2) (oneStep t1)

oneStep (Rcd [])                = Nothing
--oneStep (Rcd ((s, t):l))  = case (oneStep t) of
--                                  Nothing -> Just $ Rcd $ (s,t): (h $ oneStep $ Rcd l)
--                                    where h (Just (Rcd x))  = x
--                                          h (Nothing)       = []
--                                  Just x -> Just $ Rcd $ (s, x):l


oneStep t@(Rcd kvs) = do
  firstNonValue <- findIndex (not . isValue . snd) kvs
  let (vs, nvs)  = splitAt (firstNonValue) kvs
  nvs' <- patch nvs
  return $ Rcd (vs ++ nvs')
  where
    patch []         = Nothing
    patch ((s,t):ts) = oneStep t >>= \t' -> Just ((s, t') : ts)


oneStep (Prj s t)               = case (oneStep t) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Prj s x

oneStep _ = Nothing




whnf :: Term -> Term
whnf u = case (oneStep u) of
  Nothing -> u
  Just x -> (whnf x)