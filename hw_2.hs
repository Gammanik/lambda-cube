import Control.Applicative
import Control.Monad


type Symb = String
infixl 4 :@:
infixr 3 :->
infixl 5 :*

data Type = Boo
          | Type :-> Type
          | Type :* Type
    deriving (Read,Show,Eq)


data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)


data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Read,Show)


instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1   =  u == u1 && w == w1
  Fst z     == Fst z1       =  z == z1
  Snd z     == Snd z1       =  z == z1
  _         == _            =  False


newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)


shift :: Int -> Term -> Term
shift n tg = hlp 0 tg
  where hlp v (t1 :@: t2)   = (hlp v t1) :@: (hlp v t2)
        hlp v (Lmb s tp t)  = Lmb s tp (hlp (v + 1) t)
        hlp v (Let s t1 t2) = Let s (hlp v t1) (hlp (v+1) t2)
        hlp v (Idx num) | v <= num = Idx (num + n)
        hlp v (Idx num)     = Idx num
        hlp v (If t1 t2 t3) = If (hlp v t1) (hlp v t2) (hlp v t3)
        hlp v Fls           = Fls
        hlp v Tru           = Tru
        hlp v (Pair t1 t2)  = Pair (hlp v t1) (hlp v t2)
        hlp v (Fst t)       = Fst (hlp v t)
        hlp v (Snd t)       = Snd (hlp v t)


match :: Pat -> Term -> Maybe [(Symb,Term)]
match xg tg = h [] xg tg
  where h l (PVar v) t  | isValue t = Just $ (v, t) : l
        h l (PPair x y) (Pair x' y') = do
                   l1 <- match x x'
                   l2 <- match y y'
                   return (l1 ++ l2)
        h l _ _ = Nothing

substDB :: Int -> Term -> Term -> Term
substDB j st t = h t
  where h (Idx n) | n == j  = st
        h (Idx n)           = Idx n
        h (t1 :@: t2)       = (h t1) :@: (h t2)
        h (Lmb s tp t)      = Lmb s tp (substDB (j + 1) (shift 1 st) t)
        h (Let x t u)       = Let x (h t) (substDB (j + 1) (shift (hlp x) st) u)
          where hlp x' = 1
        h (If t1 t2 t3)     = If (h t1) (h t2) (h t3)
        h Fls               = Fls
        h Tru               = Tru
        h (Pair t1 t2)      = Pair (h t1) (h t2)
        h (Fst t)           = Fst (h t)
        h (Snd t)           = Snd (h t)

--substDB' (Lmb x t u)      = let v = j + 1
--                              in v `seq` Lmb x t $ substDB v (shift 1 s) u
--substDB' (Let x t u)      = let v = j + 1
--                              in v `seq` Let x (substDB' t) $ substDB v (shift 1 s) u

isValue :: Term -> Bool
isValue Fls = True
isValue Tru = True
isValue Lmb{} = True
isValue (Pair x y) = isValue x && isValue y
isValue _ = False

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

oneStep (Let (PVar s) t1 t2) | isValue t1 = Just $ betaRuleDB ((Lmb s Boo t2) :@: t1)
--oneStep (Let p@(PVar s) v t) | isValue v = (match p v) t
oneStep (Let s t1 t2)           = case (oneStep t1) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Let s x t2
oneStep (t1 :@: t2) =  fmap (:@: t2) (oneStep t1)

oneStep (Fst (Pair t1 t2)) | isValue t1 && isValue t2   = Just t1
oneStep (Fst x)      = Fst <$> oneStep x
oneStep (Snd (Pair t1 t2)) | isValue t1 && isValue t2  = Just t2
oneStep (Snd x)      = Snd <$> oneStep x
oneStep (Pair t1 t2) | isValue t1 = case (oneStep t2) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Pair t1 x

oneStep (Pair x y) = flip Pair y <$> oneStep x

oneStep _ = Nothing


whnf :: Term -> Term
whnf u = case (oneStep u) of
  Nothing -> u
  Just x -> (whnf x)
