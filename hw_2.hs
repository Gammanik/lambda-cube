import Control.Applicative
import Control.Monad


type Symb = String
infixl 4 :@:
infixr 3 :->
infixl 5 :*
infixl 4 :+

data Type = Boo
          | Nat
          | Type :-> Type
          | Type :* Type
          | Type :+ Type  -- !!
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          | Fix Term
          | Inl Term Type              -- !!
          | Inr Type Term              -- !!
          | Case Term Symb Term Term   -- !!
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls                 =  True
  Tru       == Tru                 =  True
  If b u w  == If b1 u1 w1         =  b == b1 && u == u1 && w == w1
  Zero      == Zero                =  True
  Succ u    == Succ u1             =  u == u1
  Pred u    == Pred u1             =  u == u1
  IsZero u  == IsZero u1           =  u == u1
  Idx m     == Idx m1              =  m == m1
  (u:@:w)   == (u1:@:w1)           =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1         =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1        =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1          =  u == u1 && w == w1
  Fst z     == Fst z1              =  z == z1
  Snd z     == Snd z1              =  z == z1
  Fix u     == Fix u1              =  u == u1
  Inl u t   == Inl u1 t1           =  u == u1 &&  t == t1           -- !
  Inr t u   == Inr t1 u1           =  t == t1 && u == u1            -- !
  Case u _ t s == Case u1 _ t1 s1  =  u == u1 && t == t1 && s == s1 -- !
  _         == _                   =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)


shift :: Int -> Term -> Term
shift n tg = hlp 0 tg
  where hlp v (t1 :@: t2)   = (hlp v t1) :@: (hlp v t2)
        hlp v (Lmb s tp t)  = Lmb s tp (hlp (v + 1) t)
        hlp v (Let p t1 t2) = Let p (hlp v t1) (hlp (v + getSize p) t2)
          where getSize (PVar v) = 1
                getSize (PPair p1 p2) = getSize p1 + getSize p2
        hlp v (Idx num) | v <= num = Idx (num + n)
        hlp v (Idx num)     = Idx num
        hlp v (If t1 t2 t3) = If (hlp v t1) (hlp v t2) (hlp v t3)
        hlp v Fls           = Fls
        hlp v Tru           = Tru
        hlp v (Pair t1 t2)  = Pair (hlp v t1) (hlp v t2)
        hlp v (Fst t)       = Fst (hlp v t)
        hlp v (Snd t)       = Snd (hlp v t)
        hlp v (IsZero n)    = IsZero $ hlp v n
        hlp v (Succ n)      = Succ $ hlp v n
        hlp v (Pred n)      = Pred $ hlp v n
        hlp v (Fix n)       = Fix $ hlp v n
        hlp _ t             = t


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
        h (Let p t u)       = Let p (h t) $ substDB (j + getSize p) (shift (getSize p) st) u
          where getSize (PVar v) = 1
                getSize (PPair p1 p2) = getSize p1 + getSize p2
        h (If t1 t2 t3)     = If (h t1) (h t2) (h t3)
        h Fls               = Fls
        h Tru               = Tru
        h (Pair t1 t2)      = Pair (h t1) (h t2)
        h (Fst t)           = Fst (h t)
        h (Snd t)           = Snd (h t)
        h (IsZero n)       = IsZero $ h n
        h (Succ n)          = Succ $ h n
        h (Pred n)         = Pred $ h n
        h (Fix n)          = Fix $ h n
        h t                = t



isNV :: Term -> Bool
isNV Zero     = True
isNV (Succ x) = isNV x
isNV _        = False

isValue :: Term -> Bool
isValue Fls   = True
isValue Tru   = True
isValue Lmb{} = True
isValue (Pair x y) = isValue x && isValue y
isValue t = isNV t


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
  -- makeMatch :: Term -> [(Symb,Term)] -> Term
  where makeMatch = foldr (\(s,v) t -> shift (-1) $ substDB 0 (shift 1 v) t)
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


oneStep (Pred Zero)               = Just Zero
oneStep (Pred (Succ n)) | isNV n  = Just n

oneStep (Succ t)                  = case (oneStep t) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Succ x
oneStep (Pred t)                  = case (oneStep t) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Pred x

oneStep (IsZero Zero)             = Just Tru
oneStep (IsZero (Succ n)) | isNV n  = Just Fls
oneStep (IsZero t)                = case (oneStep t) of
                                  Nothing -> Nothing
                                  Just x -> Just $ IsZero x

oneStep (Fix l@(Lmb _ _ u)) = Just $ substDB 0 (Fix l) u
oneStep (Fix t)                = case (oneStep t) of
                                  Nothing -> Nothing
                                  Just x -> Just $ Fix x
oneStep _ = Nothing


whnf :: Term -> Term
whnf u = case (oneStep u) of
  Nothing -> u
  Just x -> (whnf x)
