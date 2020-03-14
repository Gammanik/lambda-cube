module Module6 where

type Symb = String

infixl 4 :@:, :@>
infixr 3 :->

data Type = TIdx Int         -- типовой атом как индекс Де Брауна
          | Type :-> Type    -- стрелочный тип
          | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  _           == _           = False

-- Объявление либо переменная, либо тип
data Decl = VDecl Symb Type --  объявление термовой переменной с ее типом, Symb - справочное имя этой переменной
          | TDecl Symb      --  объявление типовой переменной, Symb - справочное имя этой переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  VDecl _ t1 == VDecl _ t2 = t1 == t2
  TDecl _    == TDecl _    = True
  _          == _          = False

type Env = [Decl]

data Term = Idx Int
          | Term :@: Term
          | Term :@> Type
          | Lmb Decl Term
    deriving (Read,Show,Eq,Ord)

lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl

-- Пары ------------------------------------
pF  = lT "sigma" $ lT "tau" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ lT "a" $ lV "f" (TIdx 4 :-> TIdx 3 :-> TIdx 0) $ Idx 0 :@: Idx 3 :@: Idx 2
pFT = ForAll "sigma" $ ForAll "tau" $ TIdx 1 :-> TIdx 0 :-> (ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0)
pT = ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0

fstP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 2 :@: (cKF    :@> TIdx 2 :@> TIdx 1) where
  cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
sndP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 1 :@: (cKastF :@> TIdx 2 :@> TIdx 1) where
  cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

------------------------------------
