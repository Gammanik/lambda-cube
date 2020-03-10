import Control.Applicative


type Symb = String

infixl 4 :@:, :@>
infixr 3 :->
infix 1 ||-

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
------------------------------------



validEnv :: Env -> Bool
validEnv []               = True
validEnv ((TDecl{}):ds)   = validEnv ds
validEnv ((VDecl _ t):ds) = (ds ||- t) && (validEnv ds)


(||-) :: Env -> Type -> Bool
e ||- (TIdx i) = if i < length e then
              (case (e !! i) of
                  (TDecl{}) -> True
                  _ -> False)
              else False
e ||- (t :-> t')    = (e ||- t) && (e ||- t')
e ||- (ForAll s t) = (TDecl s : e) ||- t


--t1 = True  == validEnv [VDecl "x" tArr, TDecl "a"]
--t2 = False == validEnv [TDecl "a", VDecl "x" tArr]
--t3 = False == ([] ||- TIdx 0 :-> TIdx 0)
--t4 = True  == ([TDecl "a"] ||- TIdx 0 :-> TIdx 0)
--t5 = True  == ([] ||- ForAll "a" (TIdx 0 :-> TIdx 0))







shiftT :: Int -> Type -> Type
shiftT n tg = h 0 tg
  where h v (TIdx i) | v <= i = TIdx $ i + n
        h v (TIdx i)          = TIdx $ i
        h v (t :-> t')        = h v t :-> h v t'
        h v (ForAll s t)      = ForAll s $ h (v + 1) t



substTT :: Int -> Type -> Type -> Type
substTT j s (TIdx i) | i == j = s
substTT j s t@(TIdx i)        = t
substTT j s (tl :-> tr)  = substTT j s tl :-> substTT j s tr
substTT j s (ForAll s' t) = ForAll s' $ substTT (j + 1) (shiftT 1 s) t

shiftV :: Int -> Term -> Term
shiftV val = h 0 where
  h v (Idx i)      = Idx $ if v <= i then i + val else i
  h v (tl :@: tr)  = h v tl :@: h v tr
  h v (tl :@> ty)  = h v tl :@> h' v ty
  h v (Lmb d@(TDecl idx) t) = Lmb d $ h (v + 1) t
  h v (Lmb (VDecl x ty) t)  = Lmb (VDecl x $ h' v ty) (h (v + 1) t)

  h' v' (TIdx i) | v' <= i = TIdx $ i + val
  h' v' (TIdx i)          = TIdx $ i
  h' v' (t :-> t')        = h' v' t :-> h' v' t'
  h' v' (ForAll s t)      = ForAll s $ h' (v' + 1) t






--t1 = (infer0 sa0 == Just (ForAll "a" (TIdx 0) :-> ForAll "b" (TIdx 0)))
--t2 = (infer0 sa1 == Just (ForAll "a" (TIdx 0 :-> TIdx 0) :-> ForAll "b" (TIdx 0 :-> TIdx 0)))
--t3 = (infer0 sa2 == Just (ForAll "a" (TIdx 0 :-> TIdx 0) :-> ForAll "a" (TIdx 0 :-> TIdx 0)))






-- типовой индекс в типе ссылается на номер объемлющего ForAll
botF = ForAll "a" (TIdx 0)
tArr  = TIdx 0 :-> TIdx 0
topF = ForAll "a" tArr
-- Кодирование самоприменения в System F (примеры из лекции)
sa0 = lV "z" botF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa1 = lV "z" topF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa2 = lV "z" topF $ Idx 0 :@> topF :@: Idx 0

-- Комбинатор $I$ (TIdx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lV "x" (TIdx 0) $ Idx 0
cIF = lT "a" $ lV "x" (TIdx 0) $ Idx 0

-- Комбинаторы $K$ и $K_\ast$
tK    = TIdx 1 :-> TIdx 0 :-> TIdx 1
tKF = ForAll "a" $ ForAll "b" tK
cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
tKast = TIdx 1 :-> TIdx 0 :-> TIdx 0
tKastF = ForAll "a" $ ForAll "b" tKast
cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

-- Комбинатор $C$
tFlip = (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 1 :-> TIdx 2 :-> TIdx 0
tFlipF = ForAll "a" $ ForAll "b" $ ForAll "c" $ tFlip
cFlipF = lT "a" $ lT "b" $ lT "c" $ lV "f" (TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lV "y" (TIdx 2) $ lV "x" (TIdx 4) $ Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование булевых значений в System F
boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0
fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0
tru = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 1

ifThenElse = lT "a" $ lV "v" boolT $ lV "x" (TIdx 1) $ lV "y" (TIdx 2) $ Idx 2 :@> TIdx 3 :@: Idx 1 :@: Idx 0
notF = lV "v" boolT $ lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 3 :@> TIdx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" $ (TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0
natAbs body = lT "a" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) body
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