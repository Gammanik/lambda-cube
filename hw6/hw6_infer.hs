import Control.Applicative ((<|>))
import Control.Monad (guard)


type Symb = String

infixl 2 :@:, :@>
infixr 3 :->

data Type = TIdx Int         -- типовой атом как индекс Де Брауна
          | Type :-> Type    -- стрелочный тип
          | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
          | Exists Symb Type -- экзистенциальный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  Exists _ t1 == Exists _ t2 = t1 == t2
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
          | As (Type,Term) Type       -- упаковка типа-свидетеля и терма в экзистенциальный тип
          | Let (Symb,Symb) Term Term -- распаковка пакета, имена типа и терма в паре - справочные
    deriving (Read,Show,Eq,Ord)




lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl


validEnv :: Env -> Bool
validEnv                  [] = True
validEnv ((TDecl _  ):decls) = validEnv decls
validEnv ((VDecl _ t):decls) = (decls ||- t) && (validEnv decls)


(||-) :: Env -> Type -> Bool
e ||- (TIdx i) = if i < length e && i > 0 then
              (case (e !! i) of
                  (TDecl{}) -> True
                  _ -> False)
              else False
e ||- (t :-> t')    = (e ||- t) && (e ||- t')
e ||- (ForAll s t) = (TDecl s : e) ||- t
e ||- (Exists s t) = (TDecl s : e) ||- t



shiftT :: Int -> Type -> Type
shiftT n tg = h 0 tg
  where h v (TIdx i) | v <= i = TIdx $ i + n
        h v (TIdx i)          = TIdx $ i
        h v (t :-> t')        = h v t :-> h v t'
        h v (ForAll s t)      = ForAll s $ h (v + 1) t
        h v (Exists s t)      = Exists s $ h (v + 1) t



substTT :: Int -> Type -> Type -> Type
substTT j s (TIdx i) | i == j = s
substTT j s t@(TIdx i)        = t
substTT j s (tl :-> tr)       = substTT j s tl :-> substTT j s tr
substTT j s (ForAll s' t)     = ForAll s' $ substTT (j + 1) (shiftT 1 s) t
substTT j s (Exists s' t)     = Exists s' $ substTT (j + 1) (shiftT 1 s) t




(!!?) :: Env -> Int -> Maybe Decl
e !!? i = if (0 <= i && i < length e && validEnv e)
          then Just (e !! i)
          else Nothing

getT :: (Maybe Type) -> Type
getT (Just t) = t


infer :: Env -> Term -> Maybe Type
infer e (Idx i)
  | 0 <= i && i < length e = do
    (VDecl _ sigma) <- e !!? i
    return $ shiftT (i + 1) sigma

infer e (t1 :@: t2) = do
  (s :-> t) <- infer e t1
  s'           <- infer e t2
  guard $ s == s'
  return $ t

infer e (Lmb var@(VDecl x t) t') = do
  guard $ e ||- t
  tau <- infer (var:e) t'
  return $ t :-> (shiftT (-1) tau)

infer e (t :@> t') = do
  guard $ e ||- t'
  (ForAll a s) <- infer e t
  return $ shiftT (-1) $ substTT 0 (shiftT 1 t') s

infer e (Lmb ty@(TDecl a) t) = do
  s <- infer (ty:e) t
  return $ ForAll a s

infer e (Let (a, x) t1 t2) = do
  (Exists _ s) <- infer e t1
  tau <- infer (VDecl x s : TDecl a : e) t2
  let result = shiftT (-2) tau
  guard $ e ||- result
  return $ result

infer e (As (tau, t) ex@(Exists a s)) = do
  t1 <- Just (shiftT (-1) $ substTT 0 (shiftT 1 tau) s)
  t2 <- infer e t
  guard $ t1 == t2
  return $ ex

infer _ _ = Nothing

infer0 :: Term -> Maybe Type
infer0 = infer []







shiftV :: Int -> Term -> Term
shiftV val = h 0 where
  h v (Idx i)      = Idx $ if v <= i then i + val else i
  h v (tl :@: tr)  = h v tl :@: h v tr
  h v (tl :@> ty)  = h v tl :@> h' v ty
  h v (Lmb d@(TDecl idx) t) = Lmb d $ h (v + 1) t
  h v (Lmb (VDecl x ty) t)  = Lmb (VDecl x $ h' v ty) (h (v + 1) t)

  h v (As (ty, t) s)    = (h' v ty, h v t) `As` (h' v s)
  h lvl (Let sp t1 t2)  = Let sp (h lvl t1) (h (lvl + 2) t2)

  h' v' (TIdx i) | v' <= i = TIdx $ i + val
  h' v' (TIdx i)          = TIdx $ i
  h' v' (t :-> t')        = h' v' t :-> h' v' t'
  h' v' (ForAll s t)      = ForAll s $ h' (v' + 1) t
  h' v' (Exists s t)      = Exists s $ h' (v' + 1) t



substVV :: Int -> Term -> Term -> Term
substVV v s (Idx i) | i == v  = s
substVV v s u@(Idx i)         = u
substVV v s (t1 :@: t2)       = substVV v s t1 :@: substVV v s t2
substVV v s (t1 :@> ty)       = substVV v s t1 :@> ty
substVV v s (Lmb d t)         = Lmb d $ substVV (v + 1) (shiftV 1 s) t
substVV v s (As (ty, t) sg)   = (ty, substVV v s t) `As` sg
substVV v s (Let d t1 t2)     =
  Let d (substVV v s t1) (substVV (v + 2) (shiftV 2 s) t2)




substTV :: Int -> Type -> Term -> Term
substTV _ _   u@(Idx _)            = u
substTV i ta (t1 :@: t2)          = substTV i ta t1 :@: substTV i ta t2
substTV i ta (t1 :@> ty)          = substTV i ta t1 :@> substTT i ta ty
substTV i ta (Lmb (VDecl x ty) t) = Lmb (VDecl x $ substTT i ta ty) (substTV (i + 1) (shiftT 1 ta) t)
substTV i ta (Lmb decl t)         = Lmb decl $ substTV (i + 1) (shiftT 1 ta) t
substTV i ta (As (ty, t) sg)      = (substTT i ta ty, substTV i ta t) `As` (substTT i ta sg)
substTV i ta (Let def t1 t2)      = Let def (substTV i ta t1) (substTV (i + 2) (shiftT 2 ta) t2)



isNF :: Term -> Bool
isNF (Lmb _ t) = isNF t
isNF (As (_, t)  _) = isNF t
isNF (Idx _) = True
isNF (t1 :@: t2) = isNF t1 && isNF t2
isNF (t1 :@> t2) = isNF t1
isNF _ = False


oneStep :: Term -> Maybe Term
oneStep (Lmb d t)               = Lmb d <$> oneStep t
oneStep (Lmb (VDecl{}) t :@: s) = Just $ shiftV (-1) $ substVV 0 (shiftV 1 s) t
oneStep (Lmb (TDecl{}) t :@> s) = Just $ shiftV (-1) $ substTV 0 (shiftT 1 s) t
oneStep (tl :@: tr)             = (:@: tr) <$> oneStep tl <|> (tl :@:) <$> oneStep tr
oneStep (tl :@> tr)             = (:@> tr) <$> oneStep tl

oneStep (As (ty, t) sigma)      = (\t' -> (ty, t') `As` sigma) <$> oneStep t
oneStep (Let _ ((ty, t) `As` _) t2) | isNF t
  = Just $ shiftV (-1) $ substTV 0 (shiftT 1 ty) $
    shiftV (-1) $ substVV 0 (shiftV 2 t) $ t2
oneStep (Let def t1 t2)           = (\t' -> Let def t' t2) <$> oneStep t1

oneStep _                       = Nothing


nf :: Term -> Term
nf u = case (oneStep u) of
  Nothing -> u
  Just x -> (nf x)

