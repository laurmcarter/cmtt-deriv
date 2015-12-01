{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Data.Derivation where

import Data.Void
import Unsafe.Coerce
import GHC.Exts (Constraint)
import Data.Proxy
import Data.List (intercalate,intersperse)
import Debug.Trace

-- Drv {{{

data D (r :: [([([k],k)],[k],k)] -> [([k],k)] -> [k] -> k -> *)
  :: ([([k],k)] -> [k] -> k -> *)
  ->  [([k],k)] -> [k] -> k -> * where
  (:$) :: !(r cs bs as a) -> !(Args d cs) -> D r d bs as a
infixl 1 :$

newtype Derivation r bs as a = D
  { drv3 :: D r (Derivation r) bs as a
  }

induction :: (forall ys xs x. D r p ys xs x -> p ys xs x)
  -> Derivation r bs as a -> p bs as a
induction f (D (r :$ subs)) = f $ r :$ subs'
  where
  subs' = mapArgs (induction f) subs

($$) :: r cs bs as a -> Args (Derivation r) cs -> Derivation r bs as a
($$) r = D . (r :$)
infixl 2 $$

base :: r Ø bs as a -> Derivation r bs as a
base = ($$ Ø)

-- }}}

-- Args {{{

data Args (d :: [([k],k)] -> [k] -> k -> *) :: [([([k],k)],[k],k)] -> * where
  Ø    :: Args d Ø
  (:*) :: !(d bs as a)
       -> !(Args d xs)
       -> Args d (T3 bs as a :< xs)
infixr 5 :*

pattern Nil :: Args (d :: [([k],k)] -> [k] -> k -> *) Ø
pattern Nil = Ø

mapArgs :: (forall ys xs x. d1 ys xs x -> d2 ys xs x)
        -> Args d1 as -> Args d2 as
mapArgs f = \case
  Ø       -> Ø
  a :* as -> f a :* mapArgs f as

-- }}}

-- Env {{{

data Env (f :: k -> *) :: [k] -> * where
  Empty :: Env f Ø
  (:&)  :: !(f a)
        -> !(Env f as)
        -> Env f (a :< as)
infixr 5 :&

headEnv :: Env f (a :< as) -> f a
headEnv (a :& _) = a

tailEnv :: Env f (a :< as) -> Env f as
tailEnv (_ :& as) = as

indexEnv :: Index as a -> Env f as -> f a
indexEnv = \case
  Z_   -> headEnv
  S_ x -> indexEnv x . tailEnv

mapEnv :: (forall x. f x -> g x) -> Env f as -> Env g as
mapEnv f = \case
  Empty   -> Empty
  a :& as -> f a :& mapEnv f as

-- }}}

-- Context {{{

data Context (f :: k -> *) (c :: [k] -> k -> k) :: [([k],k)] -> * where
  EmptyC :: Context f c Ø
  (:&&)  :: !(f (c as a))
         -> !(Context f c ps)
         -> Context f c (as # a :< ps)
infixr 5 :&&

headContext :: Context f c (p :< bs) -> f (c (Fst p) (Snd p))
headContext (a :&& _) = a

tailContext :: Context f c (p :< bs) -> Context f c bs
tailContext (_ :&& as) = as

indexContext :: Index bs p -> Context f c bs -> f (c (Fst p) (Snd p))
indexContext = \case
  Z_   -> headContext
  S_ x -> indexContext x . tailContext

-- }}}

-- T {{{

data Ty
  = O
  | N
  | Ty :-> Ty
  | Ctx [Ty] Ty
  deriving (Eq,Ord,Show)
infixr 3 :->

type Box = Ctx Ø

data T :: Ty -> * where
  TruthT :: T O
  NatT   :: T N
  ArrT   :: !(T a)
         -> !(T b)
         -> T (a :-> b)
  CtxT   :: !(Env T as)
         -> !(T a)
         -> T (Ctx as a)

instance Show (T a) where
  showsPrec d = \case
    TruthT    -> showString "o"
    NatT      -> showString "Nat"
    ArrT a b  -> showParen (d > 0)
      $ showsPrec 1 a
      . showString " -> "
      . showsPrec 0 b
    CtxT as a ->
        showString "["
      . foldl (.) id ss
      . showString "]"
      . showsPrec 11 a
      where
      ss = intersperse (showString ",") $ toList shows as

-- }}}

-- Addtl Types,Families {{{

type Ø    = '[]
type (:<) = '(:)
infixr 5 :<
type (#) = '(,)
infixr 6 #
type T2   = '(,)
type T3   = '(,,)

data Index :: [k] -> k -> * where
  Z_ :: Index (a :< as) a
  S_ :: !(Index as a)
     -> Index (b :< as) a

deriving instance Eq   (Index as a)
deriving instance Ord  (Index as a)
deriving instance Show (Index as a)

type a ∈ as = Index as a
infix 2 ∈

type family (f :: k -> l) <$> (as :: [k]) :: [l] where
  f <$>  Ø        = Ø
  f <$> (a :< as) = f a :< (f <$> as)
infixr 4 <$>

type family Fst (p :: (k,l)) :: k where
  Fst (a#b) = a

type family Snd (p :: (k,l)) :: l where
  Snd (a#b) = b

-- }}}

-- Rules {{{

data Ctxl (c :: Ty -> *) :: [([([Ty],Ty)],[Ty],Ty)] -> [([Ty],Ty)] -> [Ty] -> Ty -> * where
  Hyp   :: !(Index gam a) -> Ctxl c
    '[]
     del gam a
  Const :: !(c a) -> Ctxl c
    '[]
     del gam a
  ArrI  :: Ctxl c
    '[ T3 del (a :< gam) b ]
     del gam (a :-> b)
  -- Rec   :: Ctxl c
  --   '[ T3 del (a :< gam) a ]
  --    del gam a
  ArrE  :: Ctxl c
    '[ T3 del gam (a :-> b) , T3 del gam a ]
     del gam b
  CtxI  :: KnownLength as => Ctxl c
    '[ T3 del as a ]
     del gam (Ctx as a)
  CtxE  :: Ctxl c
    '[ T3 del gam (Ctx as a) , T3 (as # a :< del) gam b ]
     del gam b
  Add   :: Ctxl c
    '[ T3 del gam N , T3 del gam N ]
     del gam N
  Mul   :: Ctxl c
    '[ T3 del gam N , T3 del gam N ]
     del gam N
  Case :: Ctxl c
    '[ T3 del gam N , T3 del gam a , T3 del (N :< gam) a ]
     del gam a
  If    :: Ctxl c
    '[ T3 del gam O , T3 del gam a , T3 del gam a ]
     del gam a
  Ext   :: ExtArgs del gam as bs => !(Index del (as # a)) -> Ctxl c
     bs
     del gam a

class ExtArgs (del :: [([k],k)]) (gam :: [k]) (as :: [k]) (bs :: [([([k],k)],[k],k)]) | del gam as -> bs, bs -> as where
  toEnv :: Args p bs -> Env (p del gam) as
instance ExtArgs del gam Ø Ø where
  toEnv _ = Empty
instance ExtArgs del gam as bs => ExtArgs del gam (a :< as) (T3 del gam a :< bs) where
  toEnv (a :* as) = a :& toEnv as

data C :: Ty -> * where
  T :: C O
  F :: C O
  Z :: C N
  S :: !(C N)
    -> C N

instance Show (C a) where
  show = \case
    T   -> "True"
    F   -> "False"
    Z   -> show $ toInt Z
    S x -> show $ toInt $ S x

cadd :: C N -> C N -> C N
cadd = \case
  Z -> id
  S x -> S . cadd x

cmul :: C N -> C N -> C N
cmul = \case
  Z   -> pure Z
  S x -> cadd <*> cmul x

-- }}}

-- V {{{

data V :: Ty -> * where
  Fn   :: (V a -> V b) -> V (a :-> b)
  -- Rc   :: (V a -> V a) -> V a
  Clos :: (Env V as -> V a) -> V (Ctx as a)
  V    :: C a -> V a

with :: V (Ctx as a) -> Env V as -> V a
with (Clos f) = f

type family (~>) :: k -> k -> k
infixr 1 ~>

type instance (~>) = (:->)
type instance (~>) = (->)

class Apply (r :: k -> *) where
  (.@.) :: r (a ~> b) -> r a -> r b
infixl 8 .@.

instance Apply V where
  Fn f .@. a = f a

instance Apply (Derive del gam) where
  f .@. a = ArrE $$ f :* a :* Ø

instance Show (V a) where
  show = \case
    Fn   _ -> "<function>"
    -- Rc   _ -> "<fixpoint>"
    Clos _ -> "<closure>"
    V c    -> case c of
      T -> "True"
      F -> "False"
      Z   -> show $ toInt Z
      S x -> show $ toInt $ S x

-- }}}

-- Syntax {{{

type Derive = Derivation (Ctxl C)
type (&) = (#)
infix 3 &
type (==>) dg = Eval V (Fst dg) (Snd dg)
infix 2 ==>
type (|-)  dg = Derive (Fst dg) (Snd dg)
infix 2 |-

var :: Index gam a -> del & gam |- a
var = base . Hyp

(.+.) :: del & gam |- N
      -> del & gam |- N
      -> del & gam |- N
x .+. y = Add $$ x :* y :* Ø
infixl 6 .+.

(.*.) :: del & gam |- N
      -> del & gam |- N
      -> del & gam |- N
x .*. y = Mul $$ x :* y :* Ø
infixl 7 .*.

ifte :: del & gam |- O
     -> del & gam |- a
     -> del & gam |- a
     -> del & gam |- a
ifte b t f = If $$ b :* t :* f :* Ø

caseNat :: del &       gam  |- N
        -> del &       gam  |- a
        -> del & (N :< gam) |- a
        -> del &       gam  |- a
caseNat n z s = Case $$ n :* z :* s :* Ø

ct :: C a -> del & gam |- a
ct = base . Const

{-
lam' :: (forall sig. a ∈ sig -> del & gam |- b)
     -> del & gam |- (a :-> b)
lam' f = lam $ _
-}

lamAnn :: T a
    -> del & a :< gam |- b
    -> del &      gam |- a :-> b
lamAnn _ = lam

lam :: del & a :< gam |- b
    -> del &      gam |- a :-> b
lam body = ArrI $$ body :* Ø

{-
mu :: del & a :< gam |- a
    -> del &      gam |- a
mu body = Rec $$ body :* Ø
-}

{-
(.@) :: del & gam |- a :-> b
     -> del & gam |- a
     -> del & gam |- b
f .@ a = ArrE $$ f :* a :* Ø
infixl 2 .@
-}

box :: KnownLength as
    => del & as  |- a
    -> del & gam |- Ctx as a
box a = CtxI $$ a :* Ø

letIn ::           del & gam |- Ctx as a
      -> as # a :< del & gam |- b
      ->           del & gam |- b
letIn a b = CtxE $$ a :* b :* Ø

(@@) :: ExtArgs del gam as bs
     => as#a ∈ del
     -> Args Derive bs
     -> del & gam |- a
(@@) x = (Ext x $$)
infixl 9 @@

fromInt :: Int -> C N
fromInt n | n <= 0 = Z
      | True   = S $ fromInt $ n-1

toInt :: C N -> Int
toInt = \case
  Z   -> 0
  S x -> succ $ toInt x

int :: Int -> del & gam |- N
int = ct . fromInt

-- }}}

-- Known{Type,Length} {{{

class TypeC a => KnownType (a :: Ty) where
  type TypeC a :: Constraint
  type_ :: T a
instance KnownType O where
  type TypeC O = (() :: Constraint)
  type_ = TruthT
instance KnownType N where
  type TypeC N = (() :: Constraint)
  type_ = NatT
instance (KnownType a, KnownType b) => KnownType (a :-> b) where
  type TypeC (a :-> b) = (KnownType a, KnownType b)
  type_ = ArrT type_ type_
instance (KnownLength as, KnownType a) => KnownType (Ctx as a) where
  type TypeC (Ctx as a) = (KnownLength as, KnownType a)
  type_ = CtxT types_ type_

class LenC as => KnownLength (as :: [Ty]) where
  type LenC as :: Constraint
  fromList :: (forall a. r -> f a) -> [r] -> Env f as
  len :: p as -> Int
  types_ :: Env T as
instance KnownLength Ø where
  type LenC Ø = (() :: Constraint)
  fromList _ _ = Empty
  len _ = 0
  types_ = Empty
instance (KnownType a, KnownLength as) => KnownLength (a :< as) where
  type LenC (a :< as) = (KnownType a, KnownLength as)
  fromList f (r : rs) = f r :& fromList f rs
  len _ = succ $ len (Proxy :: Proxy as)
  types_ = type_ :& types_

toList :: (forall a. f a -> r) -> Env f as -> [r]
toList f = \case
  Empty   -> []
  a :& as -> f a : toList f as

-- }}}

{-
weakenUnder :: del & b :< gam |- a -> del & b :< c :< gam |- a
weakenUnder (D rs) = case rs of
  Hyp   x :$             _       -> var $ case x of
    Z_   -> Z_
    S_ x -> S_ (S_ x)
  Const c :$             _       -> ct c
  Add     :$ e1 :* e2 :* Ø       -> weakenUnder e1 .+. weakenUnder e2
  Mul     :$ e1 :* e2 :* Ø       -> weakenUnder e1 .*. weakenUnder e2
  Case    :$ e1 :* e2 :* e3 :* Ø -> caseNat (weakenUnder e1) (weakenUnder e2) undefined
  If      :$ e1 :* e2 :* e3 :* Ø -> ifte (weakenUnder e1) (weakenUnder e2) (weakenUnder e3)
  ArrI    :$ e  :* Ø             -> undefined
  ArrE    :$ e1 :* e2 :* Ø       -> undefined
  CtxI    :$ e  :* Ø             -> undefined
  CtxE    :$ e1 :* e2 :* Ø       -> undefined
  Ext x   :$ es                  -> undefined

weaken1 :: del & gam |- a -> del & b :< gam |- a
weaken1 (D rs) = case rs of
  Hyp   x :$             _       -> var $ S_ x
  Const c :$             _       -> ct c
  Add     :$ e1 :* e2 :* Ø       -> weaken1 e1 .+. weaken1 e2
  Mul     :$ e1 :* e2 :* Ø       -> weaken1 e1 .*. weaken1 e2
  Case    :$ e1 :* e2 :* e3 :* Ø -> caseNat (weaken1 e1) (weaken1 e2) undefined
  If      :$ e1 :* e2 :* e3 :* Ø -> ifte (weaken1 e1) (weaken1 e2) (weaken1 e3)
  ArrI    :$ e  :* Ø             -> lam _
  ArrE    :$ e1 :* e2 :* Ø       -> undefined
  CtxI    :$ e  :* Ø             -> undefined
  CtxE    :$ e1 :* e2 :* Ø       -> undefined
  Ext x   :$ es                  -> undefined
-}

-- Eval {{{

data Eval (f :: Ty -> *) :: [([Ty],Ty)] -> [Ty] -> Ty -> * where
  Eval ::
    { evalWith :: Context f Ctx del -> Env f gam -> f a
    } -> Eval f del gam a

evalArgs :: ExtArgs del gam as bs => Args (Eval f) bs -> Context f Ctx del -> Env f gam -> Env f as
evalArgs args ctx env = mapEnv (\e -> evalWith e ctx env) $ toEnv args

evaluate :: Ø & Ø |- a -> V a
evaluate = ($ Empty) . ($ EmptyC) . evalWith . eval

eval :: del & gam |- a -> del & gam ==> a
eval = induction $ \case
  Hyp   x :$             _  -> Eval $ \_   env -> indexEnv x env
  Const c :$             _  -> Eval $ \_   _   -> V c
  Add     :$ e1 :* e2 :* Ø  -> Eval $ \ctx env -> let
    x = evalWith e1 ctx env
    y = evalWith e2 ctx env
    in case (x,y) of
      (V a,V b) -> V $ cadd a b
  Mul     :$ e1 :* e2 :* Ø -> Eval $ \ctx env -> let
    x = evalWith e1 ctx env
    y = evalWith e2 ctx env
    in case (x,y) of
      (V a,V b) -> V $ cmul a b
  Case    :$ e1 :* e2 :* e3 :* Ø -> Eval $ \ctx env ->
    case evalWith e1 ctx env of
      V Z     -> evalWith e2 ctx env
      V (S x) -> evalWith e3 ctx $ V x :& env
  If      :$ e1 :* e2 :* e3 :* Ø -> Eval $ \ctx env ->
    case evalWith e1 ctx env of
      V T -> evalWith e2 ctx env
      V F -> evalWith e3 ctx env
  -- Rec     :$ e  :* Ø       -> Eval $ \ctx env -> Rc $ \a -> evalWith e ctx $ a :& env
  ArrI    :$ e  :* Ø       -> Eval $ \ctx env -> Fn $ \a -> evalWith e ctx $ a :& env
  ArrE    :$ e1 :* e2 :* Ø -> Eval $ \ctx env -> let
    ef = evalWith e1 ctx env
    a  = evalWith e2 ctx env
    in case ef of
      Fn f -> f a
      _    -> error "impossible"
  CtxI    :$ e  :* Ø        -> Eval $ \ctx _ -> Clos $ evalWith e ctx
  CtxE    :$ e1 :* e2 :* Ø  -> Eval $ \ctx env -> let
    a = evalWith e1 ctx env
    in evalWith e2 (a :&& ctx) env
  Ext x   :$ es -> Eval $ \ctx env -> case indexContext x ctx of
    Clos f -> f $ evalArgs es ctx env
    _      -> error "impossible"

-- }}}

-- Render {{{

data R :: Ty -> * where
  R :: (Int -> String) -> R a

display :: Ø & Ø |- a -> IO ()
display = putStrLn . showR 0 . ($ Empty) . ($ EmptyC) . evalWith . render

showR :: Int -> R a -> String
showR n (R f) = f n

render :: del & gam |- a -> Eval R del gam a
render = induction $ \case
  Hyp   x :$ _               -> Eval $ \_   env -> indexEnv x env
  Const c :$ _               -> Eval $ \_   _   -> R $ \_ -> show c
  Add     :$ e1 :* e2 :* Ø -> Eval $ \ctx env -> let
    x = evalWith e1 ctx env
    y = evalWith e2 ctx env
    in R $ \n -> showR n x ++ " + " ++ showR n y
  Mul     :$ e1 :* e2 :* Ø -> Eval $ \ctx env -> let
    x = evalWith e1 ctx env
    y = evalWith e2 ctx env
    in R $ \n -> showR n x ++ " * " ++ showR n y
  If      :$ e1 :* e2 :* e3 :* Ø -> Eval $ \ctx env -> R $ \n -> let
    b = evalWith e1 ctx env
    t = evalWith e2 ctx env
    f = evalWith e3 ctx env
    in concat
      [ "if "
      , showR n b
      , " then "
      , showR n t
      , " else "
      , showR n f
      ]
  Case    :$ e1 :* e2 :* e3 :* Ø -> Eval $ \ctx env -> R $ \n -> let
    x = evalWith e1 ctx env
    z = evalWith e2 ctx env
    v = "x" ++ show n
    s = evalWith e3 ctx $ R (pure v) :& env
    in concat
      [ "case "
      , showR n x
      , " of { Z => "
      , showR n z
      , " ; S " ++ v ++ " => "
      , showR (n+1) s
      , " }"
      ]
  -- Rec     :$ e  :* Ø             -> Eval $ \ctx env -> R $ \n -> let
  --   x    = "r" ++ show n
  --   body = evalWith e ctx $ R (pure x) :& env
  --   in concat
  --     [ "μ"
  --     , x
  --     , ". "
  --     , showR (n+1) body
  --     ]
  ArrI    :$ e  :* Ø             -> Eval $ \ctx env -> R $ \n -> let
    x    = "x" ++ show n
    body = evalWith e ctx $ R (pure x) :& env
    in concat
      [ "λ"
      , x
      , ". "
      , showR (n+1) body
      ]
  ArrE    :$ e1 :* e2 :* Ø -> Eval $ \ctx env -> let
    f = evalWith e1 ctx env
    a = evalWith e2 ctx env
    in R $ \n -> "(" ++ showR n f ++ " " ++ showR n a ++ ")"
  CtxI    :$ (e :: Eval R del as a) :* Ø       -> Eval $ \ctx _ -> R $ \n -> let
    m  = len (Proxy :: Proxy as)
    xs = [ "x" ++ show y
         | y <- [n..(n+m-1)]
         ]
    ts = types_ :: Env T as
    a  = evalWith e ctx $ fromList (R . pure) xs
    in concat
      [ "["
      , intercalate ","
        [ x ++ ":" ++ t
        | (x,t) <- zip xs $ toList show ts
        ]
      , "]"
      , "("
      , showR (n+m) a
      , ")"
      ]
  CtxE     :$ e1 :* e2 :* Ø -> Eval $ \ctx env -> let
    a = evalWith e1 ctx env
    in evalWith e2 (a :&& ctx) env
  Ext x    :$ es -> Eval $ \ctx env -> R $ \n -> let
    a   = indexContext x ctx
    es' = toList (showR n) $ evalArgs es ctx env
    in concat
      [ showR n a
      , "@("
      , unwords es'
      , ")"
      ]

-- }}}

-- Examples

add2 :: del & gam |- N :-> N
add2 = lamAnn NatT $ int 2 .+. var Z_

twice :: del & gam |- (a :-> a) :-> a :-> a
twice = lam $ lam $ var (S_ Z_) .@. (var (S_ Z_) .@. var Z_)

expon :: C N -> del & gam |- Box (N :-> N)
expon = \case
  Z   -> box $ lam $ ct $ S Z
  S x -> letIn (expon x) $ box
    $ lamAnn NatT
    $ var Z_ .*. ((Z_ @@ Ø) .@. var Z_)

e0 = lam $ var Z_
e1 = lam $ caseNat (var Z_)
  (int 2)
  (var Z_)
e2 :: del & gam |- Ctx '[N,N,N] N
e2 = box $ var (S_ $ S_ Z_) .+. var Z_ .*. var (S_ Z_)
e3 :: del & gam |- Ctx '[N] N
e3 = letIn e2 $ box $ Z_ @@ (var Z_ :* var Z_ :* var Z_ :* Ø)

{-
expon' :: del & gam |- N :-> Box (N :-> N)
expon' = mu $ lam $ caseNat (var Z_)
  ( box $ lam $ ct $ S Z )
  ( letIn (var (S_ (S_ Z_)) .@ var Z_ )
  $ box $ lam $ var Z_ .*. ((Z_ @@ Ø) .@ var Z_)
  )
-}

expon' :: del & gam |- Ctx '[N] (N :-> N)
expon' = box $ caseNat (var Z_)
  ( lam $ int 1 )
  ( letIn expon' $ lam $ var Z_ .*. (Z_ @@ (var (S_ Z_) :* Ø) .@. var Z_)
  )

