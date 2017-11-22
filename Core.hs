module Core where

import Control.Monad ((<=<), liftM2)
import Data.List (intercalate)

import Debug.Trace

--------------------------------------------------------------------------------
-- Core syntax
--------------------------------------------------------------------------------

type Ident = String
type TIdent = Int
data Core = CInt Integer | CAdd Core Core | CMult Core Core
          | CBool Bool | CIs0 Core | CIf Core Core Core
          | CVar Ident | CLam Ident Core | CApp Core Core | CLet Ident Core Core
          | CPair Core Core | CLetPair Ident Ident Core Core
          | CUnit | CLetUnit Core Core
          | CInl Core | CInr Core
          | CCase Core (Ident, Core) (Ident, Core)
          | CFix Core
  deriving (Eq, Show)

data CType = CTInt | CTBool | CTFun CType CType
           | CTProd CType CType | CTOne
           | CTSum CType CType
           | CTVar TIdent
  deriving (Eq)

data CScheme = CScheme [TIdent] CType

varName i = names !! i
    where letters = [[c] | c <- ['a'..'z']]
          names   = letters ++ [first ++ last | first <- names, last <- letters]

pp _ CTInt = "Int"
pp _ CTBool = "Bool"
pp _ CTOne = "1"
pp n (CTFun t u)
    | n > 0 = "(" ++ pp 0 (CTFun t u) ++ ")"
    | otherwise = pp 1 t ++ " -> " ++ pp 0 u
pp n (CTProd t u)
    | n > 1 = "(" ++ pp 1 (CTProd t u) ++ ")"
    | otherwise = pp 2 t ++ " * " ++ pp 2 u
pp n (CTSum t u)
    | n > 1 = "(" ++ pp 1 (CTProd t u) ++ ")"
    | otherwise = pp 2 t ++ " + " ++ pp 2 u
pp _ (CTVar i) = varName i

instance Show CType where
    show t = pp 0 t

instance Show CScheme where
    show (CScheme [] t) = show t
    show (CScheme vs t) = "forall " ++ intercalate " " (map varName vs) ++ ". " ++ show t

fv (CTVar a)    = [a]
fv (CTSum t u)  = fv t ++ fv u
fv (CTProd t u) = fv t ++ fv u
fv (CTFun t u)  = fv t ++ fv u
fv _            = []

fvs (CScheme vs t) = filter (`elem` vs) (fv t)


--------------------------------------------------------------------------------
-- Type checking: monad
--------------------------------------------------------------------------------

type TyEnv = [(Ident, CScheme)]

assumeType x t g = ((x, CScheme [] t) : g)
assumeScheme x s g = ((x, s) : g)

type TySubst = [(TIdent, CType)]
type TcState = (TySubst, Int)

data TcM a = TcM { runTcM :: TcState -> Either String (a, TcState) }

instance Functor TcM where
    fmap f = (>>= return . f)

instance Applicative TcM where
    pure = return
    (<*>) = liftM2 ($)

instance Monad TcM where
    return x = TcM (\s -> Right (x, s))
    TcM sf >>= vf =
        TcM (\s0 -> case sf s0 of
                      Left s -> Left s
                      Right (v, s1) -> runTcM (vf v) s1)

typeError err = TcM (\_ -> Left err)
fresh         = TcM (\(s, i) -> Right (CTVar i, (s, i + 1)))
bind a t
    | a `elem` fv t = typeError ("Occurs check: " ++ varName a ++ " in " ++ show t)
    | otherwise = TcM (\(s, i) -> Right ((), ((a, t) : s, i)))

--------------------------------------------------------------------------------
-- Type checking: substitutions, instantiation, and generalization
--------------------------------------------------------------------------------

apply :: TySubst -> CType -> CType
apply s (CTVar a) =
    case lookup a s of
      Just t -> apply s t
      _      -> CTVar a
apply s (CTProd t u) =
    CTProd (apply s t) (apply s u)
apply s (CTSum t u) =
    CTSum (apply s t) (apply s u)
apply s (CTFun t u) =
    CTFun (apply s t) (apply s u)
apply _  t = t

applyM :: CType -> TcM CType
applyM t = TcM (\(s, i) -> Right (apply s t, (s, i)))

applyS :: CScheme -> TcM CScheme
applyS (CScheme vs t) = TcM go
    where go (s, i) = Right (CScheme vs (apply s' t), (s, i))
              where s' = filter ((`notElem` vs) . fst) s

generalize :: TyEnv -> CType -> TcM CScheme
generalize g t =
    do t' <- applyM t
       gvs <- concat `fmap` mapM (return . fvs <=< applyS . snd) g
       let uvs = filter (`notElem` gvs) (fv t')
       return (CScheme uvs t')

instantiate :: CScheme -> TcM CType
instantiate (CScheme vs t) =
    do us <- mapM (const fresh) vs
       return (apply (zip vs us) t)

--------------------------------------------------------------------------------
-- Type checking: unification
--------------------------------------------------------------------------------

expect :: CType -> CType -> TcM ()
expect t u =
    do t' <- applyM t
       u' <- applyM u
       unify t' u'

unify :: CType -> CType -> TcM ()
--Modify this right here
--Something like 6 cases?
--Functions (likely recursive unify calls?)
--Products (same)
--Sums (same)
--Ints, bools, units, and variables.
--Wants to return a TcM unit value

--From the notes:
--If t == u, succeed.
--If either are unification variables, use "bind"
--If types don't match (e.g. int and bool), type error as shown
--Else, they must be compound types (sums, pairs, functions) so unify their components.
--So 3 cases for sums pairs and functions using pattern matching
--Two cases for unification variables
--One case for catch-all if == true succeed else fail

--Useful function: applyM. Updates/applies stored unification variables.
--Provided sample case:
unify (TFun t1 t2) (TFun u1 u2) =
    do unify t1 u1
       expect t2 u2     -- Make sure we take account of having unified t1 and u1
unify t u = typeError ("Expected " ++ show t ++ " but got " ++ show u ++
                       "\n(Some cases of unification may not be implemented)")
--Need to match matching types. If they don't match, type error.
--Question: how do you actually "fill in" the box like the directions say?
--------------------------------------------------------------------------------
-- Type checking: inference
--------------------------------------------------------------------------------

checkTop :: TyEnv -> Core -> TcM CType
checkTop g e =
    do v <- fresh
       check g e v
       applyM v

check :: TyEnv -> Core -> CType -> TcM ()
check _ (CInt _) t =
    typeError "Type checking not implemented for integer constants"
check g (CAdd e1 e2) t =
    do expect CTInt t
       check g e1 CTInt
       check g e2 CTInt
check g (CMult e1 e2) t =
    typeError "Type checking not implemented for multiplication"
check _ (CBool _) t =
    typeError "Type checking not implemented for Boolean constants"
check g (CIs0 e) t =
    typeError "Type checking not implemented for zero tests"
check g (CIf e e1 e2) t =
    typeError "Type checking not implemented for conditionals"
check g (CVar x) t =
    typeError "Type checking not implemented for variables"
check g (CLam x e) t =
    typeError "Type checking not implemented for lambdas"
check g (CApp e1 e2) u =
    typeError "Type checking not implemented for application"
check g (CLet x e1 e2) t =
    typeError "Type checking not implemented for let"
check g (CPair e1 e2) t =
    do u1 <- fresh
       u2 <- fresh
       expect (CTProd u1 u2) t
       check g e1 u1
       check g e2 u2
check g (CLetPair x1 x2 e1 e2) t =
    do u1 <- fresh
       u2 <- fresh
       check g e1 (CTProd u1 u2)
       check (assumeType x1 u1 (assumeType x2 u2 g)) e2 t
check _ CUnit t =
    typeError "Type checking not implemented for unit introduction"
check g (CLetUnit e1 e2) t =
    typeError "Type checking not implemented for unit elimination"
check g (CInl e) t =
    typeError "Type checking not implemented for Inl"
check g (CInr e) t =
    typeError "Type checking not implemented for Inr"
check g (CCase e (x1, e1) (x2, e2)) t =
    typeError "Type checking not implemented for case"
check g (CFix e) t =
    do u1 <- fresh
       u2 <- fresh
       expect t (CTFun u1 u2)
       check g e (CTFun t (CTFun u1 u2))

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data Value = VInt Integer | VBool Bool | VFun VEnv Ident Core
           | VPair Value Value | VUnit
           | VInl Value | VInr Value
           | VRef Integer
  deriving (Eq, Show)

type VEnv = [(Ident, Value)]

eval :: VEnv -> Core -> Value
eval _ (CInt x) =
    VInt x
eval h (CAdd e1 e2) =
    let VInt x1 = eval h e1
        VInt x2 = eval h e2 in
    VInt (x1 + x2)
eval h (CMult e1 e2) =
    let VInt x1 = eval h e1
        VInt x2 = eval h e2 in
    VInt (x1 * x2)
eval _ (CBool b) =
    VBool b
eval h (CIs0 e) =
    let VInt x = eval h e in
    VBool (x == 0)
eval h (CIf e1 e2 e3) =
    let VBool b = eval h e1 in
    if b then eval h e2 else eval h e3
eval h (CVar x) =
    let Just v = lookup x h in v
eval h (CLam x e) =
    VFun h x e
eval h (CApp e1 e2) =
    let VFun h' x e = eval h e1
        v = eval h e2 in
    eval ((x, v) : h') e
eval h (CLet x e1 e2) =
    let v1 = eval h e1 in
    eval ((x,v1) : h) e2
eval h (CPair e1 e2) =
    let v1 = eval h e1
        v2 = eval h e2 in
    VPair v1 v2
eval h (CLetPair x1 x2 e1 e2) =
    let VPair v1 v2 = eval h e1 in
    eval ((x1, v1) : (x2, v2) : h) e2
eval h CUnit =
    VUnit
eval h (CLetUnit e1 e2) =
    let VUnit = eval h e1 in
    eval h e2
eval h (CInl e) =
    let v = eval h e in
    VInl v
eval h (CInr e) =
    let v = eval h e in
    VInr v
eval h (CCase e (x1, e1) (x2, e2)) =
    let v = eval h e in
    case v of
      VInl w -> eval ((x1, w) : h) e1
      VInr w -> eval ((x2, w) : h) e2
eval h (CFix f) =
    VFun h "$x" (CApp (CApp f (CFix f)) (CVar "$x"))
