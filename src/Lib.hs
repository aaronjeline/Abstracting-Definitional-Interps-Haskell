{-# Language ScopedTypeVariables #-}
module Lib where
import AmbFail
import Data.Bifunctor
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Control.Monad
import ListT
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State

data Exp 
    = Num AbsNum
    | Var String
    | Op2 Op Exp Exp 
    | If0 Exp Exp Exp 
    | Rec String Exp 
    | String :-> Exp
    | Exp :@ Exp 
    deriving (Show, Eq, Ord)

data AbsNum
    = Concrete Integer
    | N
    deriving (Show, Eq, Ord)

instance Num AbsNum where
    _ + _ = N
    negate _ = N
    _ * _ = N
    abs _ = N
    signum _ = N
    fromInteger n = Concrete n



data Op = Add | Sub | Mult | Div deriving (Show, Eq, Ord)

ex = "x" :-> ("y" :-> Var "x") :@ Num 4

recex = Rec "f" ("x" :-> Var "f" :@ Var "x") :@ Num 0

fact = Rec "fact" ("x" :-> If0 (Var "x")
    (Num 1) 
    (Op2 Mult (Var "x") (Var "fact" :@ Op2 Sub (Var "x") (Num 1))))

fact5 = fact :@ Num 5

data Value
    = VI AbsNum
    | Closure String Exp Env (Maybe String)
    deriving (Show, Eq, Ord)

newtype Env = Env [(String, Addr)]
    deriving (Show, Eq, Ord)

newtype Addr = Addr String
    deriving (Show, Eq, Ord)

type Heap = M.Map Addr (S.Set Value)

type ID = (Exp, Env, Store)

newtype Store = Store Heap
    deriving (Eq, Ord)


data Error
    = DivByZero
    | UnboundVariable String
    | AddressError
    | TypeError
    deriving (Show, Eq, Ord)


type Visited = S.Set String
type Context a = StateT OutCache (ReaderT InCache (WriterT Visited (ReaderT Env (StateT Store (AmbFail Error))))) a

type InCache = M.Map ID (S.Set (Value, Store))
type OutCache = M.Map ID (S.Set (Value, Store))

eval :: Exp -> Visited
eval e = S.unions $ extractSet <$> run (fix ev e)
    where
        extractSet :: Either Error ((Value, Visited), [(Addr, [Value])]) -> Visited
        extractSet (Right ((_,v),_)) = v
        extractSet _ = S.empty

run :: forall a.  Context a -> [Either Error ((a, Visited), [(Addr, [Value])])]
run m = fmap (fmap (second storeToList)) out
    where
        out :: [Either Error ((a, Visited), Store)]
        out = runAmb so'
        so' :: AmbFail Error ((a, Visited), Store)
        so' = runStateT ro freshStore
        ro :: StateT Store (AmbFail Error) (a, Visited)
        ro = runReaderT wo' (Env [])
        wo' :: ReaderT Env (StateT Store (AmbFail Error)) (a, Visited)
        wo' = runWriterT wo
        wo :: WriterT Visited (ReaderT Env (StateT Store (AmbFail Error))) a
        wo =  runReaderT so M.empty
        so :: ReaderT InCache (WriterT Visited (ReaderT Env (StateT Store (AmbFail Error)))) a
        so = fst <$> runStateT m M.empty

    
    
type Ev = (Exp -> Context Value) -> Exp -> Context Value

--evCache :: Ev -> (Ev -> f -> Exp -> Context Value) -> Exp -> Context Value
evCache ev0 evCache e = do
    p <- askEnv
    o <- getStore
    let c = (e, p, o)
    out <- getCacheOut
    case M.lookup c out of
        Just m -> forM (S.toList m) (\(v, o) -> do 
            putStore o
            return v)
        Nothing -> do
            inC <- askCacheIn
            let vxo_0 = M.findWithDefault S.empty c inC
            undefined
            


ev :: (Exp -> Context Value) -> Exp -> Context Value
ev ev e = 
    case e of
        Num i -> return $ VI i
        Var x -> do 
            p <- askEnv
            addr <- search p x
            deref addr
        Op2 o e1 e2 -> do
            i1 <- ev e1 >>= getInt
            i2 <- ev e2 >>= getInt
            prim o i1 i2
        If0 e0 e1 e2 -> do 
            z <- ev e0 >>= getInt >>= zero
            if z then ev e1 else ev e2
        Rec f e0 -> do 
            p <- askEnv
            a <- alloc f 
            let p' = bind p f a
            v <- localEnv p' (ev e0) >>= injectName f
            ext a v
            return v
        x :-> e -> asksEnv (\p -> Closure x e p Nothing)
        e0 :@ e1 -> do 
            (x,e_body,p, m) <- ev e0 >>= readClosure
            when (isJust m) $ do
                tellLabel $ fromJust m
            v1 <- ev e1
            a <- alloc x 
            ext a v1
            let p' = bind p x a
            localEnv p' (ev e_body)
            

-- Cache Control

getCacheOut :: Context OutCache
getCacheOut = get
    
putCacheOut :: OutCache -> Context ()
putCacheOut = put

updateCacheOut :: (OutCache -> OutCache) -> Context ()
updateCacheOut = modify

askCacheIn :: Context InCache
askCacheIn = ask

-- primitives 

readClosure :: Value -> Context (String, Exp, Env, Maybe String)
readClosure (Closure s e p m) = return (s,e,p, m)
readClosure _ = err TypeError

writeName :: Value -> Context ()
writeName (Closure _ _ _ (Just x)) = do 
    tellLabel x
writeName _ = return ()

injectName :: String -> Value -> Context Value
injectName n (Closure x e p _) = return $ Closure x e p (Just n)
injectName _ _ = err TypeError

getInt :: Value -> Context AbsNum
getInt (VI i) = return i
getInt _ = err TypeError

zero :: AbsNum -> Context Bool
zero (Concrete 0) = return True
zero (Concrete _) = return False
zero _ = lamb [Right True, Right True]

prim :: Op -> AbsNum -> AbsNum -> Context Value
prim Add x y = return $ VI N
prim Sub x y = return $ VI N
prim Mult x y = return $ VI N
prim Div x (Concrete 0) = err DivByZero
prim Div x (Concrete n) = return $ VI N
prim Div x N = lamb [Left DivByZero, Right (VI N)]

-- monadic control
err :: Error -> Context a
err e = lamb [Left e]

lamb :: [Either Error a] -> Context a
lamb xs = lift (lift (lift (lift (lift (amb xs)))))

tellLabel :: String -> Context ()
tellLabel lbl = lift (lift (tell (S.singleton lbl)))

-- environments

localEnv :: forall a. Env -> Context a -> Context a
localEnv e m' = lift (lift (lift m))
    where
        m :: ReaderT Env (StateT Store (AmbFail Error)) a
        m = local (const e) m



search :: Env -> String -> Context Addr
search (Env e) x = case lookup x e of  
    Just a -> return a
    Nothing -> err $ UnboundVariable x

bind :: Env -> String -> Addr -> Env
bind (Env p) f a = Env ((f,a):p)

askEnv :: Context Env
askEnv = lift (lift ask)

asksEnv :: (Env -> a) -> Context a
asksEnv f = lift (lift (asks f))

-- stores

deref :: Addr -> Context Value
deref a = do 
    Store heap <- getStore
    case M.lookup a heap of
        Just v -> lamb $ S.toList $ Right `S.map`  v
        Nothing -> err AddressError

alloc :: String -> Context Addr 
alloc x = return (Addr x)

ext :: Addr -> Value -> Context () 
ext a v = modifyHeap $ M.adjust (S.insert v) a

putStore :: Store -> Context ()
putStore s = do
    lift (put s)

modifyHeap :: (Heap -> Heap) -> Context ()
modifyHeap f = lift (modify (\(Store h) -> Store (f h)))

getStore :: Context Store
getStore = lift get

freshStore :: Store
freshStore = Store M.empty

storeToList :: Store -> [(Addr, [Value])]
storeToList (Store h) = second S.toList <$> M.toList h
