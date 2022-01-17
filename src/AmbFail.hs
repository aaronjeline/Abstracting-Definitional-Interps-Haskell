{-# Language ScopedTypeVariables, InstanceSigs #-}
module AmbFail 
    ( AmbFail
    , amb
    , runAmb
    )
where

import Control.Monad.Trans

runAmb :: AmbFail e a -> [Either e a]
runAmb (AF xs) = xs

amb :: [Either e a] -> AmbFail e a
amb = AF

newtype AmbFail e a = AF [Either e a]

instance Functor (AmbFail e) where
    fmap :: forall a b. (a -> b) -> AmbFail e a -> AmbFail e b
    fmap f (AF []) = AF []
    fmap f (AF (x:xs)) = AF (y:ys)
        where
            y = case x of 
                Left e -> Left e 
                Right a -> Right $ f a
            AF ys = fmap f (AF xs)

append :: AmbFail e a -> AmbFail e a -> AmbFail e a
append (AF a) (AF e) = AF (a ++ e)

join :: forall a e m. AmbFail e (AmbFail e a) -> AmbFail e a
join (AF []) =  AF []
join (AF (as:ass)) =  case as of
                        Left e -> AF (Left e:ass')
                        Right as' -> append as' (AF ass')
    where
        ass' :: [Either e a]
        AF ass' = join (AF ass)

instance Applicative (AmbFail e) where
    pure x = AF [Right x]
    (<*>) :: forall a b. 
        AmbFail e (a -> b) -> AmbFail e a -> AmbFail e b
    (AF []) <*> (AF _) = AF []
    (AF (f:fs)) <*> (AF xs) = 
        append (AF xs') (AF fs <*> AF xs)
        where
            xs' :: [Either e b]
            xs' = case f of
                Left e -> fmap (const (Left e)) xs
                Right f' -> fmap (f'' f') xs
            f'' :: (a -> b) -> Either e a -> Either e b
            f'' = (<$>)
                        

instance Monad (AmbFail e) where    
    xs >>= k = k =<< xs




