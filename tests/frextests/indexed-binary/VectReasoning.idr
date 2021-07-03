module VectReasoning

import Data.Vect
import PreorderReasoning

total public export
Tabulate : (n : Nat) -> (Fin n -> a) -> Vect n a
Tabulate Z     f = Nil
Tabulate (S n) f = (f 0) :: Tabulate n (f . FS)

export
Tabulate_ext : (n : Nat) -> (f,g : Fin n -> a) -> ((i : Fin n) -> f i = g i) ->
  Tabulate n f = Tabulate n g
Tabulate_ext Z f g _ = Refl
Tabulate_ext (S n) f g pf = 
  rewrite (pf FZ) in
  cong (g FZ ::) (Tabulate_ext n (f . FS) (g . FS) (\ i => pf (FS i)))
  


export
index_Tabulate : (n : Nat) -> (f : Fin n -> a) -> (i : Fin n) ->
  index i  (Tabulate n f) = f i 
index_Tabulate _ f FZ     = Refl
index_Tabulate _ f (FS i) = index_Tabulate _ (f . FS) i

-- The inverse is index.
export
Vect_ext : (v, w : Vect n a) -> ((i : Fin n) -> index i v = index i w)
           -> v = w
Vect_ext  {n = Z  } Nil      Nil      ext = Refl
Vect_ext  {n = S n} (x :: v) (y :: w) ext 
  with (ext FZ, Vect_ext v w (\ i => ext (FS i)))
 Vect_ext {n = S n} (x :: v) (x :: v) ext | (Refl , Refl)
   = Refl
         
export
Vect_initiality : (v : Vect 0 a) -> v = []
Vect_initiality [] = Refl

export
Vect_ext_rev : (v, w : Vect n a) -> v = w -> (i : Fin n) ->
               index i v = index i w 
Vect_ext_rev v v Refl i = Refl

export
Vect_lookup : (vs : Vect n v) -> (Elem x vs) -> (y : v ** x = y)
Vect_lookup (x :: _ ) Here          = (x ** Refl)
Vect_lookup (_ :: xs) (There later) = Vect_lookup xs later

public export
indexElem : (vs : Vect n v) -> Elem x vs -> v
indexElem xs = fst . (Vect_lookup xs)

export
mapFusionVect : (f : b -> c) ->
                (g : a -> b) ->
                (xs : Vect n a) -> map f (map g xs) = map (f . g) xs
mapFusionVect f g []      = Refl
mapFusionVect f g (x::xs) = rewrite mapFusionVect f g xs in Refl

export
index_naturality : (xs : Vect n x) -> (i : Fin n) -> (f : x -> y) ->
                   (index i (map f xs)) = f (index i xs)
index_naturality (x :: xs) FZ     f = Refl
index_naturality (_ :: xs) (FS i) f = index_naturality xs i f

export
index_replication : (n : Nat) -> (i : Fin n) -> (a : x) ->
                    index i (replicate n a) = a
index_replication _ FZ     a = Refl
index_replication _ (FS i) a = index_replication _ i a

export
index_zipWith_cons : (m,n : Nat) -> (i : Fin n) -> (xs : Vect n x) -> 
                     (xss : Vect n (Vect m x)) -> 
                     index i (zipWith (::) xs xss) = 
                     (index i xs) :: (index i xss)
index_zipWith_cons m _ FZ     (x :: _ ) (xs :: _  ) = Refl
index_zipWith_cons m _ (FS i) (_ :: xs) (_  :: xss) = 
  index_zipWith_cons m _ i xs xss

export
index_transpose : (m,n : Nat) -> (xss : Vect m (Vect n x)) -> (i : Fin n) -> 
                  index i (transpose xss) = map (index i) xss
index_transpose Z     n [] i = index_replication n i []
index_transpose (S m) n (xs :: xss) i = 
  rewrite index_zipWith_cons _ _ i xs (transpose xss) in
  rewrite index_transpose _ _ xss i in 
  Refl


foldrImpl_ext :
  (f : elem -> acc -> acc) -> (e : acc) -> 
  (go1, go2 : acc -> acc) -> 
  (xs : Vect n elem) ->
  ((a : acc) -> go1 a = go2 a) ->
  foldrImpl f e go1 xs = foldrImpl f e go2 xs
foldrImpl_ext f e go1 go2 []        ext = (ext e)
foldrImpl_ext f e go1 go2 (x :: xs) ext = 
  Calculate [
    foldrImpl f e go1 (x :: xs) 
    ==| Refl ,
    foldrImpl f e (go1 . (f x)) xs
    ==| foldrImpl_ext f e (go1 . (f x)) (go2 . (f x)) xs (\ a => ext (f x a)),
    foldrImpl f e (go2 . (f x)) xs
    ==| Refl ,
    foldrImpl f e go2 (x :: xs) ==| QED
  ]
  
composeIdLeftNeutralExt : (f : a -> b) -> (x : a) -> (Prelude.id . f) x = f x
composeIdLeftNeutralExt f x = ?help0

foldrImpl_ripple : 
  (f : elem -> acc -> acc) -> (e : acc) ->
  (go1, go2 : acc -> acc) -> 
  (xs : Vect n elem) ->   
  foldrImpl f e (go2 . go1) xs = go2 (foldrImpl f e go1 xs)
foldrImpl_ripple f e go1 go2 []        = Refl
foldrImpl_ripple f e go1 go2 (x :: xs) = Calculate
  [
  foldrImpl f e (go2 . go1) (x :: xs)
  ==| Refl ,
  foldrImpl f e (go2 . go1 . (f x)) xs
  ==| foldrImpl_ripple f e (go1 . (f x)) go2 xs ,
  go2 (foldrImpl f e (go1 . (f x))  xs)
  ==| Refl ,
  go2 (foldrImpl f e go1 (x :: xs))
  ==| QED
  ]



export
foldrCons : (f : a -> b -> b) -> (e : b) -> (x : a) -> (xs : Vect n a) ->
  foldr f e (x :: xs) = f x (foldr f e xs)
foldrCons f e x xs = Calculate
  [
  foldr f e (x :: xs) 
  ==| Refl ,
  foldrImpl f e id (x :: xs) 
  ==| Refl ,
  foldrImpl f e (id . (f x)) xs
  ==| foldrImpl_ext f e (id . (f x)) ((f x) . id) xs (\ u => Refl) ,
  foldrImpl f e ((f x) . id) xs
  ==| foldrImpl_ripple f e id (f x) xs ,
  f x (foldrImpl f e id xs)
  ==| Refl ,
  f x (foldr f e xs) 
  ==| QED
  ]

export
foldrUP : (f : a -> b -> b) -> (e : b) -> (g : {n : Nat} -> Vect n a -> b) ->
  (pf_e : g [] = e) -> 
  (pf_cons : 
   (x : a) -> {n : Nat} -> (xs : Vect n a) -> 
   g (x :: xs) = f x (g xs) 
  ) ->
  {n : Nat} -> (xs : Vect n a) -> g xs = foldr f e xs
foldrUP f e g pf_e _       []        = pf_e
foldrUP f e g pf_e pf_cons (x :: xs) = Calculate
  [
  g (x :: xs) 
  ==| pf_cons x xs ,
  f x (g xs) 
  ==| cong (f x) (foldrUP f e g pf_e pf_cons xs) ,
  f x (foldr f e xs)
  ==| sym (foldrCons f e x xs) ,
  foldr f e (x :: xs) ==| QED
  ]

export
mapId : (xs : Vect n a) -> map Prelude.id xs = xs
mapId xs = Vect_ext _ _ (\i =>
  index_naturality xs i id)


public export
Vect_ctx_map : (n : Nat) -> (f : Fin n -> a -> b) -> Vect n a -> Vect n b
Vect_ctx_map _ f [] = []
Vect_ctx_map _ f (x :: xs) = (f 0 x) :: Vect_ctx_map _ (f . FS) xs

export
index_Vect_ctx_map : (n : Nat) -> (f : Fin n -> a -> b) -> (xs : Vect n a) 
  -> (i : Fin n) -> 
  index i (Vect_ctx_map n f xs) = f i (index i xs)
index_Vect_ctx_map _ f (x :: _ ) FZ = Refl
index_Vect_ctx_map _ f (_ :: xs) (FS i) = index_Vect_ctx_map _ (f . FS) xs i

export
Vect_ctx_map_constant : (n : Nat) -> (f : Fin n -> a -> b) -> (x : a) ->
Vect_ctx_map n f (replicate n x) = Tabulate n (flip f x) 
Vect_ctx_map_constant Z     f x = Refl
Vect_ctx_map_constant (S n) f x = 
  rewrite Vect_ctx_map_constant n (f . FS) x in 
  Refl


export
map_Tabulate :  (n : Nat) -> (f : a -> b) -> (g : Fin n -> a) -> 
  (map f $ Tabulate n g) = Tabulate n (f . g)
map_Tabulate n f g = Vect_ext _ _ $ \i => Calculate [
  index i (map f $ Tabulate n g)
  ==| index_naturality (Tabulate n g) i f , 
  f (index i $ Tabulate n g)
  ==| cong f (index_Tabulate n g i) ,
  f (g i)
  ==| sym (index_Tabulate n (f . g) i) ,
  index i (Tabulate n (f . g))
  ==| QED
  ]

export  
Tabulate_constantly : (n : Nat) -> (x : a) ->
  Tabulate n (\ _ => x) = replicate n x
Tabulate_constantly n x =
  Vect_ext _ _ $ \i =>
  rewrite index_Tabulate    n   (\ _ => x) i in
  rewrite index_replication n i         x    in
  Refl


||| Should probably go elsewhere
export
cong2 : (f : t -> s -> u) -> a = b -> c = d -> f a c = f b d
cong2 f Refl Refl = Refl

public export
dep_cong2 : (0 s : t -> Type) -> (0 u : (i : t) -> s i -> Type) ->
  (0 f : (i : t) -> (j : s i) -> u i j) -> 
  {0 a,b : t} -> {0 c : s a} -> {0 d : s b} -> 
  a ~=~ b -> c ~=~ d -> f a c ~=~ f b d
dep_cong2 s u f Refl Refl = Refl





||| The type of (extensional) equality between two families indexed by Fin n.
||| Probably best used as an infix operation f `FinExtEq` g.
public export
FinExtEq : {n : Nat} -> {a,b : (i : Fin n) -> Type} ->
  (f : (i : Fin n) -> a i) -> (g : (i : Fin n) -> b i) -> Type
FinExtEq {n=  Z} f g = Unit
FinExtEq {n=S n} f g = 
  ((f FZ) = (f FZ)
  ,FinExtEq (\i => f (FS i)) 
            (\i => g (FS i)))


public export
FinToElem : (0 xs : Vect n a) -> (i : Fin n) -> Elem (index i xs) xs
FinToElem (x :: _ ) FZ     = Here
FinToElem (_ :: xs) (FS i) = There (FinToElem xs i)



public export
ElemToFin : { xs : Vect n a } -> Elem x xs -> Fin n
ElemToFin {x = x} { xs = (x :: ys) } Here  = FZ
ElemToFin {x = x} { xs = (_ :: ys) } (There later)  = FS (ElemToFin later)

export
ElemToFinSpec : {xs : Vect n a} -> (pos : Elem x xs) ->
                index (ElemToFin pos) xs = x
ElemToFinSpec Here = Refl
ElemToFinSpec (There pos) = ElemToFinSpec pos 

export
ElemToFinToElem : (xs : Vect n a ) -> (pos : Elem x xs) ->
                  FinToElem xs (ElemToFin pos) ~=~ pos 
                  --- strange that = doesn't work here. Bug?
ElemToFinToElem (x :: _ )  Here           = Refl
ElemToFinToElem (y :: xs) (There pos) = 
  let u = dep_cong2 
            (\0 x       => Elem x xs)
            (\0 x , pos => Elem x (y :: xs))  
            (\0 x , pos => There pos)
            (ElemToFinSpec pos)
            (ElemToFinToElem xs pos) in
  Calculate [
  There (FinToElem xs (ElemToFin pos))
  ==| u ,
  There pos
  ==| QED
  ]
  
export
FinToElemToFin : (xs : Vect n a ) -> (i : Fin n) ->
             ElemToFin (FinToElem xs i) ~=~ i
FinToElemToFin (x::_ ) FZ     = Refl
FinToElemToFin (_::xs) (FS i) = cong FS (FinToElemToFin xs i)

export
DPair_ext : {0 b : a -> Type} -> (p : DPair a b) -> 
            (fst p ** snd p) = p
DPair_ext (x ** y) = Refl
