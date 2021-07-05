module Data.Either.Extra

%default total

public export
fromLeft : (b -> a) -> Either a b -> a
fromLeft f (Left a) = a
fromLeft f (Right b) = f b

public export
fromRight : (a -> b) -> Either a b -> b
fromRight f (Left a) = f a
fromRight f (Right b) = b

export
mapFstExtensional :
  {0 f, g : a -> b} -> ((x : a) -> f x === g x) ->
  (v : Either a c) -> mapFst f v === mapFst g v
mapFstExtensional eq (Left x) = cong Left (eq x)
mapFstExtensional eq (Right x) = Refl

export
mapSndExtensional :
  {0 f, g : a -> b} -> ((x : a) -> f x === g x) ->
  (v : Either w a) -> mapSnd f v === mapSnd g v
mapSndExtensional eq (Left x) = Refl
mapSndExtensional eq (Right x) = cong Right (eq x)

export
mapFstFusion :
  {0 f : a -> b} -> {0 g : b -> c} ->
  (v : Either a e) -> mapFst g (mapFst f v) === mapFst (g . f) v
mapFstFusion (Left x) = Refl
mapFstFusion (Right x) = Refl

export
mapSndFusion :
  {0 f : a -> b} -> {0 g : b -> c} ->
  (v : Either w a) -> mapSnd g (mapSnd f v) === mapSnd (g . f) v
mapSndFusion (Left x) = Refl
mapSndFusion (Right x) = Refl
