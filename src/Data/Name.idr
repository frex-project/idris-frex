module Data.Name

import Data.List
import Data.List1
import Data.Stream

export
data Name = MkName String

-- TODO: Move to base's `Data.Stream`
export
concat : Stream (List1 a) -> Stream a
concat (aas :: aass) = go aas aass where

  go : List1 a -> Stream (List1 a) -> Stream a
  go (a ::: [])         (aas :: aass) = a :: go aas aass
  go (a ::: (a' :: as)) aass          = a :: go (a' ::: as) aass

export
names : Stream Name
names = map MkName $ concat $ letters :: uniqueNames where

  letters : List1 String
  letters = toList1 $ map cast $ unpack "xyzabcstudefghijklmnopqrvw"

  uniqueNames : Stream (List1 String)
  uniqueNames = nats <&> \ n =>
                letters <&> \ x =>
                x ++ show n

export
Show Name where
  show (MkName nm) = nm
