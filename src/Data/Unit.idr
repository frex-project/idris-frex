module Data.Unit

%default total

export
unitIrrelevant : {x, y : ()} -> x === y
unitIrrelevant {x = ()} {y = ()} = Refl
