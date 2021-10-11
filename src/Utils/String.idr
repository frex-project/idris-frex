module Utils.String

export
uncapitalise : String -> String
uncapitalise str = case unpack str of
  [] => ""
  (x :: xs) => pack $ toLower x :: xs
