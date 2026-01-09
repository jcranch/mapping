module Data.Mapping.Util where


-- | For use in maps where we don't want to store default values
nonDefault :: Eq a => a -> a -> Maybe a
nonDefault d x
  | d == x    = Nothing
  | otherwise = Just x
