{-# LANGUAGE OverloadedStrings #-}

module Main where   

import Text.RegExp
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  line <- getLine
  putStrLn $ show $ acceptFull (fromString (args!!0)) line
