module Main where

import Data.List (partition)
import System.Environment (getArgs)
import System.IO (hSetBuffering, BufferMode(..), stdout)

import Core
import Sugar

go s = case result of
         Left e -> putStrLn ("ERROR: " ++ show e)
         Right s -> putStrLn s


    where parse' s = case parse s of
                       Left e -> Left (show e)
                       Right e -> Right e
          check' e = case runTcM (checkTop [] e) ([], 0) of
                       Left err -> Left err
                       Right (t, _)  -> Right t
          result = do e <- parse' s
                      t <- check' e
                      return (show (eval [] e) ++ "\n:: " ++ show t)

main = do args <- getArgs
          let print (Left err) = putStrLn ("ERROR: " ++ err)
              print (Right v)  = putStrLn v
              repl = do putStr "> "
                        s <- getLine
                        if s == ":q"
                        then return ()
                        else do go s
                                repl

          if null args
          then do hSetBuffering stdout NoBuffering
                  repl
          else mapM_ (\file -> readFile file >>= go) args
