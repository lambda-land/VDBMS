module Main where

import VDB.DBsetup.EnronEmailDB

import Database.HDBC.Sqlite3

main :: IO Connection
main = enronEmail
--main = return ()
