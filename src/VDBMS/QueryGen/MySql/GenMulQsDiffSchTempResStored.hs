-- | generates a relational query with its own independent schema
--   for each of the relational queries in a list while taking advantage
--   of the stored temporary results.
-- Note that this approach requires us to clean up the tables we get
-- back from the database and adjust their schema into one unified
-- schema and accumulate all tuples into one table
module VDBMS.QueryGen.MySql.GenMulQsDiffSchTempResStored where 

