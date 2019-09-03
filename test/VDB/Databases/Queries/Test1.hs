-- | queries that need to be tested on the first test database.
module VDB.Databases.Queries.Test1 where

-- | queries that test the type system. including:
--   prj_{A,B,C,D} R ?=? prj_{A,F1<B,C>,D} R
--   prj_{A,B,C,D} R ?=? F1<prj_{A,B,D} R, prj_{A,C,D} R>
--   sel_{B=2} R ?=? F1<sel_{B=2} R, Empty>
--   sel_{B=2 and C=6} R ?=? sel_{F1<B=2,C=6>} R
--   R join_{C=C} S ?=? F2<R join_{C=C} S, Empty>
--   prj_{A,C} R union S ?=? prj_{A,C} R union prj_{A,C} S
--   prj_{A,C} R union S ?=? F2<prj_{A,C} R union S, Empty>