-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForce.BruteForceSendQsPersist where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
-- import VDB.Algebra
-- import VDB.Name
-- import qualified VDB.FeatureExpr as F
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
-- import VDB.Variational
-- import VDB.Type  

-- import Data.Text as T (Text, pack, append, concat)


-- import Database.Persist
-- import Database.Persist.Sqlite (runSqlite, runMigration)
-- import Database.Persist.TH (mkPersist, mkMigrate, persistLowerCase,
--        share, sqlSettings, mkSave)

-- -- imports for dumpTable
-- import Database.Persist.Sql (rawQuery, rawSql)
-- --import Database.Persist.Sql (rawQuery, insert)
-- import Data.Conduit (($$))
-- import Data.Conduit.List as CL
-- import Control.Monad.IO.Class (liftIO)


--rawQuery :: Text -> [PersistValue] -> 
--conduit-1.2.13.1:Data.Conduit.Internal.Conduit.Source
--          m [PersistValue]
--runQ :: MonadIO m => T.Text -> m [PersistValue]
--runQ q = rawSql q [] $$ CL.mapM_ (liftIO . print)

-- runQBrute :: (BaseBackend env
--       ~
--       Database.Persist.Sql.Types.Internal.SqlBackend,
--       HasPersistBackend env,
--       Control.Monad.Reader.Class.MonadReader env m,
--       resourcet-1.1.11:Control.Monad.Trans.Resource.Internal.MonadResource
--         m) =>
--       Opt Text -> Opt (m [PersistValue])
--runQBrute (o,q) = (o, runQ q)

-- getBruteRes :: (BaseBackend env
--       ~
--       Database.Persist.Sql.Types.Internal.SqlBackend,
--       HasPersistBackend env,
--       Control.Monad.Reader.Class.MonadReader env m,
--       resourcet-1.1.11:Control.Monad.Trans.Resource.Internal.MonadResource
--         m) =>
--       [Opt Text] -> [Opt (m [PersistValue])]
--getBruteRes = CL.map runQBrute

