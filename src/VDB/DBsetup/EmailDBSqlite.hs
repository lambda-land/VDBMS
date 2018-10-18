-- Brute force translation of Variational relational algebra to SQL
module VDB.DBsetup.EmailDBSqlite where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
--import qualified VDB.Condition as C
--import qualified VDB.Target as T
--import VDB.Variational
--import VDB.Value  

import Database.Persist
import Database.Persist.Sqlite (runSqlite, runMigration)
import Database.Persist.TH (mkPersist, mkMigrate, persistLowerCase,
       share, sqlSettings, mkSave)

-- imports for dumpTable
--import Database.Persist.Sql (rawQuery, {-hi-}insert{-/hi-})
import Database.Persist.Sql (rawQuery, insert)
import Data.Conduit (($$))
import Data.Conduit.List as CL
import Control.Monad.IO.Class (liftIO)

import Data.Time.Calendar (Day)
import Data.Text (Text)

-- the type of email (rtype)
--data EmailType = TO | CC | BCC
--  deriving (Show,Eq)


-- from the database side:
-- employee primary key: eid
-- message primary key: mid
-- recipientinfo primary key: rid
-- referenceinfo primary key: rfid
-- for now the rtype and presCond are text, idea: instantiate them with persist value?
share [mkPersist sqlSettings, mkMigrate "enronEmail"] [persistLowerCase|
Employee
   firstName   Text
   lastName    Text
   emailId     Text
   email2      Text
   email3      Text
   email4      Text
   folder      Text
   status      Text
   presCond    Text
   deriving Show
Message
   sender      Text
   date        Day
   messageId   Text
   subject     Text
   body        Text
   folder      Text
   presCond    Text
   deriving Show
RecipientInfo
   mid        MessageId
   rtype      Text
   rvalue     Text
   date       Day
   presCond   Text
   deriving Show
ReferenceInfo
   mid         MessageId
   reference   Text
   presCond    Text
   deriving Show
PresCond
   employee        Text
   message         Text
   recipientInfo   Text
   referenceInfo   Text
   deriving Show
|]


main :: IO ()
main = runSqlite "enronEmail.sqlite3" $ runMigration enronEmail

{--
main = runSqlite "test1.sqlite3" $ do
    runMigrationSilent migrateTables{-hi-}
    insert $ Tutorial "Basic Haskell" "https://fpcomplete.com/school/basic-haskell-1" True{-/hi-}
    dumpTable


dumpTable = rawQuery "select * from Tutorial" [] $$ CL.mapM_ (liftIO . print)

--}

{-main = runSqlite "/src/VDB/DBsetup/test1.sqlite3" $ do
    buildDb
    dumpTable


buildDb = do
    runMigration migrateTables
    insert $ Tutorial "Basic Haskell" "https://fpcomplete.com/school/basic-haskell-1" True
    insert $ Tutorial "A monad tutorial" "https://fpcomplete.com/user/anne/monads" False
    insert $ Tutorial "Yesod usage" "https://fpcomplete.com/school/basic-yesod" True
    insert $ Tutorial "Putting the FUN in functors" "https://fpcomplete.com/user/anne/functors" False
    insert $ Tutorial "Basic Haskell" "https://fpcomplete/user/anne/basics" False



dumpTable = rawQuery "select * from Tutorial" [] $$ CL.mapM_ (liftIO . print)
-}
