-- | vqs for employee database.
module VDBMS.UseCases.Test.Queries where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.Test.Schema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
import Database.HDBC 
import VDBMS.VDB.Name hiding (name)
-- import VDBMS.VDB.GenName

-- import Data.Time.LocalTime
import Data.Time.Calendar

-- for test
import Data.Map (fromList)
import VDBMS.DBMS.Value.Type


-- opttest :: [Opt a]
opttest = [(F.And feone fetwo,1), (fetwo,2),(F.And fetwo feone,3),(feone,4)]

-- 
qone, qtwo, qthree :: Algebra
qempty = Empty

-- r1
qone = tRef rone

-- r2
qtwo = tRef rtwo

-- π (a1)r1
qthree = project (pure $ trueAttr aone_) qone

-- π (a1, a2) r1
qfour = project [trueAttr aone_, trueAttr atwo_] qone

-- π (a1^f1) r1
qfive = project (pure $ att2optatt aone_ feone) qone

-- π (a1^f2, a2^f3) r1
qfive' = project [att2optatt aone_ fetwo, att2optatt atwo_ fethree] qone

-- π (a1) r4
qsix = project (pure $ trueAttr aone_) (tRef rfour)

-- π (a1^f2) r4
qseven = project (pure $ att2optatt aone_ fetwo) (tRef rfour)

-- π (a1^f2) r5
qeight = project (pure $ att2optatt aone_ fetwo) (tRef rfive)

-- π (a1) r5
qnine = project (pure $ trueAttr aone_) (tRef rfive)

-- f1 ⟨π (a1) r5, π (a1) r6 ⟩
qten = choice 
  feone 
  (project (pure $ trueAttr aone_) (tRef rfive))
  (project (pure $ trueAttr aone_) (tRef rsix))

-- f2 ⟨π (a1) r1, π (a1) r6 ⟩
qelleven = choice 
  fetwo
  (project (pure $ trueAttr aone_) (tRef rone))
  (project (pure $ trueAttr aone_) (tRef rsix))

-- π (a1) (f2 ⟨π (a1) r1, π (a1) r6 ⟩)
qtwelve = project (pure $ trueAttr aone_) qelleven

-- f1 ⟨r5, r6⟩
qthirteen = choice
  feone
  (tRef rfive)
  (tRef rsix)

qrfive = tRef rfive

qrsix = tRef rsix