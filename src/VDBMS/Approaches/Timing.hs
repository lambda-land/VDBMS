-- timing parts of the system.
module VDBMS.Approaches.Timing (
       
       timeItName

) where 

import Control.Monad.IO.Class (MonadIO, liftIO)

import System.Clock
import Text.Printf
import Formatting
import Formatting.Clock

timeItName :: String -> Clock -> IO a -> IO a
timeItName s c ioa = 
  do start <- getTime c
     a <- ioa
     end <- getTime c
     putStrLn $ s ++ ": "
     fprint (timeSpecs % "\n") start end
     return a

-- Clock data type
-- Monotonic: a monotonic but not-absolute time which never changes after start-up.
-- Realtime: an absolute Epoch-based time (which is the system clock and can change).
-- ProcessCPUTime: CPU time taken by the process.
-- ThreadCPUTime: CPU time taken by the thread.