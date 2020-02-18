-- timing parts of the system.
module VDBMS.Approaches.Timing  where 

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
     -- let t :: Double
     --     t = fromIntegral (start-end) * 1e-12
     -- liftIO $ printf (s ++ ": %6.2fs\n") t
     putStrLn $ s ++ ": "
     fprint (timeSpecs % "\n") start end
     return a
     -- fprint (timeSpecs % (s ++ ": \n")) start end
     -- liftIO $ printf (c ++ ": %6.2fs\n") t

-- import System.Directory
-- import System.Clock
-- import System.CPUTime
-- import Text.Printf

-- time :: IO t -> IO t
-- time a = do
--     start <- getCPUTime
--     v <- a
--     end   <- getCPUTime
--     let diff = (fromIntegral (end - start)) / (10^12)
--     printf "Computation time: %0.5f sec\n" (diff :: Double)
--     return v


