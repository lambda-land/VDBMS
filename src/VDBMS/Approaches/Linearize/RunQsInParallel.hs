-- | Linearizes a vq to a list of opt query,
--   runs them synchronously on the vdb,
--   filters the results accordingly,
--   gathers the results in a vtable.
module VDBMS.Approaches.Linearize.RunQsInParallel where


