-- | Linearizes a vq to a list of opt query,
--   generates a big SQL query from the opt queries,
--   runs it over the vdb,
--   cleans up the result,
--   returns a vtable.
module VDBMS.Approaches.Linearize.RunOneBigQuery where


