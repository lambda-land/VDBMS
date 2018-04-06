-- | A module that contains several doctests for testing ParsingSQL.

module ParserTest where 

import ParsingSQL
import Text.Megaparsec

-- | TO DO : 1. fix choice among the condition 
--           2. CHOICE for 2 alternative 
--            
-- | Basic tests for lexer.
-- >>> parseTest spaceConsumer "-- comments"
-- ()
--
-- >>> parseTest spaceConsumer "/*blockcomments*/"
-- ()



-- | Tests for featureExpr and condition 
-- 
--   >>> parseTest featureExpr "true"
--   FLit True
--   
--   >>> parseTest featureExpr "US"
--   FRef (Feature {featureName = "US"})
--   
--   >>> parseTest featureExpr "US AND Iran"
--   FAnd (FRef (Feature {featureName = "US"})) (FRef (Feature {featureName = "Iran"}))
--  
--   >>> parseTest condition "true"
--   CLit True 
-- 
--   >>> parseTest condition "Price > 5000"
--   CComp GT (Val (S "Price")) (Val (I 5000))
--



-- | Tests for attribute list and relation list
-- 
--   >>> parseTest attrlistExpr "a"
--   A (Attribute {attributeName = "a"})
-- 
--   >>> parseTest attrlistExpr "a1,a2,a3"
--   AConcat (AConcat (A (Attribute {attributeName = "a1"})) (A (Attribute {attributeName = "a2"}))) (A (Attribute {attributeName = "a3"}))
--  
--   >>> parseTest attrlistExpr "CHOICE(encrypt, (mid,isEncrypted, enryptionKey), (mid,isEncrypted))"
--   AttrChc (FRef (Feature {featureName = "encrypt"})) (AConcat (AConcat (A (Attribute {attributeName = "mid"})) (A (Attribute {attributeName = "isEncrypted"}))) (A (Attribute {attributeName = "enryptionKey"}))) (AConcat (A (Attribute {attributeName = "mid"})) (A (Attribute {attributeName = "isEncrypted"})))
--
--   >>> parseTest attrlistExpr "CHOICE(encrypt,(CHOICE(signed,(mid,signed,signKey),(mid,signed))),attr1)" 
--   AttrChc (FRef (Feature {featureName = "encrypt"})) (AttrChc (FRef (Feature {featureName = "signed"})) (AConcat (AConcat (A (Attribute {attributeName = "mid"})) (A (Attribute {attributeName = "signed"}))) (A (Attribute {attributeName = "signKey"}))) (AConcat (A (Attribute {attributeName = "mid"})) (A (Attribute {attributeName = "signed"})))) (A (Attribute {attributeName = "attr1"}))
--   
--   >>> parseTest relationlistExpr "r"
--   R (Relation {relationName = "r"})
--   
--   >>> parseTest relationlistExpr "r1,r2,r3"
--   CROSSJOIN (CROSSJOIN (R (Relation {relationName = "r1"})) (R (Relation {relationName = "r2"}))) (R (Relation {relationName = "r3"}))
--   
--   >>> parseTest relationlistExpr "CHOICE(true,(r1,r2,r3),r4)"
--   RelChc (FLit True) (CROSSJOIN (CROSSJOIN (R (Relation {relationName = "r1"})) (R (Relation {relationName = "r2"}))) (R (Relation {relationName = "r3"}))) (R (Relation {relationName = "r4"}))
--  


-- | Tests for FromExpr and WhereExpr
--  
--   >>> parseTest fromExpr "FROM encryption, signature, referenceInfo"
--   From (CROSSJOIN (CROSSJOIN (R (Relation {relationName = "encryption"})) (R (Relation {relationName = "signature"}))) (R (Relation {relationName = "referenceInfo"}))) 
--  
--   >>> parseTest fromExpr "FROM CHOICE(encrypt, encrption, signature)"
--   From (RelChc (FRef (Feature {featureName = "encrypt"})) (R (Relation {relationName = "encrption"})) (R (Relation {relationName = "signature"})))
--   
--   >>> parseTest whereExpr "WHERE isEncrypted = true"
--   Where (CComp EQ (Val (S "isEncrypted")) (Val (B True)))


-- | Tests for query 
-- 
--   >>> parseTest query "SELECT mid FROM encryption WHERE isEncrypted = true"
--   Select (A (Attribute {attributeName = "mid"})) (From (R (Relation {relationName = "encryption"}))) (Where (CComp EQ (Val (S "isEncrypted")) (Val (B True))))
--   
--   >>> parseTest query "SELECT CHOICE(encrypt, (mid,isEncrypted,enryptionKey),(mid,enryptionKey)) FROM encryption WHERE isEncrypted = true"
--   Select (AttrChc (FRef (Feature {featureName = "encrypt"})) (AConcat (AConcat (A (Attribute {attributeName = "mid"})) (A (Attribute {attributeName = "isEncrypted"}))) (A (Attribute {attributeName = "enryptionKey"}))) (AConcat (A (Attribute {attributeName = "mid"})) (A (Attribute {attributeName = "enryptionKey"})))) (From (R (Relation {relationName = "encryption"}))) (Where (CComp EQ (Val (S "isEncrypted")) (Val (B True))))
--   
--   >>> parseTest query "SELECT mid FROM CHOICE(encrypt AND signed, (signiture, encryption), signiture) WHERE true"
--   Select (A (Attribute {attributeName = "mid"})) (From (RelChc (FAnd (FRef (Feature {featureName = "encrypt"})) (FRef (Feature {featureName = "signed"}))) (CROSSJOIN (R (Relation {relationName = "signiture"})) (R (Relation {relationName = "encryption"}))) (R (Relation {relationName = "signiture"})))) (Where (CLit True))
--   
--   >>> parseTest query "SELECT mid, CHOICE(encrypt, isEncrypted) ,enryptionKey FROM encryption WHERE isEncrypted = true"
