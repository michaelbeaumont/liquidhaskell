{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.Liquid.FileNames (
    Ext (..)
  
  , repFileName
  , extFileName
  , extModuleName
  , isExtFile
  , tagName 
  , dummyName
  
  , preludeName
  , boolConName
  , listConName
  , tupConName
  , vvName
  
  , getHsTargets
  , getFileInDirs
  , findFileInDirs
  , getIncludePath
  , resolvePath
  , copyFiles
  , deleteBinFiles
) where

import qualified Control.Exception            as Ex
import           Control.Monad.State
import           Data.List                    hiding (find)
import qualified Data.Map                     as M
import           Data.Maybe                   (fromMaybe)
import           Language.Haskell.Liquid.Misc
import           System.Directory
import           System.Environment
import           System.FilePath
import           System.FilePath.Find

------------------------------------------------------------
---------------- IO/Paths/Flags/Constants ------------------
------------------------------------------------------------

envVarName = "LIQUIDHS"
envPrefix  = "$" ++ envVarName ++ "/"

getIncludePath ::  IO String
getIncludePath = getEnv envVarName



data Ext = Cgi | Out | Fq | Html | Cst | Annot | LHs | Hs | Spec | Hquals | Pred | PAss| Dat
           deriving (Eq, Ord)

extMap   = M.fromList [ (Cgi,    "cgi")
                      , (Pred,   "pred")
                      , (PAss,   "pass")
                      , (Dat,    "dat")
                      , (Out,    "out")
                      , (Fq,     "fq")
                      , (Html,   "html")
                      , (Cst,    "cst")
                      , (Annot,  "annot")
                      , (Hs,     "hs")
                      , (LHs,    "lhs")
                      , (Spec,   "spec")
                      , (Hquals, "hquals") ]

repFileName     :: Ext -> FilePath -> FilePath
repFileName ext = extFileName ext . dropFileName

extFileName     :: Ext -> FilePath -> FilePath
extFileName ext = (`addExtension` (extMap M.! ext))

isExtFile ::  Ext -> FilePath -> Bool
isExtFile ext = ((extMap M.! ext) `isSuffixOf`)

extModuleName ::  String -> Ext -> FilePath
extModuleName modName ext =
  case explode modName of
    [] -> errorstar $ "malformed module name: " ++ modName
    ws -> extFileName ext $ foldr1 (</>) ws
  where explode = words . map (\c -> if c == '.' then ' ' else c)

preludeName  :: String
preludeName  = "Prelude"

-- libName      :: String -> FilePath
-- libName ext  = envPrefix ++ "Prelude." ++ ext

-- existingFiles :: String -> [FilePath] -> IO [FilePath]
-- existingFiles = filterM . warnMissing

-- warnMissing s f
--   = do b <- doesFileExist f
--        unless b $ putStrLn $ printf "WARNING: missing file (%s): %s" s f
--        return b

copyFiles :: [FilePath] -> FilePath -> IO ()
copyFiles srcs tgt
  = do Ex.catch (removeFile tgt) $ \(_ :: Ex.IOException) -> return ()
       forM_ srcs (readFile >=> appendFile tgt)

deleteBinFiles :: FilePath -> IO ()
deleteBinFiles fn = mapM_ (tryIgnore "delete binaries" . removeFile)
                  $ (fn `replaceExtension`) `fmap` exts
  where exts = ["hi", "o"]

-- retry ::  IOError -> [IO a] -> IO a
-- retry err []     = ioError err
-- retry err (a:as) = Ex.catch a $ \(e :: Ex.IOException) -> retry err as

resolvePath :: FilePath -> FilePath -> IO FilePath
resolvePath base path
  = case stripPrefix envPrefix path of
      Just path' -> liftM (</> path') getIncludePath
      Nothing    -> return $ if isAbsolute path then path else base </> path


----------------------------------------------------------------------------------

getHsTargets p
  | hasTrailingPathSeparator p = getHsSourceFiles p
  | otherwise                  = return [p]

getHsSourceFiles = find dirs hs
  where hs   = extension ==? ".hs" ||? extension ==? ".lhs"
        dirs = liftM (not . ("dist" `isSuffixOf`)) directory

---------------------------------------------------------------------------


getFileInDirs :: FilePath -> [FilePath] -> IO (Maybe FilePath)
getFileInDirs name = findFirst (testM doesFileExist . (</> name))

findFileInDirs ::  FilePath -> [FilePath] -> IO FilePath
findFileInDirs file dirs
  = liftM (fromMaybe err) (findFirst (find always (fileName ==? file)) dirs)
    where err = errorstar $ "findFileInDirs: cannot find " ++ file ++ " in " ++ show dirs


----------------------------------------------------------------------------
--------------- Global Name Definitions ------------------------------------
----------------------------------------------------------------------------

dummyName   = "_LIQUID_dummy"
tagName     = "TAG"
boolConName = "Bool"
listConName = "List"
tupConName  = "Tuple"
vvName      = "VV"