--------------------------------------------------------------------------------
--- This module contains functions to obtain information concerning the current
--- distribution of the Curry implementation.
--- Most of the information is based on the external constants
--- <b>curryCompiler...</b>.
---
--- @author Bernd Brassel, Michael Hanus, Bjoern Peemoeller
--- @version November 2014
--------------------------------------------------------------------------------

{-# OPTIONS_CYMAKE -X TypeClassExtensions #-}

module Distribution (
  curryCompiler,curryCompilerMajorVersion,curryCompilerMinorVersion,
  curryRuntime,curryRuntimeMajorVersion,curryRuntimeMinorVersion,
  installDir,stripCurrySuffix,modNameToPath,
  currySubdir,inCurrySubdir,addCurrySubdir,
  rcFileName,rcFileContents,getRcVar,getRcVars,

  joinModuleIdentifiers, splitModuleIdentifiers, splitModuleFileName,
  inCurrySubdirModule,

  findFileInLoadPath,lookupFileInLoadPath,
  readFirstFileInLoadPath,getLoadPath,getLoadPathForFile,
  getLoadPathForModule, lookupModuleSourceInLoadPath,

  FrontendTarget(..),

  FrontendParams, defaultParams, rcParams,
  quiet, extended, overlapWarn, fullPath, htmldir, logfile, specials,
  setQuiet, setExtended, setOverlapWarn, setFullPath, setHtmlDir, setLogfile,
  setSpecials,

  callFrontend,callFrontendWithParams
  ) where

import List         (split)
import Char         (toLower)
import Directory    (doesFileExist)
import FileGoodies  (lookupFileInPath, getFileInPath, fileSuffix, stripSuffix)
import FilePath     ( FilePath, (</>), (<.>), addTrailingPathSeparator
                    , dropFileName, joinPath, normalise, splitDirectories
                    , splitExtension, splitFileName, splitSearchPath
                    , takeFileName
                    )
import IO
import PropertyFile
import System

-----------------------------------------------------------------
-- Compiler and run-time environment name and version
-----------------------------------------------------------------

-- if you do not use other functions but
-- if-then-else, and the _Prelude_ functions
-- (<), (>), (<=), (>=), (==)
-- directly on the following constants,
-- the compiler might be able to eliminate
-- them at compile time.

--- The name of the Curry compiler (e.g., "pakcs" or "kics2").
curryCompiler :: String
curryCompiler external

--- The major version number of the Curry compiler.
curryCompilerMajorVersion :: Int
curryCompilerMajorVersion external

--- The minor version number of the Curry compiler.
curryCompilerMinorVersion :: Int
curryCompilerMinorVersion external

--- The name of the run-time environment (e.g., "sicstus", "swi", or "ghc")
curryRuntime :: String
curryRuntime external

--- The major version number of the Curry run-time environment.
curryRuntimeMajorVersion :: Int
curryRuntimeMajorVersion external

--- The minor version number of the Curry run-time environment.
curryRuntimeMinorVersion :: Int
curryRuntimeMinorVersion external

--- Path of the main installation directory of the Curry compiler.
installDir :: FilePath
installDir external

---------------------------------------------------
-- retrieving user specified options from rc file
---------------------------------------------------

--- The name of the file specifying configuration parameters of the
--- current distribution. This file must have the usual format of
--- property files (see description in module PropertyFile).
rcFileName :: IO String
rcFileName = getEnviron "HOME" >>= return . (</> rcFile)
  where rcFile = '.' : curryCompiler ++ "rc"

--- Returns the current configuration parameters of the distribution.
--- This action yields the list of pairs (var,val).
rcFileContents :: IO [(String,String)]
rcFileContents = rcFileName >>= readPropertyFile

--- Look up a specific configuration variable as specified by user in his rc file.
--- Uppercase/lowercase is ignored for the variable names.
getRcVar :: String -> IO (Maybe String)
getRcVar var = getRcVars [var] >>= return . head

--- Look up configuration variables as specified by user in his rc file.
--- Uppercase/lowercase is ignored for the variable names.
getRcVars :: [String] -> IO [Maybe String]
getRcVars vars = do
  rcs <- rcFileContents
  return (map (flip lookup (map (\ (a, b) -> (map toLower a, b)) rcs))
              (map (map toLower) vars))

-----------------------------------------------------------
--- Functions for handling file names of Curry modules
-----------------------------------------------------------

type ModuleIdent = String

--- Split the `FilePath` of a module into the directory prefix and the
--- `FilePath` corresponding to the module name.
--- For instance, the call `splitModuleFileName "Data.Set" "lib/Data/Set.curry"`
--- evaluates to `("lib", "Data/Set.curry")`.
--- This can be useful to compute output directories while retaining the
--- hierarchical module structure.
splitModuleFileName :: ModuleIdent -> FilePath -> (FilePath, FilePath)
splitModuleFileName mid fn = case splitModuleIdentifiers mid of
  [_] -> splitFileName fn
  ms  -> let (base, ext) = splitExtension fn
             dirs        = splitDirectories base
             (pre , suf) = splitAt (length dirs - length ms) dirs
             path        = if null pre then ""
                                       else addTrailingPathSeparator (joinPath pre)
         in  (path, joinPath suf <.> ext)

--- Split up the components of a module identifier. For instance,
--- `splitModuleIdentifiers "Data.Set"` evaluates to `["Data", "Set"]`.
splitModuleIdentifiers :: ModuleIdent -> [String]
splitModuleIdentifiers = split (=='.')

--- Join the components of a module identifier. For instance,
--- `joinModuleIdentifiers ["Data", "Set"]` evaluates to `"Data.Set"`.
joinModuleIdentifiers :: [String] -> ModuleIdent
joinModuleIdentifiers = foldr1 combine
  where combine xs ys = xs ++ '.' : ys

--- Strips the suffix ".curry" or ".lcurry" from a file name.
stripCurrySuffix :: String -> String
stripCurrySuffix s =
  if fileSuffix s `elem` ["curry","lcurry"]
  then stripSuffix s
  else s

--- A module path consists of a directory prefix (which can be omitted)
--- and a module name (which can be hierarchical). For instance, the
--- following strings are module paths in Unix-based systems:
---
---     HTML
---     Data.Number.Int
---     curry/Data.Number.Int
type ModulePath = String

--- Transforms a hierarchical module name into a path name, i.e.,
--- replace the dots in the name by directory separator chars.
modNameToPath :: ModuleIdent -> String
modNameToPath = foldr1 (</>) . split (=='.')

--- Name of the sub directory where auxiliary files (.fint, .fcy, etc)
--- are stored.
currySubdir :: FilePath
currySubdir = ".curry"

--- Transforms a path to a module name into a file name
--- by adding the `currySubDir` to the path and transforming
--- a hierarchical module name into a path.
--- For instance, `inCurrySubdir "mylib/Data.Char"` evaluates to
--- `"mylib/.curry/Data/Char"`.
inCurrySubdir :: FilePath -> FilePath
inCurrySubdir filename =
  let (base,file) = splitFileName filename
   in base </> currySubdir </> modNameToPath file

--- Transforms a file name by adding the currySubDir to the file name.
--- This version respects hierarchical module names.
inCurrySubdirModule :: ModuleIdent -> FilePath -> FilePath
inCurrySubdirModule m fn = let (dirP, modP) = splitModuleFileName m fn
                           in  dirP </> currySubdir </> modP

--- Transforms a directory name into the name of the corresponding
--- sub directory containing auxiliary files.
addCurrySubdir :: FilePath -> FilePath
addCurrySubdir dir = dir </> currySubdir

-----------------------------------------------------------
--- finding files in correspondence to compiler load path
-----------------------------------------------------------

--- Returns the current path (list of directory names) of the
--- system libraries.
getSysLibPath :: IO [String]
getSysLibPath = case curryCompiler of
  "pakcs" -> return [installDir </> "lib", installDir </> "lib" </> "meta"]
  "kics"  -> return [installDir </> "src" </> "lib"]
  "kics2" -> return [installDir </> "lib", installDir </> "lib" </> "meta"]
  _       -> error "Distribution.getSysLibPath: unknown curryCompiler"

--- Adds a directory name to a file by looking up the current load path.
--- An error message is delivered if there is no such file.
lookupFileInLoadPath :: String -> IO (Maybe String)
lookupFileInLoadPath fn =
  getLoadPathForFile fn >>= lookupFileInPath (takeFileName fn) [""]

--- Adds a directory name to a file by looking up the current load path.
--- An error message is delivered if there is no such file.
findFileInLoadPath :: String -> IO String
findFileInLoadPath fn =
  getLoadPathForFile fn >>= getFileInPath (takeFileName fn) [""]

--- Returns the contents of the file found first in the current load path.
--- An error message is delivered if there is no such file.
readFirstFileInLoadPath :: String -> IO String
readFirstFileInLoadPath fn = findFileInLoadPath fn >>= readFile

--- Returns the current path (list of directory names) that is
--- used for loading modules.
getLoadPath :: IO [String]
getLoadPath = getLoadPathForFile "xxx"

--- Returns the current path (list of directory names) that is
--- used for loading modules w.r.t. a given main module file.
--- The directory prefix of the module file (or "." if there is
--- no such prefix) is the first element of the load path and the
--- remaining elements are determined by the environment variable
--- CURRYRPATH and the entry "libraries" of the system's rc file.
getLoadPathForFile :: String -> IO [String]
getLoadPathForFile file = do
  syslib <- getSysLibPath
  mblib  <- getRcVar "libraries"
  let fileDir = dropFileName file
  if curryCompiler `elem` ["pakcs","kics","kics2"] then
    do currypath <- getEnviron "CURRYPATH"
       let llib      = maybe [] splitSearchPath mblib
           curryDirs = [fileDir, normalise (currySubdir </> fileDir)]
       return $ curryDirs ++ (addCurrySubdirs
                  (fileDir : (if null currypath
                              then []
                              else splitSearchPath currypath) ++
                              llib ++ syslib))

    else error "Distribution.getLoadPathForFile: unknown curryCompiler"
 where
  addCurrySubdirs = concatMap (\ d -> [d, addCurrySubdir d])

--- Returns the current path (list of directory names) that is
--- used for loading modules w.r.t. a given module path.
--- The directory prefix of the module path (or "." if there is
--- no such prefix) is the first element of the load path and the
--- remaining elements are determined by the environment variable
--- CURRYRPATH and the entry "libraries" of the system's rc file.
getLoadPathForModule :: ModulePath -> IO [String]
getLoadPathForModule modpath = do
  syslib <- getSysLibPath
  mblib  <- getRcVar "libraries"
  let fileDir = dropFileName modpath
  if curryCompiler `elem` ["pakcs","kics","kics2"] then
    do currypath <- getEnviron "CURRYPATH"
       let llib = maybe [] (\l -> if null l then [] else splitSearchPath l)
                        mblib
       return $ (fileDir : (if null currypath
                            then []
                            else splitSearchPath currypath) ++
                           llib ++ syslib)
    else error "Distribution.getLoadPathForModule: unknown curryCompiler"

--- Returns a directory name and the actual source file name for a module
--- by looking up the module source in the current load path.
--- If the module is hierarchical, the directory is the top directory
--- of the hierarchy.
--- Returns Nothing if there is no corresponding source file.
lookupModuleSourceInLoadPath :: ModulePath -> IO (Maybe (String,String))
lookupModuleSourceInLoadPath modpath =
  getLoadPathForModule modpath >>= lookupSourceInPath
 where
  fn       = takeFileName modpath
  fnlcurry = modNameToPath fn ++ ".lcurry"
  fncurry  = modNameToPath fn ++ ".curry"

  lookupSourceInPath [] = return Nothing
  lookupSourceInPath (dir:dirs) = do
    lcurryExists <- doesFileExist (dir </> fnlcurry)
    if lcurryExists then return (Just (dir, dir </> fnlcurry)) else do
     curryExists <- doesFileExist (dir </> fncurry)
     if curryExists then return (Just (dir, dir </> fncurry))
                    else lookupSourceInPath dirs

-------------------------------------------------------------------
-- calling the front end
-------------------------------------------------------------------

--- Data type for representing the different target files that can be produced
--- by the front end of the Curry compiler.
--- @cons FCY  - FlatCurry file ending with .fcy
--- @cons FINT - FlatCurry interface file ending with .fint
--- @cons ACY  - AbstractCurry file ending with .acy
--- @cons UACY - Untyped (without type checking) AbstractCurry file ending with .uacy
--- @cons HTML - colored HTML representation of source program
--- @cons CY   - source representation employed by the frontend
data FrontendTarget = FCY | FINT | ACY | UACY | HTML | CY

--- Abstract data type for representing parameters supported by the front end
--- of the Curry compiler.
-- The parameters are of the form
-- FrontendParams Quiet Extended NoOverlapWarn FullPath HtmlDir LogFile Specials
-- where
--   Quiet         - work silently
--   Extended      - support extended Curry syntax
--   OverlapWarn   - warn for overlapping rules
--   FullPath dirs - the complete list of directory names for loading modules
--   HtmlDir file  - output directory (only relevant for HTML target)
--   LogFile file  - store all output (including errors) of the front end in file
--   Specials      - additional special parameters (use with care!)
data FrontendParams =
  FrontendParams Bool
                 Bool
                 Bool
                 (Maybe [String])
                 (Maybe String)
                 (Maybe String)
                 String

--- The default parameters of the front end.
defaultParams :: FrontendParams
defaultParams = FrontendParams False True True Nothing Nothing Nothing ""

--- The default parameters of the front end as configured by the compiler
--- specific resource configuration file.
rcParams :: IO FrontendParams
rcParams = do
  [mbExtended,mbOverlapWarn] <- getRcVars ["curryextensions","warnoverlapping"]
  return $ setExtended    (mbExtended    /= Just "no")
         $ setOverlapWarn (mbOverlapWarn /= Just "no")
         $ defaultParams

--- Set quiet mode of the front end.
setQuiet :: Bool -> FrontendParams -> FrontendParams
setQuiet s (FrontendParams _ v w x y z sp) = FrontendParams s v w x y z sp

--- Set extended mode of the front end.
setExtended :: Bool -> FrontendParams -> FrontendParams
setExtended s (FrontendParams a _ w x y z sp) = FrontendParams a s w x y z sp

--- Set overlap warn mode of the front end.
setOverlapWarn :: Bool -> FrontendParams -> FrontendParams
setOverlapWarn s (FrontendParams a b _ x y z sp) = FrontendParams a b s x y z sp

--- Set the full path of the front end.
--- If this parameter is set, the front end searches all modules
--- in this path (instead of using the default path).
setFullPath ::  [String] -> FrontendParams -> FrontendParams
setFullPath s (FrontendParams a b c _ y z sp) =
  FrontendParams a b c (Just s) y z sp

--- Set the htmldir parameter of the front end.
--- Relevant for HTML generation.
setHtmlDir ::  String -> FrontendParams -> FrontendParams
setHtmlDir  s (FrontendParams a b c d _ z sp) =
  FrontendParams a b c d (Just s) z sp

--- Set the logfile parameter of the front end.
--- If this parameter is set, all messages produced by the front end
--- are stored in this file.
setLogfile ::  String -> FrontendParams -> FrontendParams
setLogfile  s (FrontendParams a b c d e _ sp) =
  FrontendParams a b c d e (Just s) sp

--- Set additional specials parameters of the front end.
--- These parameters are specific for the current front end and
--- should be used with care, since their form might change in the future.
setSpecials :: String -> FrontendParams -> FrontendParams
setSpecials sp (FrontendParams a b c d e z _) =
  FrontendParams a b c d e z sp

--- Returns the value of the "quiet" parameter.
quiet :: FrontendParams -> Bool
quiet (FrontendParams x _ _ _ _ _ _) = x

--- Returns the value of the "extended" parameter.
extended :: FrontendParams -> Bool
extended (FrontendParams _ x _ _ _ _ _) = x

--- Returns the value of the "overlapWarn" parameter.
overlapWarn :: FrontendParams -> Bool
overlapWarn (FrontendParams _ _ x _ _ _ _) = x

--- Returns the full path parameter of the front end.
fullPath :: FrontendParams -> Maybe [String]
fullPath (FrontendParams _ _ _ x _ _ _) = x

--- Returns the htmldir parameter of the front end.
htmldir :: FrontendParams -> Maybe String
htmldir  (FrontendParams _ _ _ _ x _ _) = x

--- Returns the logfile parameter of the front end.
logfile :: FrontendParams -> Maybe String
logfile  (FrontendParams _ _ _ _ _ x _) = x

--- Returns the special parameters of the front end.
specials :: FrontendParams -> String
specials (FrontendParams _ _ _ _ _ _ x) = x

--- In order to make sure that compiler generated files (like .fcy, .fint, .acy)
--- are up to date, one can call the front end of the Curry compiler
--- with this action.
--- If the front end returns with an error, an exception is raised.
--- @param target - the kind of target file to be generated
--- @param progname - the name of the main module of the application to be compiled
callFrontend :: FrontendTarget -> String -> IO ()
callFrontend target p = do
  params <- rcParams
  callFrontendWithParams target params p

--- In order to make sure that compiler generated files (like .fcy, .fint, .acy)
--- are up to date, one can call the front end of the Curry compiler
--- with this action where various parameters can be set.
--- If the front end returns with an error, an exception is raised.
--- @param target - the kind of target file to be generated
--- @param params - parameters for the front end
--- @param modpath - the name of the main module possibly prefixed with a
---                  directory where this module resides
callFrontendWithParams :: FrontendTarget -> FrontendParams -> ModulePath
                       -> IO ()
callFrontendWithParams target params modpath = do
  parsecurry <- callParseCurry
  let lf      = maybe "" id (logfile params)
      syscall = parsecurry ++ " " ++ showFrontendTarget target
                           ++ " " ++ showFrontendParams
                           ++ " " ++ takeFileName modpath
  retcode <- if null lf
             then system syscall
             else system (syscall ++ " > " ++ lf ++ " 2>&1")
  if retcode == 0
   then done
   else ioError (userError "Illegal source program")
 where
   callParseCurry = do
     path <- maybe (getLoadPathForModule modpath) return (fullPath params)
     return (quote (installDir </> "bin" </> "cymake")
             ++ concatMap ((" -i" ++) . quote) path)

   quote s = '"' : s ++ "\""

   showFrontendTarget FCY  = "--flat"
   showFrontendTarget FINT = "--flat"
   showFrontendTarget ACY  = "--acy"
   showFrontendTarget UACY = "--uacy"
   showFrontendTarget HTML = "--html"
   showFrontendTarget CY   = "--parse-only"

   showFrontendParams = unwords
    [ if quiet       params then runQuiet     else ""
    , if extended    params then "--extended" else ""
    , if overlapWarn params then ""           else "--no-overlap-warn"
    , maybe "" ("--htmldir="++) (htmldir params)
    , specials params
    ]

   runQuiet = "--no-verb --no-warn --no-overlap-warn"
