{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_RoboGame (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/amey/Study/Project/se2/TrapLand/.cabal-sandbox/bin"
libdir     = "/home/amey/Study/Project/se2/TrapLand/.cabal-sandbox/lib/x86_64-linux-ghc-8.0.1/RoboGame-0.1.0.0-GdBrEE9GKmnFvR19iVguXU"
dynlibdir  = "/home/amey/Study/Project/se2/TrapLand/.cabal-sandbox/lib/x86_64-linux-ghc-8.0.1"
datadir    = "/home/amey/Study/Project/se2/TrapLand/.cabal-sandbox/share/x86_64-linux-ghc-8.0.1/RoboGame-0.1.0.0"
libexecdir = "/home/amey/Study/Project/se2/TrapLand/.cabal-sandbox/libexec"
sysconfdir = "/home/amey/Study/Project/se2/TrapLand/.cabal-sandbox/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "RoboGame_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "RoboGame_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "RoboGame_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "RoboGame_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "RoboGame_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "RoboGame_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
