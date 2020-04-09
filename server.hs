import Network
import Network.HTTP
import System.IO


main :: IO ()
main = withSocketsDo $ do
         sock <- listenOn $ PortNumber 80
         putStrLn "Starting server ..."
         handleConnections sock

handleConnections :: Socket -> IO ()
handleConnections sock = do
  (handle, host, port) <- accept sock
  output <- hGetLine handle
  putStrLn output
  handleConnections sock
