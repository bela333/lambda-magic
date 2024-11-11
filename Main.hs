module Main where
import Text.Parsec
import Control.Monad (forever)
import System.IO (hFlush, stdout)
import Control.Monad.State (evalStateT, MonadIO (liftIO), MonadState (get), modify)
import Control.Applicative (Alternative(some))
import Data.List (intercalate)

data Term where
    Free :: String -> Term
    Bound :: Int -> Term
    Lam :: String -> Term -> Term
    App :: Term -> Term -> Term
    Effect :: String -> [Term] -> Term

instance Show Term where
  show :: Term -> String
  show (Free s) = s
  show (Bound n) = "#"++show n
  show (Lam n t) = "\\"++n++". " ++ show t
  show (App t1 t2) = "("++show t1++")("++show t2++")"
  show (Effect name terms) = name ++ show terms

hshow :: Term -> String
hshow (Free s) = "Free " ++ show s
hshow (Bound n) = "Bound " ++ show n
hshow (Lam n t) = "Lam " ++ show n ++ " (" ++ hshow t ++ ")"
hshow (App t1 t2) = "App (" ++ hshow t1 ++ ") (" ++ hshow t2 ++ ")"
hshow (Effect name terms) = "Effect " ++ show name

uprint :: Term -> IO ()
uprint = putStrLn . hshow

bindSingle :: String -> Int -> Term -> Term
bindSingle boundName level (Free freeName)
    | freeName == boundName = Bound level
    | otherwise             = Free freeName
bindSingle boundName level (Lam name t)
    | boundName == name = Lam name t
    | otherwise         = Lam name $ bindSingle boundName (level+1) t
bindSingle boundName level (App t1 t2) = App (b t1) (b t2)
    where b = bindSingle boundName level
bindSingle boundName level t = t

bind :: Term -> Term
bind (Lam name t) = Lam name $ bind $ bindSingle name 0 t
bind (App t1 t2) = App (bind t1) (bind t2)
bind t = t

unbindSingle :: String -> Int -> Term -> Term
unbindSingle boundName level (Bound n)
    | level == n = Free boundName
    | otherwise  = Bound n
unbindSingle boundName level (Lam name t) = Lam name $ unbindSingle boundName (level+1) t
unbindSingle boundName level (App t1 t2) = App (b t1) (b t2)
    where b = unbindSingle boundName level
unbindSingle boundName level t = t

unbind :: Term -> Term
unbind (Lam name t) = Lam name $ unbind $ unbindSingle name 0 t
unbind (App t1 t2) = App (unbind t1) (unbind t2)
unbind t = t

increaseScopeBy :: Int -> Int -> Term -> Term
increaseScopeBy level amount (Bound n)
    | level > n = Bound n
    | otherwise = Bound $ n + amount
increaseScopeBy level amount (Lam name t) = Lam name $ increaseScopeBy (level+1) amount t
increaseScopeBy level amount (App t1 t2) = App (increaseScopeBy level amount t1) (increaseScopeBy level amount t2)
increaseScopeBy level amount (Effect name ts) = Effect name $ map (increaseScopeBy level amount) ts
increaseScopeBy level amount t = t

rename :: Term -> Int -> Term -> Term
rename inner level (Bound n)
    | level == n = increaseScopeBy 0 level inner
    | level < n  = Bound (n-1)
    | level > n  = Bound n
rename inner level (Lam name t) = Lam name $ rename inner (level+1) t
rename inner level (App t1 t2) = App (r t1) (r t2)
    where r = rename inner level
rename inner level (Effect name ts) = Effect name $ map (rename inner level) ts
rename inner level t = t

beta :: Term -> Term
beta (App t1 t2) = case (beta t1, beta t2) of
                      (Effect name ts, t2) -> Effect name $ ts ++ [t2]
                      (Lam _ t, t2) -> beta $ rename t2 0 t
                      (t1, t2)         -> App t1 t2
beta (Lam name t) = Lam name $ beta t
beta t = t

exec :: Term -> Term
exec = unbind.beta.bind

zeroTerm :: Term
zeroTerm = Effect "zero" []

succTerm :: Term
succTerm = Effect "succ" []

runNumberTerm :: Term -> Int
runNumberTerm (Effect "succ" [t]) = 1+runNumberTerm t
runNumberTerm (Effect "zero" []) = 0

parseNumber :: Term -> Int
parseNumber t = runNumberTerm$exec$App (App t succTerm) zeroTerm



topParser :: Monad m => ParsecT String u m Term
topParser = applicationParser

expressionParser :: Monad m => ParsecT String u m Term
expressionParser = do
    spaces
    r <- between (char '(') (char ')') topParser <|> lambdaParser <|> variableParser
    spaces
    return r

variableParser :: Monad m => ParsecT String u m Term
variableParser = Free <$> many1 alphaNum

applicationParser :: Monad m => ParsecT String u m Term
applicationParser = chainl1 expressionParser $ do
    spaces
    return App


lambdaParser :: Monad m => ParsecT String u m Term
lambdaParser = do
    char '\\'
    spaces
    identifier <- many1 alphaNum
    spaces
    char '.'
    spaces
    Lam identifier <$> topParser

defineVariable :: Term -> String -> Term -> Term
defineVariable t name = App (Lam name t)


zero :: Term
zero = Lam "s" $ Lam "z" $ Free "z"

one :: Term
one = Lam "s" $ Lam "z" $ App (Free "s") (Free "z")

two :: Term
two = Lam "s" $ Lam "z" $ App (Free "s") (App (Free "s") (Free "z"))

incr :: Term
incr = Lam "n" $ Lam "s" $ Lam "z" $ App (App (Free "n") (Lam "p" $ App (Free "s") (Free "p"))) (App (Free "s") (Free "z"))

add :: Term
add = Lam "a" $ Lam "b" $ Lam "s" $ Lam "z" $ App (App (Free "a") (Lam "p" $ App (Free "s") (Free "p"))) (App (App (Free "b") (Free "s")) (Free "z"))

mul :: Term
Right mul = execString [] "(\\a.\\b.\\s.\\z.a (\\p.b s p) (z))"


execString :: [(String, Term)] -> String -> Either ParseError Term
execString variables s = case parse (do v<-topParser;eof;return v) "" s of
                Right t -> Right $ exec $ foldl (uncurry . defineVariable) t variables
                other -> other

defaultVariables = [
    ("zero", zero),
    ("one", one),
    ("two", two),
    ("incr", incr),
    ("mul", mul),
    ("add", add)]

repeatRead :: [(String, Term)] -> IO (Maybe Term)
repeatRead variables = do
    putStr "Type in the value of the new variable:"
    liftIO $ hFlush stdout
    line <- getLine
    case execString variables line of
                Left err -> do
                    putStrLn "Error:"
                    print err
                    putStrLn ""
                    repeatRead variables
                Right val -> do
                    return $ Just val
                    

main :: IO ()
main = flip evalStateT defaultVariables $ forever $ do
    variables <- get
    liftIO $ putStr "Type in an expression: "
    liftIO $ hFlush stdout
    line <- liftIO getLine
    case line of
        "DEF" -> do
                 liftIO $ putStr "Type in the name of the new variable:"
                 liftIO $ hFlush stdout
                 name <- liftIO getLine
                 t <- liftIO $ repeatRead variables
                 case t of
                    Just t -> do
                        _ <- modify ((name, t):)
                        return ()
                    Nothing -> return ()
        "VARS" -> do
            let a = "Currently defined variables:":map (\(name, value)->name ++ ": " ++ show value) variables
            liftIO $ putStrLn $ intercalate "\n" a
        _ -> case execString variables line of
                Left err -> do
                    liftIO $ putStrLn "Error:"
                    liftIO $ print err
                    liftIO $ putStrLn ""
                Right val -> liftIO $ print val