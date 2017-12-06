module Main where
import Data.Hex
import Numeric
import Data.List.Split (chunksOf,splitOn)
import Data.Maybe (isJust)
import Control.Monad
import Control.Monad.Trans (lift)
import Data.Char
import Data.Map
import Data.Int
import Text.Parsec.Prim
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token 
import System.Environment (getArgs)

data AsmProgram = AsmProgram { symbolTable :: SymbolTable,
                               opCodeTable :: OpCodeTable,
                               literalTable :: LiteralTable,
                               lineSource :: Map Int String } deriving (Eq,Show)

data OpCodeTable = OpCodeTable { instructionList :: Map Int Instruction,
                                 instructionSize :: Map Int Int,
                                 opCode :: Map Int String } deriving (Eq,Show)

data LiteralTable = LiteralTable { literals :: Map Int Imm } deriving (Eq,Show)

data SymbolTable = SymTab { entries :: Map Int SymbolRow,
                            entryNo :: Map String Int } deriving (Eq,Show)

data SymbolRow = SymRow { varName :: String,
                          value :: Maybe [Int],
                          byteValue :: Maybe ByteValue,
                          sizeM :: Maybe Int,
                          definedFlag :: Bool,
                          symbolType :: Stype,
                          lineNo :: Int,
                          address :: String } | EmptySymRow | ToDeleteSym deriving (Eq,Show)

data Stype = BSS | TEXT | DATA | LABEL | GLOBAL | EXTERN deriving (Eq,Show)

data ByteValue = DD | DB | DW | RESB | RESD | RESW deriving (Eq,Show)

data Reg = R8 { r8 :: Reg8 } | R16 { r16 :: Reg16 } | R32 { r32 :: Reg32 } deriving (Eq,Show)
data Reg8 = AH | AL | BH | BL | CH | CL | DH | DL deriving (Eq,Show)
data Reg16 = AX | BX | CX | DX | SP | BP | SI | DI deriving (Eq,Show)
data Reg32 = EAX | EBX | ECX | EDX | ESP | EBP | ESI | EDI deriving (Eq,Show)

data Mem = M8 { m8 :: Mem8 } | M16 { m16 :: Mem16 } | M32 { m32 :: Mem32 } | MU { mu :: MemUnknown } deriving (Eq,Show)
data Mem8 = Byte { b::String } | R8M { r8m::Reg8 } deriving (Eq,Show)
data Mem16 = Word { w::String } | R16M { r16m::Reg16 } deriving (Eq,Show)
data Mem32 = Dword { d::String } | R32M { r32m::Reg32 } deriving (Eq,Show)
type MemUnknown = String

data Arg  = M { m::Mem } | R { r::Reg } | I { i::Imm } deriving (Eq,Show)

data Imm = ImmC Char | ImmI Integer | ImmV String deriving (Eq,Show)

data Arg2 = RR8  Reg8  Reg8  | --11
            RR16 Reg16 Reg16 | --11
            RR32 Reg32 Reg32 | --11
            RM8  Reg8  Mem8  | --00
            MR8  Mem8  Reg8  | --00
            RM16 Reg16 Mem16 | --00
            MR16 Mem16 Reg16 | --00
            RM32 Reg32 Mem32 | --00
            MR32 Mem32 Reg32 | --00
            MUR  MemUnknown Reg|
            RMU  Reg MemUnknown|
            RI   Reg   Imm   deriving (Eq,Show)
                   
data Instruction = I2 InstructionWith2Args Arg2 | I1 InstructionWith1Arg Arg | I0 InstructionWith0Arg | EmptyInstruction | ToDelete  deriving (Eq,Show)

data InstructionWith2Args = Mov | Add | Sub | Cmp deriving (Eq,Show)

data InstructionWith1Arg = Jmp | Inc | Dec | Rep deriving (Eq,Show)

data InstructionWith0Arg = Scasb | Movsb | Cmpsb | Lodsb deriving (Eq,Show)

data SectionTokens = ST { sText :: Maybe (Map Int String),
                          sData :: Maybe (Map Int String),
                          sBss  :: Maybe (Map Int String) } deriving (Eq,Show)

main :: IO()
main = do
  args <- getArgs
  run (args!!0)

  -- case args of
  --   [x] -> run (args!!0)
  --   [x,y] -> case y of
  --              "-s" -> 

run :: FilePath -> IO ()
run f = do
  file <- readFile f
  let m = extractMacros file
  let lineS' = getSource file
  let secs = (getSections lineS')
  let lineS = (maybe (fromList []) id $ sData secs) `union` (maybe (fromList []) id $ sBss secs) `union` (Data.Map.mapKeys (\k-> k+(fst$findMin $ maybe (fromList []) id (sText secs))) $ getSource $ replaceMacro m (unlines $ elems $ maybe (fromList []) id (sText secs)))  
  symT<-generateSymTabWithAddresses lineS
  opT<- generateOpTab lineS
  litT<-generateLitTab (instructionList opT) symT
  let insOps = newIns $ Data.Map.map (\x-> opCodeGen x symT) (instructionList opT)
  let symOps = Data.Map.map (\a-> case a of
                                EmptySymRow -> ""
                                SymRow a1 a2 a3 a4 a5 a6 a7 a8 -> a8 ) (entries $ symT)
  let lstF = union insOps symOps
  zipWithM_ (\(x,y) z-> putStrLn $ (show x ++ " " ++ y) ++ (replicate (35 - length (show x ++ " " ++ y)) ' ') ++ z ) (assocs lstF) (elems lineS)
  
  
getSizeIns :: String -> Int
getSizeIns str = div (length $ Prelude.filter (\x-> x/='['&& x/=']') str) 2

newIns :: Map Int String -> Map Int String
newIns x = Data.Map.mapWithKey (\k a-> if (a=="") then "" else ((replicate (8-length (j k)) '0')++ (j k) ++ " " ++ a)) x
  where
    j h = (Prelude.map toUpper $ showHex (Data.Map.foldr (\m n-> getSizeIns m + n) 0 (Data.Map.filterWithKey (\k' a'-> k' < h) x)) "")
    
generateLitTab :: Monad m => Map Int Instruction -> SymbolTable -> m LiteralTable
generateLitTab insList symTab = if allLiteralsExist then return litTab else fail "Literal out of scope"
  where
    litTab = LiteralTable $ Data.Map.map (\a-> riToImm a) onlyRI 
    riToImm (I2 i (RI x y)) = y
    onlyRI = Data.Map.filter (\a-> case a of
                                 I2 i (RI x y) -> True
                                 _      -> False) insList
    onlyImmV = Data.Map.filter (\a-> case a of
                                       ImmV x -> True
                                       _ -> False) (literals litTab)
    allLiteralsExist = and $ elems $ Data.Map.map (\(ImmV s)-> isJust $ Data.Map.lookup s (entryNo symTab)) onlyImmV

generateOpTab :: Monad m => Map Int String -> m OpCodeTable
generateOpTab lineS = do
  let st = getSections lineS
  let textI = liftM (mapParser (\i-> myTry (whiteSpace >> instructionParser) <|> myTry (many (char '\t') >> eol >> return EmptyInstruction) <|> myTry (whiteSpace >> reserved "section .text" >> return EmptyInstruction) <* eol <|> myTry (labelParser 4 >> return EmptyInstruction) <|> myTry (globalParser 4 >> return EmptyInstruction) <|> myTry (externParser 4 >> return EmptyInstruction) <|> (many anyChar >> fail "Invalid Instruction!!!!!!!!!!!!!!!!"))) (sText st)
  let textI2 = maybe empty id textI
  let textI3 = Data.Map.map (\a-> either (\x-> error (show x)) id a) textI2
  let textI4 = Data.Map.filter (/=ToDelete) textI3
  return $ OpCodeTable { instructionList = textI4,
                         instructionSize = empty,
                         opCode = empty }

toBssCodes :: Int -> Int -> String
toBssCodes x s = addr ++ " <res " ++ size ++">"
  where
    size = replicate (8-length (show s)) '0' ++ show s
    addr = replicate (8-length h) '0' ++h 
    h=(Prelude.map toUpper $ showHex x "")

myhexNByte :: Int ->Int -> String
myhexNByte n s = Prelude.map toUpper $ let h = showHex s ""
               in (replicate ((n*2)-(length h)) '0') ++ h

toDataCodes :: Int -> Int -> [Int] -> String
toDataCodes byte x s = addr ++ " " ++ (concat $ Prelude.map (\t-> myhexNByte byte t) s)
  where
    addr = replicate (8-length h) '0' ++h 
    h=(Prelude.map toUpper $ showHex x "")

generateSymTabWithAddresses :: Monad m => Map Int String -> m SymbolTable
generateSymTabWithAddresses lineS = do
  symT <- generateSymTab lineS
  let newBssSymT x = Data.Map.mapWithKey (\k a-> a { address = toBssCodes (Data.Map.foldr (\a' b'-> (maybe 0 id (sizeM a'))+b' ) 0 (Data.Map.filterWithKey (\k' a'-> k'<lineNo a) x)) (maybe 0 id (sizeM a))}) x
  let newDataSymT x = Data.Map.mapWithKey (\k a-> a { address = toDataCodes (maybe 0 id (getByteSize $ byteValue a)) (Data.Map.foldr (\a' b'-> (maybe 0 id (sizeM a'))+b' ) 0 (Data.Map.filterWithKey (\k' a'-> k'<lineNo a) x)) (maybe [] id (value a))}) x
  let bssSyms = Data.Map.filter (\a-> case a of
                                    SymRow a1 a2 a3 a4 a5 BSS a7 a8 -> True
                                    _ -> False) (entries $ symT)
  let dataSyms = Data.Map.filter (\a-> case a of
                                    SymRow a1 a2 a3 a4 a5 DATA a7 a8 -> True
                                    _ -> False) (entries $ symT)
  let restSyms = ((entries $ symT) \\ bssSyms) \\ dataSyms
  let dataWithAddress = SymTab (union (union (newBssSymT bssSyms) (newDataSymT dataSyms)) restSyms) (entryNo $ symT)
  return dataWithAddress

generateSymTab :: Monad m => Map Int String -> m SymbolTable
generateSymTab lineS = do
  let st = getSections lineS
  let dataS = maybe empty id (liftM (mapParserSymRow dataSymRowParser) (sData st))
  let dataS2 = Data.Map.map (\a-> either (\x-> error (show x)) id a) dataS
  let bssS = maybe empty id (liftM (mapParserSymRow bssSymRowParser) (sBss st))
  let bssS2 = Data.Map.map (\a-> either (\x-> error (show x)) id a) bssS  
  let textS = maybe empty id (liftM (Data.Map.filter (/= Right ToDeleteSym)) $ liftM (mapParser textSymRowParser) (sText st))
  let textS2 = Data.Map.map (\a-> either (\x-> error (show x)) id a) textS
  return $ SymTab (union (union textS2 bssS2) dataS2) (fromList $ Prelude.map (\x->(varName x,lineNo x)) $ Prelude.filter (\x-> not (x==ToDeleteSym || x==EmptySymRow)) $ elems (union (union textS2 bssS2) dataS2))

getAddressFromSymTab :: SymbolTable -> String -> String
getAddressFromSymTab symT var = fst $ break (==' ') $ (address (maybe EmptySymRow id (Data.Map.lookup varKey (entries symT))))
  where
    varKey = maybe (error "Variable not Found!!!!!") id (Data.Map.lookup var (entryNo symT)) 
 
opCodeGen :: Instruction -> SymbolTable -> String
opCodeGen ins symT = case ins of
                 I2 Mov arg2 -> (movArgOpCode687 arg2 symT) ++ (movArgOpCode40 arg2 symT)
                 I2 Cmp arg2 -> (cmpArgOpCode arg2 symT)
                 I0 Scasb -> "AE"
                 I0 Movsb -> "A4"
                 I0 Lodsb -> "AC"
                 I0 Cmpsb -> "A6"
                 EmptyInstruction -> ""
                 _ -> error "Invalid instruction Found!!!"

cmpArgOpCode :: Arg2 -> SymbolTable -> String
cmpArgOpCode arg2 symT = case arg2 of
                        RR8 x y  -> "3A"
                        RR16 x y -> "3B"
                        RR32 x y -> "3B"
                        RM8 x y  -> "3A"
                        RM16 x y -> "3B"
                        RM32 x y -> "3B"
                        MR8 x y  -> "38"
                        MR16 x y -> "39"
                        MR32 x y -> "39"
                        RI  r i  -> case r of
                                      R8 r' -> if r'==AL then "3C" else "80"
                                      R16 r' -> if r'==AX then "3D" else "81"
                                      R32 r' -> if r'==EAX then "3D" else "81"
                        MUR m r  -> case r of
                                      R8 x -> opCodeGen (I2 Cmp (MR8 (Byte m) x)) symT
                                      R16 x -> opCodeGen (I2 Cmp (MR16 (Word m) x)) symT
                                      R32 x -> opCodeGen (I2 Cmp (MR32 (Dword m) x)) symT                           
                        RMU r m  -> case r of
                                      R8 x -> opCodeGen (I2 Cmp (MR8 (Byte m) x)) symT
                                      R16 x -> opCodeGen (I2 Cmp (MR16 (Word m) x)) symT
                                      R32 x -> opCodeGen (I2 Cmp (MR32 (Dword m) x)) symT                           

                      
movArgOpCode687 :: Arg2 -> SymbolTable -> String
movArgOpCode687 arg2 symT = case arg2 of
                        RR8 x y  -> "88"
                        RR16 x y -> "6689"
                        RR32 x y -> "89"
                        RM8 x y  -> if x==AL then "A0" else "8A"
                        RM16 x y -> if x==AX then "66A1" else "668B"
                        RM32 x y -> case y of
                                      R32M r -> "89"
                                      _ -> if x==EAX then "A1" else "8B"
                        MR8 x y  -> if y==AL then "A2" else "88"
                        MR16 x y -> if y==AX then "66A3" else "6689"
                        MR32 x y -> case x of
                                      R32M r -> "89"
                                      _ -> if y==EAX then "A3" else "89"
                        RI r i   -> case r of
                                      R8 x -> (addHex "B0" (b2Hex ("0" ++ (getStringFromRegBin (R8 x))))) ++
                                        case i of
                                          ImmI t -> myhexNByte 1 (fromInteger t :: Int)
                                          ImmC t -> myhexNByte 1 (ord t)
                                          ImmV t -> getAddressFromSymTab symT t
                                      R16 x -> ("66" ++ addHex "B8" (b2Hex ("0" ++ (getStringFromRegBin (R16 x))))) ++
                                        case i of
                                          ImmI t -> myhexNByte 2 (fromInteger t :: Int)
                                          ImmC t -> myhexNByte 2 (ord t)
                                          ImmV t -> getAddressFromSymTab symT t                                        
                                      R32 x -> (addHex "B8" (b2Hex ("0" ++ (getStringFromRegBin (R32 x))))) ++
                                        case i of
                                          ImmI t -> myhexNByte 4 (fromInteger t :: Int)
                                          ImmC t -> myhexNByte 4 (ord t)
                                          ImmV t -> getAddressFromSymTab symT t                                        
                        MUR m r  -> case r of
                                      R8 x -> opCodeGen (I2 Mov (MR8 (Byte m) x)) symT
                                      R16 x -> opCodeGen (I2 Mov (MR16 (Word m) x)) symT
                                      R32 x -> opCodeGen (I2 Mov (MR32 (Dword m) x)) symT 
                        RMU r m  -> case r of
                                      R8 x -> opCodeGen (I2 Mov (RM8 x (Byte m))) symT
                                      R16 x -> opCodeGen (I2 Mov (RM16 x (Word m))) symT
                                      R32 x -> opCodeGen (I2 Mov (RM32 x (Dword m))) symT

movArgOpCode40 :: Arg2 -> SymbolTable -> String
movArgOpCode40 arg2 symT = case arg2 of
                        RR8 x y -> b2Hex $ "11" ++ getStringFromRegBin (R8 y) ++ getStringFromRegBin (R8 x)
                        RR16 x y -> b2Hex $ "11" ++ getStringFromRegBin (R16 y) ++ getStringFromRegBin (R16 x)
                        RR32 x y -> b2Hex $ "11" ++ getStringFromRegBin (R32 y) ++ getStringFromRegBin (R32 x)
                        RM8 x y -> (b2Hex $ if x==AL then "" else "00" ++ getStringFromRegBin (R8 x) ++ "101") ++
                          case y of
                            Byte v -> "["++getAddressFromSymTab symT v++"]"
                            _ -> ""
                        RM16 r m -> (b2Hex $ if r==AX then "" else "00" ++ getStringFromRegBin (R16 r) ++ "101") ++
                           case m of
                             Word v -> "["++getAddressFromSymTab symT v++"]"
                             _ -> ""
                        RM32 x y -> case y of
                                      Dword r -> (b2Hex $ if x==EAX then "" else "00" ++ getStringFromRegBin (R32 x) ++ "101") ++
                                                 "["++getAddressFromSymTab symT r++"]"
                                      R32M r -> b2Hex $ "00" ++ getStringFromRegBin (R32 x) ++ getStringFromRegBin (R32 r) 
                        MR8 x y -> (b2Hex $ if y==AL then "" else "00" ++ getStringFromRegBin (R8 y) ++ "101") ++
                           case x of
                             Byte v -> "["++getAddressFromSymTab symT v++"]"
                             _ -> ""
                        MR16 m r -> (b2Hex $ if r==AX then "" else "00" ++ getStringFromRegBin (R16 r) ++ "101") ++
                           case m of
                             Word v -> "["++getAddressFromSymTab symT v++"]"
                             _ -> ""
                        MR32 x y -> case x of
                                      Dword r -> (b2Hex $ if y==EAX then "" else "00" ++ getStringFromRegBin (R32 y) ++ "101") ++
                                                 "["++getAddressFromSymTab symT r++"]"                          
                                      R32M r -> b2Hex $ "00" ++ getStringFromRegBin (R32 y) ++ getStringFromRegBin (R32 r)
                        RI r i -> ""
                        MUR m r -> case r of
                                      R8 x -> ""
                                      R16 x -> ""
                                      R32 x -> ""
                        RMU r m -> case r of
                                      R8 x -> ""
                                      R16 x -> ""
                                      R32 x -> ""
                                      
myTry = Text.ParserCombinators.Parsec.try

-------------------------------------------------------

data Macro = Mc { mName :: String
                , mArg :: Int
                , mBody :: String
                } deriving (Show,Eq)

extractMacros :: String -> [Macro]
extractMacros cont = extractMacros' $ takeWhile (\x -> head (words x) /= "section") $ Prelude.filter (\x-> (words x) /= []) (lines cont)

extractMacros' :: [String] -> [Macro]
extractMacros' [] = []
extractMacros' cont | (tillEndMacro $ skipTillMacro cont) == [] = (extractMacros' $ myTail $ dropWhile (\x-> head (words x) /= "%endmacro") cont)
                    | otherwise =  (makeMacro (tillEndMacro $ skipTillMacro cont))
                      :(extractMacros' $ tail $ dropWhile (\x-> head (words x) /= "%endmacro") cont)
  where
    tillEndMacro s = takeWhile (\x-> head (words x) /= "%endmacro") s
    skipTillMacro s = dropWhile (\x -> head (words x) /= "%macro") s
    
makeMacro :: [String] -> Macro
makeMacro mm = Mc { mName = (words (head mm))!!1,
                    mArg = read ((words (head mm))!!2) :: Int,
                    mBody = unlines $ tail mm
                  }
  
replaceMacro :: [Macro] -> String -> String
replaceMacro [] s = s
replaceMacro mm st = unlines $ (\x -> checkAndChange mm x ) <$> (lines st)

checkAndChange :: [Macro] -> String -> String
checkAndChange mm ln1 | length ln > 1 = case Prelude.filter (\x -> (head ln) == (mName x) && (length args)== mArg x) mm of
                                          [] -> ln1
                                          e -> init $ Prelude.foldl (\z (x,y)-> subst x y z) (mBody $ head e) (zip args perList)
                      | length ln == 1 = case Prelude.filter (\x -> (head ln) == (mName x) && (mArg x)==0) mm of
                                           [] -> ln1
                                           e -> init $ mBody $ head e
                      | otherwise = ln1
  where
    ln = words ln1
    perList = (Prelude.map (\x-> "%"++show x) [1..])
    args = (splitOn "," (ln!!1))

subst :: String -> String -> String -> String
subst _ _ [] = []
subst newsub (o:ld) (e:st) | e==o = case checkRestStr ld st of
                                      True -> (newsub ++ (subst newsub (o:ld) $ drop (length ld) st))
                                      False -> e:(subst newsub (o:ld) st)
                           | otherwise = e:(subst newsub (o:ld) st)

checkRestStr :: String -> String -> Bool
checkRestStr [] [] = True
checkRestStr _ [] = False
checkRestStr [] _ = True
checkRestStr (l:ld) (s:st) | l==s = checkRestStr ld st
                           | otherwise = False

-------------------------------------------------------

faltuInstructionParser :: Int -> Parser Instruction
faltuInstructionParser i = do
  whiteSpace
  manyTill (noneOf "\n") eol
  return $ EmptyInstruction

textSymRowParser :: Int -> Parser SymbolRow
textSymRowParser i = (myTry (globalParser i) <|> myTry (externParser i) <|> myTry (labelParser i)) <|> faltuParser i

globalParser :: Int -> Parser SymbolRow
globalParser i = do
  whiteSpace >> reserved "global"
  var <- whiteSpace >> Token.identifier lexer
  eol
  return $ SymRow var Nothing Nothing Nothing False GLOBAL i ""

labelParser :: Int -> Parser SymbolRow
labelParser i = do
  var <- whiteSpace >> Token.identifier lexer
  char ':'
  eol
  return $ SymRow var Nothing Nothing Nothing True LABEL i ""

externParser :: Int -> Parser SymbolRow
externParser i = do
  whiteSpace >> reserved "extern"
  var <- whiteSpace >> Token.identifier lexer
  eol
  return $ SymRow var Nothing Nothing Nothing False EXTERN i ""

faltuParser :: Int -> Parser SymbolRow
faltuParser i = do
  whiteSpace
  manyTill (noneOf "\n") eol
  return $ ToDeleteSym

dataSymRowParser :: Int -> Parser SymbolRow
dataSymRowParser i = do
  var <- whiteSpace >> Token.identifier lexer
  byte <- whiteSpace >> byteParser
  val <- whiteSpace >> dataSectionDataParser
  let siz = liftM2 (*) (Just $ length val) (getByteSize byte) 
  return $ SymRow var (Just val) byte siz False DATA i ""

bssSymRowParser :: Int -> Parser SymbolRow
bssSymRowParser i = do
  var <- whiteSpace >> Token.identifier lexer
  byte <- whiteSpace >> byteParser
  val <- whiteSpace >> ((\x-> [read x] :: [Int]) <$> (many1 digit)) <* optional eol 
  let siz = liftM2 (*) (Just $ (\[x]-> x) val) (getByteSize byte) 
  return $ SymRow var (Just val) byte siz True BSS i ""

---------------------------wrapper fxns---------------------

myTail :: [a] -> [a]
myTail x = case x of
             [] -> []
             y -> tail y

addHex :: String -> String -> String
addHex h1 h2 = Prelude.map toUpper $ showHex intVal ""
  where
    getInt x = (\[t]-> fst t) x
    intVal = getInt (readHex h1) + getInt (readHex h2)

getStringFromRegBin :: Reg -> String
getStringFromRegBin reg = (\[t]-> snd t) $ Prelude.filter (\(x,y)-> x==reg) regBin

toHex :: String -> Char
toHex "0000" = '0'
toHex "0001" = '1'
toHex "0010" = '2'
toHex "0011" = '3'
toHex "0100" = '4'
toHex "0101" = '5'
toHex "0110" = '6'
toHex "0111" = '7'
toHex "1000" = '8'
toHex "1001" = '9'
toHex "1010" = 'A'
toHex "1011" = 'B'
toHex "1100" = 'C'
toHex "1101" = 'D'
toHex "1110" = 'E'
toHex "1111" = 'F'

toBin :: Char -> String
toBin '0' = "0000"
toBin '1' = "0001"
toBin '2' = "0010"
toBin '3' = "0011"
toBin '4' = "0100"
toBin '5' = "0101"
toBin '6' = "0110"
toBin '7' = "0111"
toBin '8' = "1000"
toBin '9' = "1001"
toBin 'A' = "1010"
toBin 'B' = "1011"
toBin 'C' = "1100"
toBin 'D' = "1101"
toBin 'E' = "1110"
toBin 'F' = "1111"

h2Bin :: String -> String
h2Bin str = concat $ Prelude.map toBin $ str

b2Hex :: String -> String
b2Hex str = Prelude.map toHex $ chunksOf 4 str

byteParser :: Parser (Maybe ByteValue)
byteParser = (whiteSpace >> (reserved "dd") *> (return $ Just DD))
  <|> (whiteSpace >> (reserved "db") *> (return $ Just DB))
  <|> (whiteSpace >> (reserved "dw") *> (return $ Just DW))
  <|> (whiteSpace >> (reserved "resb") *> (return $ Just RESB))
  <|> (whiteSpace >> (reserved "resw") *> (return $ Just RESW))
  <|> (whiteSpace >> (reserved "resd") *> (return $ Just RESD))

getByteSize :: Maybe ByteValue -> Maybe Int
getByteSize Nothing = Nothing
getByteSize (Just  DB) = Just 1
getByteSize (Just  DW) = Just 2
getByteSize (Just  DD) = Just 4
getByteSize (Just  RESB) = Just 1
getByteSize (Just  RESW) = Just 2
getByteSize (Just  RESD) = Just 4

dataSectionDataParser :: Parser [Int]
dataSectionDataParser = concat <$> (sepBy1 (whiteSpace >> dataSectionArgParser <* whiteSpace) (char ','))
  where
    dataSectionArgParser = (\x->[read x]::[Int]) <$> (many1 digit) <|> (Prelude.map ord) <$> ((strParser (many (noneOf "\""))))

------------------------------Generic Parsers---------------

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDef
eol :: Parser ()
eol = void (char '\n') <|> eof
reserved :: String -> Parser ()
reserved  = Token.reserved lexer
parens :: Parser a -> Parser a
parens = Token.parens lexer
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer
brackets :: Parser a -> Parser a
brackets p = between (Token.symbol lexer "[") (Token.symbol lexer "]") p
apostrophe :: Parser a -> Parser a
apostrophe p = between (Token.symbol lexer "'") (Token.symbol lexer "'") p
strParser :: Parser a -> Parser a
strParser p = between (Token.symbol lexer "\"") (Token.symbol lexer "\"") p
parser :: Parser a -> String -> Either ParseError a
parser p x = parse p "" x

mapParser :: (Int -> Parser a) -> Map Int String -> Map Int (Either ParseError a)
mapParser p x = Data.Map.mapWithKey (\i s-> parse (p i) "" s) x

mapParserSymRow :: (Int -> Parser SymbolRow) -> Map Int String -> Map Int (Either ParseError SymbolRow)
mapParserSymRow p x = union s m
  where
    m=Data.Map.mapWithKey (\k a-> parse ((p k) <|> (eol >> return EmptySymRow))"" a) (deleteMin x)
    s=(\(k,a)-> fromList [(k,Right EmptySymRow)]) $ findMin x

instructionParser :: Parser Instruction
instructionParser = myTry (movParser <* eol) <|> myTry (cmpParser <* eol) <|> myTry (cmpsbParser <* eol) <|> myTry (movsbParser <* eol) <|>myTry (lodsbParser <* eol) <|> myTry (scasbParser <* eol)
movParser :: Parser Instruction
movParser =
  do
    whiteSpace
    reserved "mov"
    whiteSpace
    arg2<-arg2Parser
    return $ I2 Mov arg2

cmpParser :: Parser Instruction
cmpParser =
  do
    whiteSpace
    reserved "cmp"
    whiteSpace
    arg2<-arg2Parser
    return $ I2 Cmp arg2

scasbParser :: Parser Instruction
scasbParser =
  do
    whiteSpace
    reserved "scasb"
    whiteSpace
    return $ I0 Scasb

movsbParser :: Parser Instruction
movsbParser =
  do
    whiteSpace
    reserved "movsb"
    whiteSpace
    return $ I0 Movsb

lodsbParser :: Parser Instruction
lodsbParser =
  do
    whiteSpace
    reserved "cmpsb"
    whiteSpace
    return $ I0 Lodsb

cmpsbParser :: Parser Instruction
cmpsbParser =
  do
    whiteSpace
    reserved "cmpsb"
    whiteSpace
    return $ I0 Cmpsb


arg2Parser :: Parser Arg2
arg2Parser =
  do
    whiteSpace
    x<-argParser
    whiteSpace
    _<-Token.comma lexer
    whiteSpace
    y<-argParser
    case (x,y) of
      (R r,I i) -> return $ RI r i
      (R r,M (MU m)) -> return $ RMU r m
      (R r,M m) -> case (r,m) of
                     (R8 r8,M8 m8) -> return $ RM8 r8 m8
                     (R16 r16,M16 m16) -> return $ RM16 r16 m16
                     (R32 r32,M32 m32) -> return $ RM32 r32 m32
                     _               -> fail "Size MisMatch!!!\n"
      (M (MU m),R r) -> return $ MUR m r                     
      (M m,R r) ->  case (m,r) of
                     (M8 m8,R8 r8) -> return $ MR8 m8 r8
                     (M16 m16,R16 r16) -> return $ MR16 m16 r16
                     (M32 m32,R32 r32) -> return $ MR32 m32 r32
                     _               -> fail "Size MisMatch!!!\n"                     
      (R r1,R r2) -> case (r1,r2) of
                       (R32 e1,R32 e2) -> return $ RR32 e1 e2
                       (R16 e1,R16 e2) -> return $ RR16 e1 e2
                       (R8  e1,R8  e2) -> return $ RR8 e1 e2
                       _               -> fail "Size MisMatch!!!\n"
      _               -> fail "Size MisMatch!!!\n"         

argParser :: Parser Arg
argParser = regParser <|> memParser <|> (intParser <|> charParser <|> varParser) <|> memUnknownParser
  where
    mapStringParser = Data.Map.mapWithKey (\k a-> reserved k >> return (R a)) regTypeTup
    regParser = Data.Map.foldl' (<|>) ((!) mapStringParser "sp") mapStringParser
    charParser = (\x-> I (ImmC x)) <$> (apostrophe alphaNum)
    intParser = (\x-> I (ImmI x)) <$> (Token.integer lexer)
    varParser = (\x-> I (ImmV x)) <$> (Token.identifier lexer)
    -- hex8Parser = (\x-> I (ImmH8 x)) <$> ((reserved "0x" >> count 2 hexDigit) <|> (count 2 hexDigit <* char 'h'))
    memParser = myTry ((\x-> M $ M8 $ Byte x) <$> memParser' "byte") <|> myTry ((\x-> M $ M16 $ Word x) <$> memParser' "word") <|> myTry ((\x-> M $ M32 $ Dword x) <$> memParser' "dword") <|> myTry ((\(R x)-> case x of
                                                                                                                                                                                                          R32 y -> M $ M32 $ R32M y
                                                                                                                                                                                                          R16 y -> M $ M16 $ R16M y
                                                                                                                                                                                                          R8 y -> M $ M8 $ R8M y) <$> brackets regParser)
    memParser' x = reserved x >> (brackets $ Token.identifier lexer)
    memUnknownParser = (\x-> M (MU x)) <$> brackets (Token.identifier lexer)

------------------------------Scrape data---------------

getSource :: String -> Map Int String
getSource str = fromList $ zip [1..] (lines str)

getSections :: Map Int String -> SectionTokens
getSections linSource = ST { sData = toMaybeMap $ getSectionWithNo 0,
                             sText = toMaybeMap $ getSectionWithNo 1,
                             sBss  = toMaybeMap $ getSectionWithNo 2 }
  where
    sectionIndexes = keys $ Data.Map.filter (\x-> elem (words x) sections) linSource
    sectionRanges = Prelude.zipWith (\x y-> (x,y-1)) sectionIndexes (myTail (sectionIndexes ++ [Data.Map.size linSource + 1]))
    getSectionWithNo z = Prelude.filter (\(x,y)-> ((words $ linSource Data.Map.! x)) == sections!!z) sectionRanges
    toMaybeMap xs = case xs of
                         [] -> Nothing
                         [x]  -> Just $ uncurry (\i j-> Data.Map.filterWithKey (\k a-> k>=i && k<=j) linSource) x
                         _   -> fail "Multiple Declarations of a Section!!!"
             
---------------------------------Immutables-------------------

regBin :: [(Reg,String)]
regBin = [(R32 EAX,"000"),(R8 AL,"000"),(R16 AX,"000"),(R8 CL,"001"),(R16 CX,"001"),(R32 ECX,"001"),(R8 DL,"010"),(R16 DX,"010"),(R32 EDX,"010"),(R8 BL,"011"),(R16 BX,"011"),(R32 EBX,"011"),(R8 AH,"100"),(R16 SP,"100"),(R32 ESP,"100"),(R8 CH,"101"),(R16 BP,"101"),(R32 EBP,"101"),(R8 DH,"110"),(R16 SI,"110"),(R32 ESI,"110"),(R8 BH,"111"),(R16 DI,"111"),(R32 EDI,"111")]

sections :: [[String]]
sections = [["section", ".data"],["section", ".text"],["section", ".bss"]]

regTypeTup :: Map String Reg
regTypeTup = fromList [("ah", R8  AH),
                       ("al", R8  AL),
                       ("bh", R8  BH),
                       ("bl", R8  BL),
                       ("ch", R8  CH),
                       ("cl", R8  CL),
                       ("dh", R8  DH),
                       ("dl", R8  DL),
                       ("ax", R16 AX),
                       ("bx", R16 BX),
                       ("cx", R16 CX),
                       ("dx", R16 DX),
                       ("sp", R16 SP),
                       ("bp", R16 BP),
                       ("di", R16 DI),
                       ("si", R16 SI),
                       ("eax",R32 EAX),
                       ("ebx",R32 EBX),
                       ("ecx",R32 ECX),
                       ("edx",R32 EDX),
                       ("esp",R32 ESP),
                       ("ebp",R32 EBP),
                       ("edi",R32 EDI),
                       ("esi",R32 EDI)]

languageDef :: LanguageDef ()
languageDef = emptyDef { Token.identStart = letter <|> satisfy (=='_')
                       , Token.identLetter = alphaNum
                       , Token.reservedNames = []
                       , Token.caseSensitive = True
                       }

-------------------------------Scratched Code------------------

                           -- ["section"
                           --                     ,"global"
                           --                     ,"main"
                           --                     ,"mov"
                           --                     ,"eax"
                           --                     ,"ebx"
                           --                     ,"ecx"
                           --                     ,"edx"
                           --                     ,"ah"
                           --                     ,"al"
                           --                     ,"bh"
                           --                     ,"bl"
                           --                     ,"ch"
                           --                     ,"cl"
                           --                     ,"dh"
                           --                     ,"dl"
                           --                     ,"ax"
                           --                     ,"bx"
                           --                     ,"cx"
                           --                     ,"dx"]

-- regStrBin :: Map String String
-- regStrBin = fromList [("eax","000"),("al","000"),("ax","000"),("cl","001"),("cx","001"),("ecx","001"),("dl","010"),("dx","010"),("edx","010"),("bl","011"),("bx","011"),("ebx","011"),("ah","100"),("sp","100"),("esp","100"),("ch","101"),("bp","101"),("bsp","101"),("dh","110"),("si","110"),("esi","110"),("bh","110"),("di","110"),("edi","110")]

-- reg32 :: [String]
-- reg32 = ["eax","ebx","ecx","edx","esp","ebp","esi","edi"]

-- reg16 :: [String]
-- reg16 = ["ax","bx","cx","dx","sp","bp","di","si"]

-- reg8 :: [String]
-- reg8 = ["ah","al","bh","bl","ch","cl","dh","dl"]


-- subParser :: Parser Instruction
-- subParser =
--   do
--     whiteSpace
--     reserved "sub"
--     whiteSpace
--     arg2<-arg2Parser
--     return $ Sub arg2

-- addParser :: Parser Instruction
-- addParser =
--   do
--     whiteSpace
--     reserved "add"
--     whiteSpace
--     arg2<-arg2Parser
--     return $ Add arg2


-- bssSectionParser :: Parser SymbolTable
-- bssSectionParser = do
--   whiteSpace >> reserved "section"
--   whiteSpace >> reserved ".bss"
--   symrows <- many bssSymRowParser
--   return $ SymTab (fromList symrows)

-- bssSymRowParser :: Parser (String,SymbolRow)
-- bssSymRowParser = do
--   var <- whiteSpace >> Token.identifier lexer
--   byte <- whiteSpace >> byteParser
--   val <- whiteSpace >> ((\x-> [read x] :: [Int]) <$> (many1 digit)) <* optional eol 
--   let siz = liftM2 (*) (Just $ length val) (getByteSize byte) 
--   return $ (var, SymRow var (Just val) byte siz False BSS)

-- dataSectionParser :: Parser SymbolTable
-- dataSectionParser = do
  -- whiteSpace >> reserved "section"
  -- whiteSpace >> reserved ".data"
  -- symrows <- many dataSymRowParser
  -- return $ SymTab (fromList symrows)

-- liftM (mapParserSymRow dataSymRowParser) (sData st)
-- liftM (mapParserSymRow bssSymRowParser) (sBss st)
-- liftM (mapParser (\i-> myTry (whiteSpace >> movParser) <|> myTry (many (char '\t') >> eol >> return EmptyInstruction) <|> myTry (whiteSpace >> reserved "section .text" >> return EmptyInstruction) <* eol <|> faltuInstructionParser i)) (sText st)
-- liftM (Data.Map.filter (/= Right ToDeleteSym)) $ liftM (mapParser textSymRowParser) (sText st)
