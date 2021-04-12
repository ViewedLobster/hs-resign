module Parse (
    runParse,
    Parser
) where

import Data.Word (Word8, Word16)
import Data.Bits
import Data.List
import Control.Applicative
import Control.Monad

type Bytes = [Word8]

newtype Parser a = Parser ( Bytes -> [(a, Bytes)] )

instance Functor Parser where
    fmap = liftM

instance Applicative Parser where
    pure a = Parser (\ws -> [(a, ws)])
    (<*>) = ap

runParse (Parser f) = f

instance Monad Parser where
    -- f :: a -> Parser b
    -- (>>=) :: Parser a -> (a -> Parser b) -> Parser b
    m >>= f = Parser (\ws -> let l = runParse m ws
                                 f' (a, ws') = runParse (f a) ws'
                             in l >>= f')

-- Failed/empty parse
empt :: Parser a
empt = Parser (\_ -> [])

-- Choice
p <+> p' = Parser (\ws -> runParse p ws ++ runParse p' ws)

-- Biased choice: pick first one if success
p </> p' = Parser (\ws -> let res = runParse p ws
                          in case res of
                                  (r:rs) -> res
                                  _      -> runParse p' ws)

-- Optional parser
optl :: Parser a -> Parser (Maybe a)
optl p = (liftM Just p) </> (return Nothing)


-- Filtering
filtr :: (a -> Bool) -> Parser a -> Parser a
filtr pred parse = do
    res <- parse
    if pred res then return res
                else empt


-- Get byte
byte :: Parser Word8
byte = Parser itmIntern

itmIntern (w:ws) = [(w, ws)]
itmIntern _      = []


-- Get predetermined byte
lit :: Word8 -> Parser Word8
lit c = filtr (c ==) byte


-- Get predetermined byte sequence
byteSeq :: [Word8] -> Parser [Word8]
byteSeq (c:cs) = do
    r <- lit c
    rs <- byteSeq cs
    return (r:rs)
byteSeq _     = return []


-- Get n bytes
bytes :: Int -> Parser [Word8]
bytes n = do
    if n == 0 then return []
    else do
        r <- byte
        rs <- bytes (n - 1)
        return (r:rs)


-- TODO might need iterate


uniTag = 0xC0 :: Word8 -- Universal tag mask

tagInteger      = 2 :: Int
tagBitString    = 3 :: Int
tagOctetString  = 4 :: Int
tagNull         = 5 :: Int
tagOid          = 6 :: Int
tagSeq          = 16 :: Int
tagSet          = 17 :: Int

tagPrintableString  = 19 :: Int
tagT61String        = 20 :: Int
tagIA5String        = 22 :: Int
tagUTCTime          = 23 :: Int


--class ASN1 asn1 where
--    datlen :: ans1 -> Int
--    dat :: asn1 -> [Word8]

data ASN1 = ASN1Null
          | ASN1Integer Integer
          | ASN1Oid [Int]
    deriving (Eq, Show)

data TagClass = Universal
              | Application
              | ContextSpecific
              | Private
    deriving (Eq, Show)

data Tag = TagInteger
         | TagBitString
         | TagOctetString
         | TagNull
         | TagOid
         | TagSeq
         | TagSet
         | TagPrintableString
         | TagT61String
         | TagIA5String
         | TagUTCTime
         | TagOther TagClass Int
    deriving (Eq, Show)

data DerId = DerId TagClass Int
    deriving (Eq, Show)

tagClassMask = 0xC0 :: Word8

tagClass b = case ((b .&. tagClassMask) `shiftR` 6) of 
    v | v == 0 -> Universal
      | v == 1 -> Application
      | v == 2 -> ContextSpecific
      | v == 3 -> Private


tagFromInt :: Int -> Maybe Tag
tagFromInt b
    | b == tagInteger          = Just TagInteger
    | b == tagBitString        = Just TagBitString
    | b == tagOctetString      = Just TagOctetString
    | b == tagNull             = Just TagNull
    | b == tagOid              = Just TagOid
    | b == tagSeq              = Just TagSeq
    | b == tagSet              = Just TagSet
    | b == tagPrintableString  = Just TagPrintableString
    | b == tagT61String        = Just TagT61String
    | b == tagIA5String        = Just TagIA5String
    | b == tagUTCTime          = Just TagUTCTime
    | otherwise                = Nothing


intFromTag :: Tag -> Int
intFromTag t = case t of
    TagInteger          -> tagInteger
    TagBitString        -> tagBitString
    TagOctetString      -> tagOctetString
    TagNull             -> tagNull
    TagOid              -> tagOid
    TagSeq              -> tagSeq
    TagSet              -> tagSet
    TagPrintableString  -> tagPrintableString
    TagT61String        -> tagT61String
    TagIA5String        -> tagIA5String
    TagUTCTime          -> tagUTCTime


tagIsExtended b = 0x1f .&. b == 0x1f

tagMaskClass b = b .&. (complement tagClassMask)

extendedMore b = (0x80 .&. b) > 0
maskExtendedMore = (.&.) (complement 0x80)

derTagExtendedBytes = do
    b <- byte
    if extendedMore b then do
        bs <- derTagExtendedBytes
        return (b:bs)
    else return [b]

derTagExtended :: Parser Int
derTagExtended = liftM (foldl' accum 0) derTagExtendedBytes
    where accum acc b = (acc `shiftL` 7) .|. (fromIntegral (maskExtendedMore b))
    

derId :: Parser DerId
derId = do
    b <- byte
    let tc = tagClass b in
        if tagIsExtended b then do 
            i <- derTagExtended
            return (DerId tc i)
        else do
            return (DerId tc (fromIntegral (tagMaskClass b)))

lenOctetsToInt :: [Word8] -> Int
lenOctetsToInt = foldl' accum 0
    where accum acc b = (acc `shiftL` 8) .|. (fromIntegral b)

derLen :: Parser Int
derLen = do
    b <- byte
    if b .&. 0x80 == 0 then
        return (fromIntegral b)
    else
        let lenlen = fromIntegral (b .&. (complement 0x80))
        in do
            oct <- bytes lenlen
            return (lenOctetsToInt oct)


data DerValue = DerValue DerId Int Bytes
    deriving (Eq, Show)

derValue :: Parser DerValue
derValue = do
    t <- derId
    len <- derLen
    dat <- bytes len
    return (DerValue t len dat)


derCheckedId :: DerId -> Parser DerId
derCheckedId t = filtr (t ==) derId

derCheckedIdValue id = do
    t <- derCheckedId id
    len <- derLen
    dat <- bytes len
    return (DerValue t len dat)


fromIntegerDerOctets :: [Word8] -> Integer
fromIntegerDerOctets (b:bs) =
                       let negative = 0x80 .&. b == 0
                           b' = (complement 0x80) .&. b
                           abspos = foldl' accum 0 (b':bs)
                           absneg = foldl' accum 0 (map complement (b':bs))
                       in if negative then -absneg
                                      else abspos
    where accum acc b = (acc `shiftL` 8) .|. (fromIntegral b)

diu = DerId Universal -- Shorthand

derIdInteger      = diu tagInteger
derIdBitString    = diu tagBitString
derIdOctetString  = diu tagOctetString
derIdNull         = diu tagNull
derIdOid          = diu tagOid
derIdSeq          = diu tagSeq
derIdSet          = diu tagSet

derIdPrintableString  = diu tagPrintableString
derIdT61String        = diu tagT61String
derIdIA5String        = diu tagIA5String
derIdUTCTime          = diu tagUTCTime


derASN1Integer = do
    DerValue t len octs <- derCheckedIdValue derIdInteger
    return (ASN1Integer (fromIntegerDerOctets octs))

derASN1Null = do
    byteSeq [0x05, 0x00]
    return ASN1Null

-- TODO bit string

eof :: Parser ()
eof = do
    b <- optl byte
    case b of
        Just _ -> empt
        _      -> return ()

derOidValue :: Parser [Int]
derOidValue = do
    b <- byte
    let firstTwo = map fromIntegral [(0xC0 .&. b) `shiftR` 6, (0x3F .&. b)] in do
        rest <- derOidRest
        return (firstTwo ++ rest)

derOidRest :: Parser [Int]
derOidRest = do
    next <- optl derTagExtended
    case next of
        Just v -> do
            more <- derOidRest
            return (v:more)
        Nothing -> return []
            

derASN1Oid = do
    DerValue t len octs <- derCheckedIdValue derIdOid
    case runParse derOidValue octs of -- Run inner parser of der content octets
        [(v, [])] -> return (ASN1Oid v) -- Input of parse must be depleted
        _         -> empt
        
