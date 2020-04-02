import Data.Vect

{- Data scheme for storage - storage either string or int, or combination of them -}
infixr 5 .+. -- sheme combining operator .+. with right assotiativity and priority 5 (like == and /=)
data Schema = SString
            | SInt
            | (.+.) Schema Schema

-- Converts schema to corresponding type
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
     constructor MkData
     schema: Schema
     size: Nat
     items: Vect size (SchemaType schema)

{- Add value to the store -}
addToStore : (store: DataStore) -> (item: SchemaType (schema store)) -> DataStore
addToStore (MkData schema size items) item = MkData schema _ $ addToData items
  where
    addToData : Vect oldSize (SchemaType schema) -> Vect (S oldSize) (SchemaType schema)
    addToData [] = [item]
    addToData (x :: xs) = x :: addToData xs

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (item1, item2) = display item1 ++ ", " ++ display item2

{- Get value from the store -}
getEntry : (pos: Integer) -> (store: DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              Just id => Just (display (index id (items store)) ++ "\n", store)

{- Object model for all console commands -}
data Command : Schema -> Type where
  SetSchema : (newSchema: Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  Quit : Command schema

{- Converts list of types to schema -}
parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) = case xs of
                                    [] => Just SString
                                    _  => case parseSchema xs of
                                               Nothing => Nothing
                                               Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs) = case xs of
                                 [] => Just SInt
                                 _  => case parseSchema xs of
                                            Nothing => Nothing
                                            Just xs_sch => Just (SInt .+. xs_sch)
parseSchema _ = Nothing


{- Changes schema of the storage only if it is empty -}
setSchema : (store: DataStore) -> (newSchema: Schema) -> Maybe DataStore
setSchema store newSchema = case size store of
                                 Z => Just $ MkData newSchema _ []
                                 S k => Nothing

{- Inner function for parseBySchema -}
parsePrefix : (schema: Schema) -> (input: String) -> Maybe (SchemaType schema, String)
parsePrefix SString input = case unpack input of
                                 [] => Nothing
                                 ('"' :: xs) => case span (/= '"') xs of
                                                     (quoted, '"' :: rest) => Just (pack quoted, ltrim $ pack rest)
                                                     _ => Nothing
                                 _ => Nothing
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schema1 .+. schema2) input =
  case parsePrefix schema1 input of
    Nothing => Nothing
    Just (l_val, input') =>
         case parsePrefix schema2 input' of
              Nothing => Nothing
              Just (r_val, input'') => Just ((l_val, r_val), input'')

{- Parses user's input basing on schema -}
parseBySchema : (schema: Schema) -> (input: String) -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Just (res, "") => Just res
                                  Just _         => Nothing
                                  Nothing        => Nothing

{- Parses user's commands -}
parseCommand : (schema: Schema) -> (input: String) -> (rest: String) -> Maybe (Command schema)
parseCommand schema "add" rest = case parseBySchema schema rest of
                                      Nothing => Nothing
                                      Just resTok => Just $ Add resTok
parseCommand schema "get" val = case all isDigit (unpack val) of
                                     False => Nothing
                                     True => Just $ Get $ cast val
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest = case parseSchema (words rest) of
                                         Nothing => Nothing
                                         Just schemaok => Just $ SetSchema schemaok
parseCommand _ _ _ = Nothing

{- Common parsing method -}
parse : (schema: Schema) -> (input: String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd $ ltrim args

{- Function for processing repl input -}
processInput : (store: DataStore) -> (input: String) -> Maybe (String, DataStore)
processInput store input = case parse (schema store) input of
                                Nothing         => Just ("Invalid command\n", store)
                                Just (SetSchema newSchema) => case setSchema store newSchema of
                                                                   Just newStore => Just ("OK\n", newStore)
                                                                   Nothing => Just ("Cant update schema\n", store)
                                Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                                Just (Get pos)  => getEntry pos store
                                Just Quit       => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
