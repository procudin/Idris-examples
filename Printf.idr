
||| Representing format string as data type
||| "%s=%d" is equal to Str (Lit "=" (Number End))
private
data Format = Number Format
            | Str Format
            | Chr Format
            | Dbl Format
            | Lit String Format
            | End
%name Format fmt

private
PrintfType : Format -> Type
PrintfType (Number fmt) = (i: Int) -> PrintfType fmt
PrintfType (Str fmt) = (s: String) -> PrintfType fmt
PrintfType (Chr fmt) = (c: Char) -> PrintfType fmt
PrintfType (Dbl fmt) = (d: Double) -> PrintfType fmt
PrintfType (Lit lit fmt) = PrintfType fmt
PrintfType End = String

private
toFormat : (xs: List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number $ toFormat chars
toFormat ('%' :: 's' :: chars) = Str $ toFormat chars
toFormat ('%' :: 'c' :: chars) = Chr $ toFormat chars
toFormat ('%' :: 'f' :: chars) = Dbl $ toFormat chars
toFormat ('%' :: chars) = Lit "%" $ toFormat chars
toFormat (c :: chars) = case toFormat chars of
                             (Lit lit chars') => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt
private
printFmt : (fmt: Format) -> (acc: String) -> PrintfType fmt
printFmt (Number fmt) acc = \i => printFmt fmt $ acc ++ show i
printFmt (Str fmt) acc = \s => printFmt fmt $ acc ++ s
printFmt (Chr fmt) acc = \c => printFmt fmt $ strCons c acc
printFmt (Dbl fmt) acc = \d => printFmt fmt $ acc ++ show d
printFmt (Lit lit fmt) acc = printFmt fmt $ acc ++ lit
printFmt End acc = acc

||| Type-safe printf function.
||| Numbers and types of arguments depend on format string.
public
printf : (fmt: String) -> PrintfType $ toFormat $ unpack fmt
printf fmt = printFmt _ ""
