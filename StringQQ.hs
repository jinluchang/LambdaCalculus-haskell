module StringQQ where

import Language.Haskell.TH
import Language.Haskell.TH.Quote

stringQQ :: QuasiQuoter
stringQQ = QuasiQuoter
    { quoteExp = return . LitE . stringL . trimLeadingNewline . removeCRs
    , quotePat = return . LitP . stringL . trimLeadingNewline . removeCRs
    , quoteType = undefined
    , quoteDec = undefined }
  where
    removeCRs = filter (/= '\r')
    trimLeadingNewline ('\n':xs) = xs
    trimLeadingNewline xs = xs
