module

public import Init.Data.ByteArray.Lemmas

@[expose] public section

-- Keep byte arrays printable inside source syntax and runtime stores.
deriving instance Repr for ByteArray
