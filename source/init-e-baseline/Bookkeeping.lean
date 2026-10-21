import Guest.Basic

namespace Guest

/-- Canonical baseline runtime pointers, verified against its linked ELF.
The reserved startup page is part of the fixed source initial semantics. -/
def startupHeaders : List Word :=
  [0xa0020018, 0xa0028ff0, 0xa0028ff0, 0x800f0134, 0x800f1000]

end Guest
