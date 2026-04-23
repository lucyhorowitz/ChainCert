import Cultivar.Examples.Complexes
import Cultivar.Boundary.Basis
import Cultivar.SNF.Tactic

#eval canonicalBasisRaw kleinBottleFFC 0
#eval canonicalBasisRaw kleinBottleFFC 1
#eval canonicalBasisRaw kleinBottleFFC 2
#eval (canonicalBasisRaw kleinBottleFFC 1).length
#eval (canonicalBasisRaw kleinBottleFFC 0).length
#eval (canonicalBasisRaw kleinBottleFFC 2).length

#snf (boundaryMatrix triangleFFC 1)       -- should print Sage SNF output

/-- Smoke test: `snf` tactic on an FFC-derived-dim matrix (non-literal `Fin`). -/
example : True := by
  snf (boundaryMatrix triangleFFC 1)
  trivial
