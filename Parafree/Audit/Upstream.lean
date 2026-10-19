import LieRings.Plotkin.GenericPBW
import LieRings.Homological.LieHomology.HopfNaturality
import Parafree.Audit.StandardAxioms

/-! Batch axiom audit; dependency subgraphs are visited only once. -/

#assert_standard_axioms [
  LieRings.PBW.freeModulePBW_commRing,
  LieRings.Homological.LieHomology.homologyTwo_free_subsingleton,
  LieRings.Homological.LieHomology.homologyTwoHopfEquiv,
  LieRings.Homological.LieHomology.PresentationHom.secondHomologyHopfEquiv_natural
]
