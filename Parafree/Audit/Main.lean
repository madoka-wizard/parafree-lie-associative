import Parafree
import Parafree.Audit.StandardAxioms
import Parafree.Audit.TheoremAStatement
import Parafree.Audit.TheoremBStatement
import Parafree.Audit.TheoremDStatement
import Parafree.Audit.TheoremCStatement

/-! Audit every library and statement-check declaration, including private
helpers and the ported Koszul namespaces. The audit implementation itself
is excluded as a root; no mathematical dependency is excluded. -/
#assert_module_standard_axioms Parafree excluding [Parafree.Audit.StandardAxioms]
