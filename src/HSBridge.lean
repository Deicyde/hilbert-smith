import HilbertSmith.Statements
import HSBridge.Statements
import HSBridge.Purity
import HSBridge.PurityFixtures.Clean
import HSBridge.PurityFixtures.FCReversed
import HSBridge.PurityFixtures.Tainted
import HSBridge.PurityFixtures.TwinClean
import HSBridge.PurityFixtures.TwinHS
import HSBridge.PurityTest
import HSBridge.SideBySide

/-!
# The two routes side by side

The library that compares OpenAI's route (`HilbertSmith`) with HS_proof's (`HSFormal`). It checks
that both routes conclude the same statements, records what each route assumes, and audits that
OpenAI's route uses no constant of HS_proof.
-/
