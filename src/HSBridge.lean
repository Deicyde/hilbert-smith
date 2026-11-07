import HilbertSmith.Statements
import HSBridge.Statements
import HSBridge.Purity
import HSBridge.PurityTest
import HSBridge.SideBySide

/-!
# The two routes side by side

The only library that imports both OpenAI's route (`HilbertSmith`) and HS_proof's (`HSFormal`, with
`HSGeneral`). It states that both routes prove the same statements and records what each route
assumes.
-/
