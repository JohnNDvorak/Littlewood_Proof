/-
Master import for all bridge files.
Import this to get all proved hypothesis instances and bridge lemmas.
-/

import Littlewood.Bridge.AristotleBridges
import Littlewood.Bridge.HypothesisInstances
import Littlewood.Bridge.AristotleHypothesisConnections
import Littlewood.Bridge.AristotleWiring
import Littlewood.Bridge.ZeroCountingBridge
import Littlewood.Bridge.AristotleTransfers

/-!
# All Bridges

This file re-exports all bridge modules for convenience.
Import `Littlewood.Bridge.AllBridges` to get:
- AristotleBridges: Bridge lemmas (chebyshevPsiV3, zeroCountingFunction = N)
- HypothesisInstances: Proved hypothesis class instances (4 total)
- AristotleHypothesisConnections: Documentation of connections
- AristotleWiring: Re-exported Aristotle theorems with standardized names
- ZeroCountingBridge: RVM.NZeros and ZCN.NZeros = zeroCountingFunction bridges
- AristotleTransfers: Master catalog of 19 transferred theorems in canonical types
-/
