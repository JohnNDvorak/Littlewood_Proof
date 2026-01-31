# Hardy Theorem Completion Checklist

*Updated 2026-01-31*

## When Aristotle Returns MeanSquareLowerBound

- [ ] Download to `Littlewood/Aristotle/_incoming/`
- [ ] Run `./intake.sh <filename>`
- [ ] Fix any `exact?` calls
- [ ] Remove `#check`/`#print` debug lines
- [ ] Add namespace (likely `MeanSquareLowerBound` or extend `HardyEstimatesPartial`)
- [ ] Verify imports `HardyEstimatesPartial` for `hardyZ` definition
- [ ] Build: `lake env lean Littlewood/Aristotle/<filename>.lean`
- [ ] Verify 0 sorries
- [ ] Add import to `Littlewood.lean`
- [ ] Full build: `lake build`
- [ ] Wire to `BuildingBlocks.zeta_mean_square_lower_bound` in `HardyBuildingBlocksInstance.lean`

## When Aristotle Returns HardyZIntegralBound

- [ ] Download to `Littlewood/Aristotle/_incoming/`
- [ ] Run `./intake.sh <filename>`
- [ ] Verify imports `HardyEstimatesPartial` for `hardyZ` definition
- [ ] Fix any issues
- [ ] Build: `lake env lean Littlewood/Aristotle/<filename>.lean`
- [ ] Verify 0 sorries
- [ ] Add import to `Littlewood.lean`
- [ ] Full build: `lake build`
- [ ] Wire to `BuildingBlocks.hardyZ_integral_bound` in `HardyBuildingBlocksInstance.lean`

## When Both Are Available: Complete BuildingBlocks

- [ ] Uncomment instance in `HardyBuildingBlocksInstance.lean`
- [ ] Fill in `zeta_mean_square_lower_bound` field
- [ ] Fill in `hardyZ_integral_bound` field
- [ ] Verify other 4 fields still work
- [ ] Build: `lake env lean Littlewood/Bridge/HardyBuildingBlocksInstance.lean`
- [ ] Full build: `lake build`

## When Aristotle Returns HardyInfiniteZerosComplete

- [ ] Download and intake
- [ ] Verify it imports all necessary files
- [ ] Check if it needs BuildingBlocks wired first
- [ ] Build individually, then full
- [ ] If 0 sorries: Hardy's theorem is COMPLETE

## After Hardy Completes

- [ ] Wire to `HardyCriticalLineZerosHyp` in `HardyCriticalLineWiring.lean`
- [ ] Move instance to `Assumptions.lean` (replace sorry)
- [ ] Check dependent assumptions that can now close
- [ ] Update `StatusDashboard.md`
- [ ] Commit with clear message
- [ ] Push
