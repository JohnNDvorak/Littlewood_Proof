/-
Template for wiring new Aristotle proofs to existing sorries.

When Aristotle returns a proof for lemma X:

1. Check if statement matches exactly:
   - Same types
   - Same hypotheses  
   - Same conclusion

2. If exact match, replace sorry:
   -- Option A: Copy proof inline
   lemma foo : statement := by
     [paste Aristotle proof here]
   
   -- Option B: Import from new file
   import Littlewood.Aristotle.NewFile
   lemma foo : statement := NewFile.foo

3. If slight mismatch, create bridge:
   lemma foo_bridge : adjusted_statement := aristotle_proof
   lemma foo : original_statement := by
     convert foo_bridge using 1
     [prove equivalence]

4. After wiring, verify:
   lake build Littlewood.Aristotle.TargetFile
-/
