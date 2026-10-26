import V185TrunkScan23Chunk0268

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1591386 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_1591386 : Nat := 118140960795 + 1591386 * 2 ^ 59
def prefixEnd_1591386 : Nat := 4983230072969 + 3 ^ 40 * 1591386 * 2
def baseEnd_1591386 : Nat := 817145924836015928656355

theorem tailTrace_1591386 : CollatzResearch.WordTrace tailWord_1591386 prefixEnd_1591386 817145924836015928656355 := by
  unfold tailWord_1591386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14510653953171945983958503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38695077208458522623889341 14510653953171945983958503)
  ·
    refine ⟨21765980929757918975937755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14510653953171945983958503 21765980929757918975937755)
    ·
      refine ⟨32648971394636878463906633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21765980929757918975937755 32648971394636878463906633)
      ·
        refine ⟨24486728545977658847929975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32648971394636878463906633 24486728545977658847929975)
        ·
          refine ⟨36730092818966488271894963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24486728545977658847929975 36730092818966488271894963)
          ·
            refine ⟨55095139228449732407842445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36730092818966488271894963 55095139228449732407842445)
            ·
              refine ⟨20660677210668649652940917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55095139228449732407842445 20660677210668649652940917)
              ·
                refine ⟨1936938488500185904963211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20660677210668649652940917 1936938488500185904963211)
                ·
                  refine ⟨2905407732750278857444817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936938488500185904963211 2905407732750278857444817)
                  ·
                    refine ⟨2179055799562709143083613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905407732750278857444817 2179055799562709143083613)
                    ·
                      refine ⟨817145924836015928656355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2179055799562709143083613 817145924836015928656355)
                      ·
                        rfl

theorem cell23_1591386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_1591386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591386 prefixEnd_1591386 := by exact prefixLift 1591386
  have htrace : WordTrace (prefixWord ++ tailWord_1591386) baseStart_1591386 baseEnd_1591386 := by
    simpa [prefixWord, tailWord_1591386, baseEnd_1591386] using wordTrace_append hprefix tailTrace_1591386
  have hstable : (prefixWord ++ tailWord_1591386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591386).length < 2 ^ (prefixWord ++ tailWord_1591386).sum := by decide
  have hdescent : baseEnd_1591386 < baseStart_1591386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591394 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1591394 : Nat := 118140960795 + 1591394 * 2 ^ 59
def prefixEnd_1591394 : Nat := 4983230072969 + 3 ^ 40 * 1591394 * 2
def baseEnd_1591394 : Nat := 817150032681251897356319

theorem tailTrace_1591394 : CollatzResearch.WordTrace tailWord_1591394 prefixEnd_1591394 817150032681251897356319 := by
  unfold tailWord_1591394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14510726899164700325531309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38695271731105867534750157 14510726899164700325531309)
  ·
    refine ⟨5441522587186762622074241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14510726899164700325531309 5441522587186762622074241)
    ·
      refine ⟨4081141940390071966555681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5441522587186762622074241 4081141940390071966555681)
      ·
        refine ⟨3060856455292553974916761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4081141940390071966555681 3060856455292553974916761)
        ·
          refine ⟨2295642341469415481187571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060856455292553974916761 2295642341469415481187571)
          ·
            refine ⟨3443463512204123221781357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295642341469415481187571 3443463512204123221781357)
            ·
              refine ⟨1291298817076546208168009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3443463512204123221781357 1291298817076546208168009)
              ·
                refine ⟨968474112807409656126007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291298817076546208168009 968474112807409656126007)
                ·
                  refine ⟨1452711169211114484189011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968474112807409656126007 1452711169211114484189011)
                  ·
                    refine ⟨2179066753816671726283517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1452711169211114484189011 2179066753816671726283517)
                    ·
                      refine ⟨817150032681251897356319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2179066753816671726283517 817150032681251897356319)
                      ·
                        rfl

theorem cell23_1591394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1591394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591394 prefixEnd_1591394 := by exact prefixLift 1591394
  have htrace : WordTrace (prefixWord ++ tailWord_1591394) baseStart_1591394 baseEnd_1591394 := by
    simpa [prefixWord, tailWord_1591394, baseEnd_1591394] using wordTrace_append hprefix tailTrace_1591394
  have hstable : (prefixWord ++ tailWord_1591394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591394).length < 2 ^ (prefixWord ++ tailWord_1591394).sum := by decide
  have hdescent : baseEnd_1591394 < baseStart_1591394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591410 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_1591410 : Nat := 118140960795 + 1591410 * 2 ^ 59
def prefixEnd_1591410 : Nat := 4983230072969 + 3 ^ 40 * 1591410 * 2
def baseEnd_1591410 : Nat := 272386082790574611585415

theorem tailTrace_1591410 : CollatzResearch.WordTrace tailWord_1591410 prefixEnd_1591410 272386082790574611585415 := by
  unfold tailWord_1591410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14510872791150209008676921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38695660776400557356471789 14510872791150209008676921)
  ·
    refine ⟨10883154593362656756507691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14510872791150209008676921 10883154593362656756507691)
    ·
      refine ⟨16324731890043985134761537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10883154593362656756507691 16324731890043985134761537)
      ·
        refine ⟨12243548917532988851071153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16324731890043985134761537 12243548917532988851071153)
        ·
          refine ⟨9182661688149741638303365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12243548917532988851071153 9182661688149741638303365)
          ·
            refine ⟨1721749066528076557181881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9182661688149741638303365 1721749066528076557181881)
            ·
              refine ⟨1291311799896057417886411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721749066528076557181881 1291311799896057417886411)
              ·
                refine ⟨1936967699844086126829617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291311799896057417886411 1936967699844086126829617)
                ·
                  refine ⟨1452725774883064595122213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1936967699844086126829617 1452725774883064595122213)
                  ·
                    refine ⟨272386082790574611585415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452725774883064595122213 272386082790574611585415)
                    ·
                      rfl

theorem cell23_1591410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_1591410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591410 prefixEnd_1591410 := by exact prefixLift 1591410
  have htrace : WordTrace (prefixWord ++ tailWord_1591410) baseStart_1591410 baseEnd_1591410 := by
    simpa [prefixWord, tailWord_1591410, baseEnd_1591410] using wordTrace_append hprefix tailTrace_1591410
  have hstable : (prefixWord ++ tailWord_1591410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591410).length < 2 ^ (prefixWord ++ tailWord_1591410).sum := by decide
  have hdescent : baseEnd_1591410 < baseStart_1591410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591479 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 9]
def baseStart_1591479 : Nat := 118140960795 + 1591479 * 2 ^ 59
def prefixEnd_1591479 : Nat := 4983230072969 + 3 ^ 40 * 1591479 * 2
def baseEnd_1591479 : Nat := 90799297615209340532603

theorem tailTrace_1591479 : CollatzResearch.WordTrace tailWord_1591479 prefixEnd_1591479 90799297615209340532603 := by
  unfold tailWord_1591479
  simp only [CollatzResearch.WordTrace]
  refine ⟨58046007801350860818969491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38697338534233907212646327 58046007801350860818969491)
  ·
    refine ⟨87069011702026291228454237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58046007801350860818969491 87069011702026291228454237)
    ·
      refine ⟨32650879388259859210670339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87069011702026291228454237 32650879388259859210670339)
      ·
        refine ⟨48976319082389788816005509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32650879388259859210670339 48976319082389788816005509)
        ·
          refine ⟨9183059827948085403001033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48976319082389788816005509 9183059827948085403001033)
          ·
            refine ⟨6887294870961064052250775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9183059827948085403001033 6887294870961064052250775)
            ·
              refine ⟨10330942306441596078376163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887294870961064052250775 10330942306441596078376163)
              ·
                refine ⟨15496413459662394117564245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10330942306441596078376163 15496413459662394117564245)
                ·
                  refine ⟨90799297615209340532603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15496413459662394117564245 90799297615209340532603)
                  ·
                    rfl

theorem cell23_1591479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 9].length) (baseStart_1591479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591479 prefixEnd_1591479 := by exact prefixLift 1591479
  have htrace : WordTrace (prefixWord ++ tailWord_1591479) baseStart_1591479 baseEnd_1591479 := by
    simpa [prefixWord, tailWord_1591479, baseEnd_1591479] using wordTrace_append hprefix tailTrace_1591479
  have hstable : (prefixWord ++ tailWord_1591479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591479).length < 2 ^ (prefixWord ++ tailWord_1591479).sum := by decide
  have hdescent : baseEnd_1591479 < baseStart_1591479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591519 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1591519 : Nat := 118140960795 + 1591519 * 2 ^ 59
def prefixEnd_1591519 : Nat := 4983230072969 + 3 ^ 40 * 1591519 * 2
def baseEnd_1591519 : Nat := 817214217763063908293243

theorem tailTrace_1591519 : CollatzResearch.WordTrace tailWord_1591519 prefixEnd_1591519 817214217763063908293243 := by
  unfold tailWord_1591519
  simp only [CollatzResearch.WordTrace]
  refine ⟨58047466721205947650425611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38698311147470631766950407 58047466721205947650425611)
  ·
    refine ⟨87071200081808921475638417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58047466721205947650425611 87071200081808921475638417)
    ·
      refine ⟨65303400061356691106728813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87071200081808921475638417 65303400061356691106728813)
      ·
        refine ⟨24488775023008759165023305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65303400061356691106728813 24488775023008759165023305)
        ·
          refine ⟨18366581267256569373767479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24488775023008759165023305 18366581267256569373767479)
          ·
            refine ⟨27549871900884854060651219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366581267256569373767479 27549871900884854060651219)
            ·
              refine ⟨41324807851327281090976829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27549871900884854060651219 41324807851327281090976829)
              ·
                refine ⟨15496802944247730409116311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41324807851327281090976829 15496802944247730409116311)
                ·
                  refine ⟨23245204416371595613674467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15496802944247730409116311 23245204416371595613674467)
                  ·
                    refine ⟨34867806624557393420511701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23245204416371595613674467 34867806624557393420511701)
                    ·
                      refine ⟨817214217763063908293243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34867806624557393420511701 817214217763063908293243)
                      ·
                        rfl

theorem cell23_1591519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1591519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591519 prefixEnd_1591519 := by exact prefixLift 1591519
  have htrace : WordTrace (prefixWord ++ tailWord_1591519) baseStart_1591519 baseEnd_1591519 := by
    simpa [prefixWord, tailWord_1591519, baseEnd_1591519] using wordTrace_append hprefix tailTrace_1591519
  have hstable : (prefixWord ++ tailWord_1591519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591519).length < 2 ^ (prefixWord ++ tailWord_1591519).sum := by decide
  have hdescent : baseEnd_1591519 < baseStart_1591519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591539 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 8]
def baseStart_1591539 : Nat := 118140960795 + 1591539 * 2 ^ 59
def prefixEnd_1591539 : Nat := 4983230072969 + 3 ^ 40 * 1591539 * 2
def baseEnd_1591539 : Nat := 272408162458717943347717

theorem tailTrace_1591539 : CollatzResearch.WordTrace tailWord_1591539 prefixEnd_1591539 272408162458717943347717 := by
  unfold tailWord_1591539
  simp only [CollatzResearch.WordTrace]
  refine ⟨58048196181133491066153671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38698797454088994044102447 58048196181133491066153671)
  ·
    refine ⟨87072294271700236599230507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58048196181133491066153671 87072294271700236599230507)
    ·
      refine ⟨130608441407550354898845761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87072294271700236599230507 130608441407550354898845761)
      ·
        refine ⟨97956331055662766174134321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130608441407550354898845761 97956331055662766174134321)
        ·
          refine ⟨73467248291747074630600741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97956331055662766174134321 73467248291747074630600741)
          ·
            refine ⟨13775109054702576493237639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73467248291747074630600741 13775109054702576493237639)
            ·
              refine ⟨20662663582053864739856459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775109054702576493237639 20662663582053864739856459)
              ·
                refine ⟨30993995373080797109784689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20662663582053864739856459 30993995373080797109784689)
                ·
                  refine ⟨23245496529810597832338517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30993995373080797109784689 23245496529810597832338517)
                  ·
                    refine ⟨272408162458717943347717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23245496529810597832338517 272408162458717943347717)
                    ·
                      rfl

theorem cell23_1591539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_1591539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591539 prefixEnd_1591539 := by exact prefixLift 1591539
  have htrace : WordTrace (prefixWord ++ tailWord_1591539) baseStart_1591539 baseEnd_1591539 := by
    simpa [prefixWord, tailWord_1591539, baseEnd_1591539] using wordTrace_append hprefix tailTrace_1591539
  have hstable : (prefixWord ++ tailWord_1591539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591539).length < 2 ^ (prefixWord ++ tailWord_1591539).sum := by decide
  have hdescent : baseEnd_1591539 < baseStart_1591539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591546 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_1591546 : Nat := 118140960795 + 1591546 * 2 ^ 59
def prefixEnd_1591546 : Nat := 4983230072969 + 3 ^ 40 * 1591546 * 2
def baseEnd_1591546 : Nat := 817228081740735302655619

theorem tailTrace_1591546 : CollatzResearch.WordTrace tailWord_1591546 prefixEnd_1591546 817228081740735302655619 := by
  unfold tailWord_1591546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512112873027032815414623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38698967661405420841105661 14512112873027032815414623)
  ·
    refine ⟨21768169309540549223121935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14512112873027032815414623 21768169309540549223121935)
    ·
      refine ⟨32652253964310823834682903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21768169309540549223121935 32652253964310823834682903)
      ·
        refine ⟨48978380946466235752024355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32652253964310823834682903 48978380946466235752024355)
        ·
          refine ⟨73467571419699353628036533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48978380946466235752024355 73467571419699353628036533)
          ·
            refine ⟨6887584820596814402628425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73467571419699353628036533 6887584820596814402628425)
            ·
              refine ⟨5165688615447610801971319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6887584820596814402628425 5165688615447610801971319)
              ·
                refine ⟨7748532923171416202956979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165688615447610801971319 7748532923171416202956979)
                ·
                  refine ⟨11622799384757124304435469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7748532923171416202956979 11622799384757124304435469)
                  ·
                    refine ⟨4358549769283921614163301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11622799384757124304435469 4358549769283921614163301)
                    ·
                      refine ⟨817228081740735302655619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4358549769283921614163301 817228081740735302655619)
                      ·
                        rfl

theorem cell23_1591546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_1591546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591546 prefixEnd_1591546 := by exact prefixLift 1591546
  have htrace : WordTrace (prefixWord ++ tailWord_1591546) baseStart_1591546 baseEnd_1591546 := by
    simpa [prefixWord, tailWord_1591546, baseEnd_1591546] using wordTrace_append hprefix tailTrace_1591546
  have hstable : (prefixWord ++ tailWord_1591546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591546).length < 2 ^ (prefixWord ++ tailWord_1591546).sum := by decide
  have hdescent : baseEnd_1591546 < baseStart_1591546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591573 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1591573 : Nat := 118140960795 + 1591573 * 2 ^ 59
def prefixEnd_1591573 : Nat := 4983230072969 + 3 ^ 40 * 1591573 * 2
def baseEnd_1591573 : Nat := 272413981906135565672665

theorem tailTrace_1591573 : CollatzResearch.WordTrace tailWord_1591573 prefixEnd_1591573 272413981906135565672665 := by
  unfold tailWord_1591573
  simp only [CollatzResearch.WordTrace]
  refine ⟨58049436263010314872891373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38699624175340209915260915 58049436263010314872891373)
  ·
    refine ⟨21768538598628868077334265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58049436263010314872891373 21768538598628868077334265)
    ·
      refine ⟨16326403948971651058000699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21768538598628868077334265 16326403948971651058000699)
      ·
        refine ⟨24489605923457476587001049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326403948971651058000699 24489605923457476587001049)
        ·
          refine ⟨18367204442593107440250787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24489605923457476587001049 18367204442593107440250787)
          ·
            refine ⟨27550806663889661160376181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18367204442593107440250787 27550806663889661160376181)
            ·
              refine ⟨2582888124739655733785267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27550806663889661160376181 2582888124739655733785267)
              ·
                refine ⟨3874332187109483600677901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582888124739655733785267 3874332187109483600677901)
                ·
                  refine ⟨1452874570166056350254213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3874332187109483600677901 1452874570166056350254213)
                  ·
                    refine ⟨272413981906135565672665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452874570166056350254213 272413981906135565672665)
                    ·
                      rfl

theorem cell23_1591573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1591573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591573 prefixEnd_1591573 := by exact prefixLift 1591573
  have htrace : WordTrace (prefixWord ++ tailWord_1591573) baseStart_1591573 baseEnd_1591573 := by
    simpa [prefixWord, tailWord_1591573, baseEnd_1591573] using wordTrace_append hprefix tailTrace_1591573
  have hstable : (prefixWord ++ tailWord_1591573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591573).length < 2 ^ (prefixWord ++ tailWord_1591573).sum := by decide
  have hdescent : baseEnd_1591573 < baseStart_1591573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591596 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_1591596 : Nat := 118140960795 + 1591596 * 2 ^ 59
def prefixEnd_1591596 : Nat := 4983230072969 + 3 ^ 40 * 1591596 * 2
def baseEnd_1591596 : Nat := 817253755773460107030389

theorem tailTrace_1591596 : CollatzResearch.WordTrace tailWord_1591596 prefixEnd_1591596 817253755773460107030389 := by
  unfold tailWord_1591596
  simp only [CollatzResearch.WordTrace]
  refine ⟨29025137570963494900489321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38700183427951326533985761 29025137570963494900489321)
  ·
    refine ⟨21768853178222621175366991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29025137570963494900489321 21768853178222621175366991)
    ·
      refine ⟨32653279767333931763050487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21768853178222621175366991 32653279767333931763050487)
      ·
        refine ⟨48979919651000897644575731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32653279767333931763050487 48979919651000897644575731)
        ·
          refine ⟨73469879476501346466863597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48979919651000897644575731 73469879476501346466863597)
          ·
            refine ⟨27551204803688004925073849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73469879476501346466863597 27551204803688004925073849)
            ·
              refine ⟨20663403602766003693805387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27551204803688004925073849 20663403602766003693805387)
              ·
                refine ⟨30995105404149005540708081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20663403602766003693805387 30995105404149005540708081)
                ·
                  refine ⟨23246329053111754155531061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30995105404149005540708081 23246329053111754155531061)
                  ·
                    refine ⟨2179343348729226952081037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23246329053111754155531061 2179343348729226952081037)
                    ·
                      refine ⟨817253755773460107030389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2179343348729226952081037 817253755773460107030389)
                      ·
                        rfl

theorem cell23_1591596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_1591596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591596 prefixEnd_1591596 := by exact prefixLift 1591596
  have htrace : WordTrace (prefixWord ++ tailWord_1591596) baseStart_1591596 baseEnd_1591596 := by
    simpa [prefixWord, tailWord_1591596, baseEnd_1591596] using wordTrace_append hprefix tailTrace_1591596
  have hstable : (prefixWord ++ tailWord_1591596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591596).length < 2 ^ (prefixWord ++ tailWord_1591596).sum := by decide
  have hdescent : baseEnd_1591596 < baseStart_1591596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591597 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1591597 : Nat := 118140960795 + 1591597 * 2 ^ 59
def prefixEnd_1591597 : Nat := 4983230072969 + 3 ^ 40 * 1591597 * 2
def baseEnd_1591597 : Nat := 817254269254114603117885

theorem tailTrace_1591597 : CollatzResearch.WordTrace tailWord_1591597 prefixEnd_1591597 817254269254114603117885 := by
  unfold tailWord_1591597
  simp only [CollatzResearch.WordTrace]
  refine ⟨58050311614923366971765045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38700207743282244647843363 58050311614923366971765045)
  ·
    refine ⟨5442216713899065653602973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58050311614923366971765045 5442216713899065653602973)
    ·
      refine ⟨2040831267712149620101115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5442216713899065653602973 2040831267712149620101115)
      ·
        refine ⟨3061246901568224430151673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040831267712149620101115 3061246901568224430151673)
        ·
          refine ⟨2295935176176168322613755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061246901568224430151673 2295935176176168322613755)
          ·
            refine ⟨3443902764264252483920633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295935176176168322613755 3443902764264252483920633)
            ·
              refine ⟨2582927073198189362940475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443902764264252483920633 2582927073198189362940475)
              ·
                refine ⟨3874390609797284044410713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582927073198189362940475 3874390609797284044410713)
                ·
                  refine ⟨2905792957347963033308035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3874390609797284044410713 2905792957347963033308035)
                  ·
                    refine ⟨4358689436021944549962053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905792957347963033308035 4358689436021944549962053)
                    ·
                      refine ⟨817254269254114603117885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4358689436021944549962053 817254269254114603117885)
                      ·
                        rfl

theorem cell23_1591597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1591597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591597 prefixEnd_1591597 := by exact prefixLift 1591597
  have htrace : WordTrace (prefixWord ++ tailWord_1591597) baseStart_1591597 baseEnd_1591597 := by
    simpa [prefixWord, tailWord_1591597, baseEnd_1591597] using wordTrace_append hprefix tailTrace_1591597
  have hstable : (prefixWord ++ tailWord_1591597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591597).length < 2 ^ (prefixWord ++ tailWord_1591597).sum := by decide
  have hdescent : baseEnd_1591597 < baseStart_1591597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591653 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1591653 : Nat := 118140960795 + 1591653 * 2 ^ 59
def prefixEnd_1591653 : Nat := 4983230072969 + 3 ^ 40 * 1591653 * 2
def baseEnd_1591653 : Nat := 817283024170766384017627

theorem tailTrace_1591653 : CollatzResearch.WordTrace tailWord_1591653 prefixEnd_1591653 817283024170766384017627 := by
  unfold tailWord_1591653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58052354102720488535803613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38701569401813659023869075 58052354102720488535803613)
  ·
    refine ⟨21769632788520183200926355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58052354102720488535803613 21769632788520183200926355)
    ·
      refine ⟨32654449182780274801389533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21769632788520183200926355 32654449182780274801389533)
      ·
        refine ⟨12245418443542603050521075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32654449182780274801389533 12245418443542603050521075)
        ·
          refine ⟨18368127665313904575781613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12245418443542603050521075 18368127665313904575781613)
          ·
            refine ⟨6888047874492714215918105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18368127665313904575781613 6888047874492714215918105)
            ·
              refine ⟨5166035905869535661938579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6888047874492714215918105 5166035905869535661938579)
              ·
                refine ⟨7749053858804303492907869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166035905869535661938579 7749053858804303492907869)
                ·
                  refine ⟨2905895197051613809840451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7749053858804303492907869 2905895197051613809840451)
                  ·
                    refine ⟨4358842795577420714760677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905895197051613809840451 4358842795577420714760677)
                    ·
                      refine ⟨817283024170766384017627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4358842795577420714760677 817283024170766384017627)
                      ·
                        rfl

theorem cell23_1591653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1591653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591653 prefixEnd_1591653 := by exact prefixLift 1591653
  have htrace : WordTrace (prefixWord ++ tailWord_1591653) baseStart_1591653 baseEnd_1591653 := by
    simpa [prefixWord, tailWord_1591653, baseEnd_1591653] using wordTrace_append hprefix tailTrace_1591653
  have hstable : (prefixWord ++ tailWord_1591653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591653).length < 2 ^ (prefixWord ++ tailWord_1591653).sum := by decide
  have hdescent : baseEnd_1591653 < baseStart_1591653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591687 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_1591687 : Nat := 118140960795 + 1591687 * 2 ^ 59
def prefixEnd_1591687 : Nat := 4983230072969 + 3 ^ 40 * 1591687 * 2
def baseEnd_1591687 : Nat := 817300482513019250992471

theorem tailTrace_1591687 : CollatzResearch.WordTrace tailWord_1591687 prefixEnd_1591687 817300482513019250992471 := by
  unfold tailWord_1591687
  simp only [CollatzResearch.WordTrace]
  refine ⟨58053594184597312342541315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38702396123064874895027543 58053594184597312342541315)
  ·
    refine ⟨87080391276895968513811973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58053594184597312342541315 87080391276895968513811973)
    ·
      refine ⟨16327573364417994096339745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87080391276895968513811973 16327573364417994096339745)
      ·
        refine ⟨12245680023313495572254809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16327573364417994096339745 12245680023313495572254809)
        ·
          refine ⟨9184260017485121679191107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12245680023313495572254809 9184260017485121679191107)
          ·
            refine ⟨13776390026227682518786661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184260017485121679191107 13776390026227682518786661)
            ·
              refine ⟨2583073129917690472272499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13776390026227682518786661 2583073129917690472272499)
              ·
                refine ⟨3874609694876535708408749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583073129917690472272499 3874609694876535708408749)
                ·
                  refine ⟨1452978635578700890653281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3874609694876535708408749 1452978635578700890653281)
                  ·
                    refine ⟨1089733976684025667989961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1452978635578700890653281 1089733976684025667989961)
                    ·
                      refine ⟨817300482513019250992471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089733976684025667989961 817300482513019250992471)
                      ·
                        rfl

theorem cell23_1591687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_1591687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591687 prefixEnd_1591687 := by exact prefixLift 1591687
  have htrace : WordTrace (prefixWord ++ tailWord_1591687) baseStart_1591687 baseEnd_1591687 := by
    simpa [prefixWord, tailWord_1591687, baseEnd_1591687] using wordTrace_append hprefix tailTrace_1591687
  have hstable : (prefixWord ++ tailWord_1591687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591687).length < 2 ^ (prefixWord ++ tailWord_1591687).sum := by decide
  have hdescent : baseEnd_1591687 < baseStart_1591687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591700 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1591700 : Nat := 118140960795 + 1591700 * 2 ^ 59
def prefixEnd_1591700 : Nat := 4983230072969 + 3 ^ 40 * 1591700 * 2
def baseEnd_1591700 : Nat := 817307157761527700129911

theorem tailTrace_1591700 : CollatzResearch.WordTrace tailWord_1591700 prefixEnd_1591700 817307157761527700129911 := by
  unfold tailWord_1591700
  simp only [CollatzResearch.WordTrace]
  refine ⟨29027034166775107781382277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38702712222366810375176369 29027034166775107781382277)
  ·
    refine ⟨5442568906270332709009177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29027034166775107781382277 5442568906270332709009177)
    ·
      refine ⟨4081926679702749531756883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5442568906270332709009177 4081926679702749531756883)
      ·
        refine ⟨6122890019554124297635325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081926679702749531756883 6122890019554124297635325)
        ·
          refine ⟨2296083757332796611613247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6122890019554124297635325 2296083757332796611613247)
          ·
            refine ⟨3444125635999194917419871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296083757332796611613247 3444125635999194917419871)
            ·
              refine ⟨5166188453998792376129807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444125635999194917419871 5166188453998792376129807)
              ·
                refine ⟨7749282680998188564194711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166188453998792376129807 7749282680998188564194711)
                ·
                  refine ⟨11623924021497282846292067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749282680998188564194711 11623924021497282846292067)
                  ·
                    refine ⟨17435886032245924269438101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11623924021497282846292067 17435886032245924269438101)
                    ·
                      refine ⟨817307157761527700129911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17435886032245924269438101 817307157761527700129911)
                      ·
                        rfl

theorem cell23_1591700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1591700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591700 prefixEnd_1591700 := by exact prefixLift 1591700
  have htrace : WordTrace (prefixWord ++ tailWord_1591700) baseStart_1591700 baseEnd_1591700 := by
    simpa [prefixWord, tailWord_1591700, baseEnd_1591700] using wordTrace_append hprefix tailTrace_1591700
  have hstable : (prefixWord ++ tailWord_1591700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591700).length < 2 ^ (prefixWord ++ tailWord_1591700).sum := by decide
  have hdescent : baseEnd_1591700 < baseStart_1591700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591710 : List Nat := [4, 3, 1, 2, 1, 2, 1, 9]
def baseStart_1591710 : Nat := 118140960795 + 1591710 * 2 ^ 59
def prefixEnd_1591710 : Nat := 4983230072969 + 3 ^ 40 * 1591710 * 2
def baseEnd_1591710 : Nat := 30270825650669357814995

theorem tailTrace_1591710 : CollatzResearch.WordTrace tailWord_1591710 prefixEnd_1591710 30270825650669357814995 := by
  unfold tailWord_1591710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256804132939248408828573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38702955375675991513752389 7256804132939248408828573)
  ·
    refine ⟨2721301549852218153310715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7256804132939248408828573 2721301549852218153310715)
    ·
      refine ⟨4081952324778327229966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721301549852218153310715 4081952324778327229966073)
      ·
        refine ⟨3061464243583745422474555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4081952324778327229966073 3061464243583745422474555)
        ·
          refine ⟨4592196365375618133711833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061464243583745422474555 4592196365375618133711833)
          ·
            refine ⟨3444147274031713600283875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4592196365375618133711833 3444147274031713600283875)
            ·
              refine ⟨5166220911047570400425813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444147274031713600283875 5166220911047570400425813)
              ·
                refine ⟨30270825650669357814995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5166220911047570400425813 30270825650669357814995)
                ·
                  rfl

theorem cell23_1591710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_1591710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591710 prefixEnd_1591710 := by exact prefixLift 1591710
  have htrace : WordTrace (prefixWord ++ tailWord_1591710) baseStart_1591710 baseEnd_1591710 := by
    simpa [prefixWord, tailWord_1591710, baseEnd_1591710] using wordTrace_append hprefix tailTrace_1591710
  have hstable : (prefixWord ++ tailWord_1591710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591710).length < 2 ^ (prefixWord ++ tailWord_1591710).sum := by decide
  have hdescent : baseEnd_1591710 < baseStart_1591710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591764 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1591764 : Nat := 118140960795 + 1591764 * 2 ^ 59
def prefixEnd_1591764 : Nat := 4983230072969 + 3 ^ 40 * 1591764 * 2
def baseEnd_1591764 : Nat := 817340020523415449729617

theorem tailTrace_1591764 : CollatzResearch.WordTrace tailWord_1591764 prefixEnd_1591764 817340020523415449729617 := by
  unfold tailWord_1591764
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028201302659177246547173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38704268403545569662062897 29028201302659177246547173)
  ·
    refine ⟨5442787744248595733727595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29028201302659177246547173 5442787744248595733727595)
    ·
      refine ⟨8164181616372893600591393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5442787744248595733727595 8164181616372893600591393)
      ·
        refine ⟨6123136212279670200443545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8164181616372893600591393 6123136212279670200443545)
        ·
          refine ⟨4592352159209752650332659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6123136212279670200443545 4592352159209752650332659)
          ·
            refine ⟨6888528238814628975498989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592352159209752650332659 6888528238814628975498989)
            ·
              refine ⟨2583198089555485865812121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6888528238814628975498989 2583198089555485865812121)
              ·
                refine ⟨1937398567166614399359091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583198089555485865812121 1937398567166614399359091)
                ·
                  refine ⟨2906097850749921599038637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937398567166614399359091 2906097850749921599038637)
                  ·
                    refine ⟨1089786694031220599639489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906097850749921599038637 1089786694031220599639489)
                    ·
                      refine ⟨817340020523415449729617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089786694031220599639489 817340020523415449729617)
                      ·
                        rfl

theorem cell23_1591764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1591764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591764 prefixEnd_1591764 := by exact prefixLift 1591764
  have htrace : WordTrace (prefixWord ++ tailWord_1591764) baseStart_1591764 baseEnd_1591764 := by
    simpa [prefixWord, tailWord_1591764, baseEnd_1591764] using wordTrace_append hprefix tailTrace_1591764
  have hstable : (prefixWord ++ tailWord_1591764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591764).length < 2 ^ (prefixWord ++ tailWord_1591764).sum := by decide
  have hdescent : baseEnd_1591764 < baseStart_1591764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591781 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1591781 : Nat := 118140960795 + 1591781 * 2 ^ 59
def prefixEnd_1591781 : Nat := 4983230072969 + 3 ^ 40 * 1591781 * 2
def baseEnd_1591781 : Nat := 817348749694541883217039

theorem tailTrace_1591781 : CollatzResearch.WordTrace tailWord_1591781 prefixEnd_1591781 817348749694541883217039 := by
  unfold tailWord_1591781
  simp only [CollatzResearch.WordTrace]
  refine ⟨58057022646256766396463197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38704681764171177597642131 58057022646256766396463197)
  ·
    refine ⟨21771383492346287398673699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58057022646256766396463197 21771383492346287398673699)
    ·
      refine ⟨32657075238519431098010549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21771383492346287398673699 32657075238519431098010549)
      ·
        refine ⟨3061600803611196665438489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32657075238519431098010549 3061600803611196665438489)
        ·
          refine ⟨2296200602708397499078867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061600803611196665438489 2296200602708397499078867)
          ·
            refine ⟨3444300904062596248618301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296200602708397499078867 3444300904062596248618301)
            ·
              refine ⟨1291612839023473593231863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444300904062596248618301 1291612839023473593231863)
              ·
                refine ⟨1937419258535210389847795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291612839023473593231863 1937419258535210389847795)
                ·
                  refine ⟨2906128887802815584771693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937419258535210389847795 2906128887802815584771693)
                  ·
                    refine ⟨1089798332926055844289385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2906128887802815584771693 1089798332926055844289385)
                    ·
                      refine ⟨817348749694541883217039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089798332926055844289385 817348749694541883217039)
                      ·
                        rfl

theorem cell23_1591781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1591781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591781 prefixEnd_1591781 := by exact prefixLift 1591781
  have htrace : WordTrace (prefixWord ++ tailWord_1591781) baseStart_1591781 baseEnd_1591781 := by
    simpa [prefixWord, tailWord_1591781, baseEnd_1591781] using wordTrace_append hprefix tailTrace_1591781
  have hstable : (prefixWord ++ tailWord_1591781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591781).length < 2 ^ (prefixWord ++ tailWord_1591781).sum := by decide
  have hdescent : baseEnd_1591781 < baseStart_1591781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591800 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 5]
def baseStart_1591800 : Nat := 118140960795 + 1591800 * 2 ^ 59
def prefixEnd_1591800 : Nat := 4983230072969 + 3 ^ 40 * 1591800 * 2
def baseEnd_1591800 : Nat := 90817611758553034319939

theorem tailTrace_1591800 : CollatzResearch.WordTrace tailWord_1591800 prefixEnd_1591800 90817611758553034319939 := by
  unfold tailWord_1591800
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028857816593966320702427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38705143755458621760936569 29028857816593966320702427)
  ·
    refine ⟨43543286724890949481053641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29028857816593966320702427 43543286724890949481053641)
    ·
      refine ⟨32657465043668212110790231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43543286724890949481053641 32657465043668212110790231)
      ·
        refine ⟨48986197565502318166185347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32657465043668212110790231 48986197565502318166185347)
        ·
          refine ⟨73479296348253477249278021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48986197565502318166185347 73479296348253477249278021)
          ·
            refine ⟨13777368065297526984239629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73479296348253477249278021 13777368065297526984239629)
            ·
              refine ⟨5166513024486572619089861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13777368065297526984239629 5166513024486572619089861)
              ·
                refine ⟨968721192091232366079349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5166513024486572619089861 968721192091232366079349)
                ·
                  refine ⟨90817611758553034319939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 968721192091232366079349 90817611758553034319939)
                  ·
                    rfl

theorem cell23_1591800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 5].length) (baseStart_1591800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591800 prefixEnd_1591800 := by exact prefixLift 1591800
  have htrace : WordTrace (prefixWord ++ tailWord_1591800) baseStart_1591800 baseEnd_1591800 := by
    simpa [prefixWord, tailWord_1591800, baseEnd_1591800] using wordTrace_append hprefix tailTrace_1591800
  have hstable : (prefixWord ++ tailWord_1591800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591800).length < 2 ^ (prefixWord ++ tailWord_1591800).sum := by decide
  have hdescent : baseEnd_1591800 < baseStart_1591800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591813 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_1591813 : Nat := 118140960795 + 1591813 * 2 ^ 59
def prefixEnd_1591813 : Nat := 4983230072969 + 3 ^ 40 * 1591813 * 2
def baseEnd_1591813 : Nat := 272455060358495252672297

theorem tailTrace_1591813 : CollatzResearch.WordTrace tailWord_1591813 prefixEnd_1591813 272455060358495252672297 := by
  unfold tailWord_1591813
  simp only [CollatzResearch.WordTrace]
  refine ⟨58058189782140835861628093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38705459854760557241085395 58058189782140835861628093)
  ·
    refine ⟨21771821168302813448110535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58058189782140835861628093 21771821168302813448110535)
    ·
      refine ⟨32657731752454220172165803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21771821168302813448110535 32657731752454220172165803)
      ·
        refine ⟨48986597628681330258248705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32657731752454220172165803 48986597628681330258248705)
        ·
          refine ⟨36739948221510997693686529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48986597628681330258248705 36739948221510997693686529)
          ·
            refine ⟨27554961166133248270264897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36739948221510997693686529 27554961166133248270264897)
            ·
              refine ⟨20666220874599936202698673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27554961166133248270264897 20666220874599936202698673)
              ·
                refine ⟨15499665655949952152024005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20666220874599936202698673 15499665655949952152024005)
                ·
                  refine ⟨2906187310490616028504501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15499665655949952152024005 2906187310490616028504501)
                  ·
                    refine ⟨272455060358495252672297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2906187310490616028504501 272455060358495252672297)
                    ·
                      rfl

theorem cell23_1591813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_1591813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591813 prefixEnd_1591813 := by exact prefixLift 1591813
  have htrace : WordTrace (prefixWord ++ tailWord_1591813) baseStart_1591813 baseEnd_1591813 := by
    simpa [prefixWord, tailWord_1591813, baseEnd_1591813] using wordTrace_append hprefix tailTrace_1591813
  have hstable : (prefixWord ++ tailWord_1591813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591813).length < 2 ^ (prefixWord ++ tailWord_1591813).sum := by decide
  have hdescent : baseEnd_1591813 < baseStart_1591813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591833 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1591833 : Nat := 118140960795 + 1591833 * 2 ^ 59
def prefixEnd_1591833 : Nat := 4983230072969 + 3 ^ 40 * 1591833 * 2
def baseEnd_1591833 : Nat := 817375450688575679766799

theorem tailTrace_1591833 : CollatzResearch.WordTrace tailWord_1591833 prefixEnd_1591833 817375450688575679766799 := by
  unfold tailWord_1591833
  simp only [CollatzResearch.WordTrace]
  refine ⟨58058919242068379277356153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38705946161378919518237435 58058919242068379277356153)
  ·
    refine ⟨43544189431551284458017115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58058919242068379277356153 43544189431551284458017115)
    ·
      refine ⟨65316284147326926687025673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43544189431551284458017115 65316284147326926687025673)
      ·
        refine ⟨48987213110495195015269255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65316284147326926687025673 48987213110495195015269255)
        ·
          refine ⟨73480819665742792522903883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48987213110495195015269255 73480819665742792522903883)
          ·
            refine ⟨110221229498614188784355825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73480819665742792522903883 110221229498614188784355825)
            ·
              refine ⟨82665922123960641588266869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110221229498614188784355825 82665922123960641588266869)
              ·
                refine ⟨7749930199121310148900019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82665922123960641588266869 7749930199121310148900019)
                ·
                  refine ⟨11624895298681965223350029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749930199121310148900019 11624895298681965223350029)
                  ·
                    refine ⟨4359335737005736958756261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11624895298681965223350029 4359335737005736958756261)
                    ·
                      refine ⟨817375450688575679766799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4359335737005736958756261 817375450688575679766799)
                      ·
                        rfl

theorem cell23_1591833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1591833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591833 prefixEnd_1591833 := by exact prefixLift 1591833
  have htrace : WordTrace (prefixWord ++ tailWord_1591833) baseStart_1591833 baseEnd_1591833 := by
    simpa [prefixWord, tailWord_1591833, baseEnd_1591833] using wordTrace_append hprefix tailTrace_1591833
  have hstable : (prefixWord ++ tailWord_1591833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591833).length < 2 ^ (prefixWord ++ tailWord_1591833).sum := by decide
  have hdescent : baseEnd_1591833 < baseStart_1591833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591863 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1591863 : Nat := 118140960795 + 1591863 * 2 ^ 59
def prefixEnd_1591863 : Nat := 4983230072969 + 3 ^ 40 * 1591863 * 2
def baseEnd_1591863 : Nat := 817390855108210562391661

theorem tailTrace_1591863 : CollatzResearch.WordTrace tailWord_1591863 prefixEnd_1591863 817390855108210562391661 := by
  unfold tailWord_1591863
  simp only [CollatzResearch.WordTrace]
  refine ⟨58060013431959694400948243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38706675621306462933965495 58060013431959694400948243)
  ·
    refine ⟨87090020147939541601422365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58060013431959694400948243 87090020147939541601422365)
    ·
      refine ⟨32658757555477328100533387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87090020147939541601422365 32658757555477328100533387)
      ·
        refine ⟨48988136333215992150800081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32658757555477328100533387 48988136333215992150800081)
        ·
          refine ⟨36741102249911994113100061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48988136333215992150800081 36741102249911994113100061)
          ·
            refine ⟨13777913343716997792412523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36741102249911994113100061 13777913343716997792412523)
            ·
              refine ⟨20666870015575496688618785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13777913343716997792412523 20666870015575496688618785)
              ·
                refine ⟨15500152511681622516464089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20666870015575496688618785 15500152511681622516464089)
                ·
                  refine ⟨11625114383761216887348067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15500152511681622516464089 11625114383761216887348067)
                  ·
                    refine ⟨17437671575641825331022101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11625114383761216887348067 17437671575641825331022101)
                    ·
                      refine ⟨817390855108210562391661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17437671575641825331022101 817390855108210562391661)
                      ·
                        rfl

theorem cell23_1591863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1591863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591863 prefixEnd_1591863 := by exact prefixLift 1591863
  have htrace : WordTrace (prefixWord ++ tailWord_1591863) baseStart_1591863 baseEnd_1591863 := by
    simpa [prefixWord, tailWord_1591863, baseEnd_1591863] using wordTrace_append hprefix tailTrace_1591863
  have hstable : (prefixWord ++ tailWord_1591863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591863).length < 2 ^ (prefixWord ++ tailWord_1591863).sum := by decide
  have hdescent : baseEnd_1591863 < baseStart_1591863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591913 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_1591913 : Nat := 118140960795 + 1591913 * 2 ^ 59
def prefixEnd_1591913 : Nat := 4983230072969 + 3 ^ 40 * 1591913 * 2
def baseEnd_1591913 : Nat := 817416529140935366766431

theorem tailTrace_1591913 : CollatzResearch.WordTrace tailWord_1591913 prefixEnd_1591913 817416529140935366766431 := by
  unfold tailWord_1591913
  simp only [CollatzResearch.WordTrace]
  refine ⟨58061837081778552940268393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38707891387852368626845595 58061837081778552940268393)
  ·
    refine ⟨43546377811333914705201295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58061837081778552940268393 43546377811333914705201295)
    ·
      refine ⟨65319566717000872057801943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43546377811333914705201295 65319566717000872057801943)
      ·
        refine ⟨97979350075501308086702915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65319566717000872057801943 97979350075501308086702915)
        ·
          refine ⟨146969025113251962130054373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97979350075501308086702915 146969025113251962130054373)
          ·
            refine ⟨27556692208734742899385195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146969025113251962130054373 27556692208734742899385195)
            ·
              refine ⟨41335038313102114349077793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27556692208734742899385195 41335038313102114349077793)
              ·
                refine ⟨31001278734826585761808345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41335038313102114349077793 31001278734826585761808345)
                ·
                  refine ⟨23250959051119939321356259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31001278734826585761808345 23250959051119939321356259)
                  ·
                    refine ⟨34876438576679908982034389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23250959051119939321356259 34876438576679908982034389)
                    ·
                      refine ⟨817416529140935366766431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34876438576679908982034389 817416529140935366766431)
                      ·
                        rfl

theorem cell23_1591913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_1591913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591913 prefixEnd_1591913 := by exact prefixLift 1591913
  have htrace : WordTrace (prefixWord ++ tailWord_1591913) baseStart_1591913 baseEnd_1591913 := by
    simpa [prefixWord, tailWord_1591913, baseEnd_1591913] using wordTrace_append hprefix tailTrace_1591913
  have hstable : (prefixWord ++ tailWord_1591913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591913).length < 2 ^ (prefixWord ++ tailWord_1591913).sum := by decide
  have hdescent : baseEnd_1591913 < baseStart_1591913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591987 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4]
def baseStart_1591987 : Nat := 118140960795 + 1591987 * 2 ^ 59
def prefixEnd_1591987 : Nat := 4983230072969 + 3 ^ 40 * 1591987 * 2
def baseEnd_1591987 : Nat := 817454526709368077241091

theorem tailTrace_1591987 : CollatzResearch.WordTrace tailWord_1591987 prefixEnd_1591987 817454526709368077241091 := by
  unfold tailWord_1591987
  simp only [CollatzResearch.WordTrace]
  refine ⟨58064536083510463578462215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38709690722340309052308143 58064536083510463578462215)
  ·
    refine ⟨87096804125265695367693323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58064536083510463578462215 87096804125265695367693323)
    ·
      refine ⟨130645206187898543051539985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87096804125265695367693323 130645206187898543051539985)
      ·
        refine ⟨97983904640923907288654989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130645206187898543051539985 97983904640923907288654989)
        ·
          refine ⟨36743964240346465233245621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97983904640923907288654989 36743964240346465233245621)
          ·
            refine ⟨3444746647532481115616777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36743964240346465233245621 3444746647532481115616777)
            ·
              refine ⟨2583559985649360836712583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444746647532481115616777 2583559985649360836712583)
              ·
                refine ⟨3875339978474041255068875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583559985649360836712583 3875339978474041255068875)
                ·
                  refine ⟨5813009967711061882603313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875339978474041255068875 5813009967711061882603313)
                  ·
                    refine ⟨4359757475783296411952485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5813009967711061882603313 4359757475783296411952485)
                    ·
                      refine ⟨817454526709368077241091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4359757475783296411952485 817454526709368077241091)
                      ·
                        rfl

theorem cell23_1591987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_1591987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591987 prefixEnd_1591987 := by exact prefixLift 1591987
  have htrace : WordTrace (prefixWord ++ tailWord_1591987) baseStart_1591987 baseEnd_1591987 := by
    simpa [prefixWord, tailWord_1591987, baseEnd_1591987] using wordTrace_append hprefix tailTrace_1591987
  have hstable : (prefixWord ++ tailWord_1591987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591987).length < 2 ^ (prefixWord ++ tailWord_1591987).sum := by decide
  have hdescent : baseEnd_1591987 < baseStart_1591987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591991 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_1591991 : Nat := 118140960795 + 1591991 * 2 ^ 59
def prefixEnd_1591991 : Nat := 4983230072969 + 3 ^ 40 * 1591991 * 2
def baseEnd_1591991 : Nat := 817456580631986061591073

theorem tailTrace_1591991 : CollatzResearch.WordTrace tailWord_1591991 prefixEnd_1591991 817456580631986061591073 := by
  unfold tailWord_1591991
  simp only [CollatzResearch.WordTrace]
  refine ⟨58064681975495972261607827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38709787983663981507738551 58064681975495972261607827)
  ·
    refine ⟨87097022963243958392411741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58064681975495972261607827 87097022963243958392411741)
    ·
      refine ⟨32661383611216484397154403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87097022963243958392411741 32661383611216484397154403)
      ·
        refine ⟨48992075416824726595731605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32661383611216484397154403 48992075416824726595731605)
        ·
          refine ⟨2296503535163659059174919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48992075416824726595731605 2296503535163659059174919)
          ·
            refine ⟨3444755302745488588762379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296503535163659059174919 3444755302745488588762379)
            ·
              refine ⟨5167132954118232883143569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444755302745488588762379 5167132954118232883143569)
              ·
                refine ⟨3875349715588674662357677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167132954118232883143569 3875349715588674662357677)
                ·
                  refine ⟨1453256143345752998384129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3875349715588674662357677 1453256143345752998384129)
                  ·
                    refine ⟨1089942107509314748788097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453256143345752998384129 1089942107509314748788097)
                    ·
                      refine ⟨817456580631986061591073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089942107509314748788097 817456580631986061591073)
                      ·
                        rfl

theorem cell23_1591991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_1591991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591991 prefixEnd_1591991 := by exact prefixLift 1591991
  have htrace : WordTrace (prefixWord ++ tailWord_1591991) baseStart_1591991 baseEnd_1591991 := by
    simpa [prefixWord, tailWord_1591991, baseEnd_1591991] using wordTrace_append hprefix tailTrace_1591991
  have hstable : (prefixWord ++ tailWord_1591991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591991).length < 2 ^ (prefixWord ++ tailWord_1591991).sum := by decide
  have hdescent : baseEnd_1591991 < baseStart_1591991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591997 : List Nat := [1, 4, 1, 2, 1, 4, 3, 7]
def baseStart_1591997 : Nat := 118140960795 + 1591997 * 2 ^ 59
def prefixEnd_1591997 : Nat := 4983230072969 + 3 ^ 40 * 1591997 * 2
def baseEnd_1591997 : Nat := 30276283759848631041335

theorem tailTrace_1591997 : CollatzResearch.WordTrace tailWord_1591997 prefixEnd_1591997 30276283759848631041335 := by
  unfold tailWord_1591997
  simp only [CollatzResearch.WordTrace]
  refine ⟨58064900813474235286326245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38709933875649490190884163 58064900813474235286326245)
  ·
    refine ⟨10887168902526419116186171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58064900813474235286326245 10887168902526419116186171)
    ·
      refine ⟨16330753353789628674279257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10887168902526419116186171 16330753353789628674279257)
      ·
        refine ⟨12248065015342221505709443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16330753353789628674279257 12248065015342221505709443)
        ·
          refine ⟨18372097523013332258564165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12248065015342221505709443 18372097523013332258564165)
          ·
            refine ⟨3444768285564999798480781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18372097523013332258564165 3444768285564999798480781)
            ·
              refine ⟨1291788107086874924430293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444768285564999798480781 1291788107086874924430293)
              ·
                refine ⟨30276283759848631041335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1291788107086874924430293 30276283759848631041335)
                ·
                  rfl

theorem cell23_1591997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 7].length) (baseStart_1591997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591997 prefixEnd_1591997 := by exact prefixLift 1591997
  have htrace : WordTrace (prefixWord ++ tailWord_1591997) baseStart_1591997 baseEnd_1591997 := by
    simpa [prefixWord, tailWord_1591997, baseEnd_1591997] using wordTrace_append hprefix tailTrace_1591997
  have hstable : (prefixWord ++ tailWord_1591997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591997).length < 2 ^ (prefixWord ++ tailWord_1591997).sum := by decide
  have hdescent : baseEnd_1591997 < baseStart_1591997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592008 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_1592008 : Nat := 118140960795 + 1592008 * 2 ^ 59
def prefixEnd_1592008 : Nat := 4983230072969 + 3 ^ 40 * 1592008 * 2
def baseEnd_1592008 : Nat := 817465309803112495078495

theorem tailTrace_1592008 : CollatzResearch.WordTrace tailWord_1592008 prefixEnd_1592008 817465309803112495078495 := by
  unfold tailWord_1592008
  simp only [CollatzResearch.WordTrace]
  refine ⟨29032651008217192082488339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38710201344289589443317785 29032651008217192082488339)
  ·
    refine ⟨43548976512325788123732509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29032651008217192082488339 43548976512325788123732509)
    ·
      refine ⟨16330866192122170546399691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43548976512325788123732509 16330866192122170546399691)
      ·
        refine ⟨24496299288183255819599537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16330866192122170546399691 24496299288183255819599537)
        ·
          refine ⟨18372224466137441864699653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24496299288183255819599537 18372224466137441864699653)
          ·
            refine ⟨3444792087400770349631185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18372224466137441864699653 3444792087400770349631185)
            ·
              refine ⟨2583594065550577762223389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444792087400770349631185 2583594065550577762223389)
              ·
                refine ⟨968847774581466660833771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583594065550577762223389 968847774581466660833771)
                ·
                  refine ⟨1453271661872199991250657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968847774581466660833771 1453271661872199991250657)
                  ·
                    refine ⟨1089953746404149993437993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453271661872199991250657 1089953746404149993437993)
                    ·
                      refine ⟨817465309803112495078495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089953746404149993437993 817465309803112495078495)
                      ·
                        rfl

theorem cell23_1592008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_1592008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592008 prefixEnd_1592008 := by exact prefixLift 1592008
  have htrace : WordTrace (prefixWord ++ tailWord_1592008) baseStart_1592008 baseEnd_1592008 := by
    simpa [prefixWord, tailWord_1592008, baseEnd_1592008] using wordTrace_append hprefix tailTrace_1592008
  have hstable : (prefixWord ++ tailWord_1592008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592008).length < 2 ^ (prefixWord ++ tailWord_1592008).sum := by decide
  have hdescent : baseEnd_1592008 < baseStart_1592008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592018 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1592018 : Nat := 118140960795 + 1592018 * 2 ^ 59
def prefixEnd_1592018 : Nat := 4983230072969 + 3 ^ 40 * 1592018 * 2
def baseEnd_1592018 : Nat := 272490148203219151984483

theorem tailTrace_1592018 : CollatzResearch.WordTrace tailWord_1592018 prefixEnd_1592018 272490148203219151984483 := by
  unfold tailWord_1592018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516416686599538968210177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38710444497598770581893805 14516416686599538968210177)
  ·
    refine ⟨10887312514949654226157633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14516416686599538968210177 10887312514949654226157633)
    ·
      refine ⟨8165484386212240669618225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10887312514949654226157633 8165484386212240669618225)
      ·
        refine ⟨6124113289659180502213669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8165484386212240669618225 6124113289659180502213669)
        ·
          refine ⟨1148271241811096344165063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6124113289659180502213669 1148271241811096344165063)
          ·
            refine ⟨1722406862716644516247595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148271241811096344165063 1722406862716644516247595)
            ·
              refine ⟨2583610294074966774371393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722406862716644516247595 2583610294074966774371393)
              ·
                refine ⟨1937707720556225080778545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583610294074966774371393 1937707720556225080778545)
                ·
                  refine ⟨1453280790417168810583909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937707720556225080778545 1453280790417168810583909)
                  ·
                    refine ⟨272490148203219151984483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453280790417168810583909 272490148203219151984483)
                    ·
                      rfl

theorem cell23_1592018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1592018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592018 prefixEnd_1592018 := by exact prefixLift 1592018
  have htrace : WordTrace (prefixWord ++ tailWord_1592018) baseStart_1592018 baseEnd_1592018 := by
    simpa [prefixWord, tailWord_1592018, baseEnd_1592018] using wordTrace_append hprefix tailTrace_1592018
  have hstable : (prefixWord ++ tailWord_1592018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592018).length < 2 ^ (prefixWord ++ tailWord_1592018).sum := by decide
  have hdescent : baseEnd_1592018 < baseStart_1592018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592024 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1592024 : Nat := 118140960795 + 1592024 * 2 ^ 59
def prefixEnd_1592024 : Nat := 4983230072969 + 3 ^ 40 * 1592024 * 2
def baseEnd_1592024 : Nat := 817473525493584432478421

theorem tailTrace_1592024 : CollatzResearch.WordTrace tailWord_1592024 prefixEnd_1592024 817473525493584432478421 := by
  unfold tailWord_1592024
  simp only [CollatzResearch.WordTrace]
  refine ⟨29032942792188209448779563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38710590389584279265039417 29032942792188209448779563)
  ·
    refine ⟨43549414188282314173169345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29032942792188209448779563 43549414188282314173169345)
    ·
      refine ⟨32662060641211735629877009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43549414188282314173169345 32662060641211735629877009)
      ·
        refine ⟨24496545480908801722407757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32662060641211735629877009 24496545480908801722407757)
        ·
          refine ⟨9186204555340800645902909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24496545480908801722407757 9186204555340800645902909)
          ·
            refine ⟨3444826708252800242213591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9186204555340800645902909 3444826708252800242213591)
            ·
              refine ⟨5167240062379200363320387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444826708252800242213591 5167240062379200363320387)
              ·
                refine ⟨7750860093568800544980581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167240062379200363320387 7750860093568800544980581)
                ·
                  refine ⟨1453286267544150102183859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7750860093568800544980581 1453286267544150102183859)
                  ·
                    refine ⟨2179929401316225153275789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453286267544150102183859 2179929401316225153275789)
                    ·
                      refine ⟨817473525493584432478421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2179929401316225153275789 817473525493584432478421)
                      ·
                        rfl

theorem cell23_1592024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1592024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592024 prefixEnd_1592024 := by exact prefixLift 1592024
  have htrace : WordTrace (prefixWord ++ tailWord_1592024) baseStart_1592024 baseEnd_1592024 := by
    simpa [prefixWord, tailWord_1592024, baseEnd_1592024] using wordTrace_append hprefix tailTrace_1592024
  have hstable : (prefixWord ++ tailWord_1592024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592024).length < 2 ^ (prefixWord ++ tailWord_1592024).sum := by decide
  have hdescent : baseEnd_1592024 < baseStart_1592024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592097 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1592097 : Nat := 118140960795 + 1592097 * 2 ^ 59
def prefixEnd_1592097 : Nat := 4983230072969 + 3 ^ 40 * 1592097 * 2
def baseEnd_1592097 : Nat := 817511009581362646865585

theorem tailTrace_1592097 : CollatzResearch.WordTrace tailWord_1592097 prefixEnd_1592097 817511009581362646865585 := by
  unfold tailWord_1592097
  simp only [CollatzResearch.WordTrace]
  refine ⟨58068548113111952364966545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38712365408741301576644363 58068548113111952364966545)
  ·
    refine ⟨43551411084833964273724909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58068548113111952364966545 43551411084833964273724909)
    ·
      refine ⟨16331779156812736602646841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43551411084833964273724909 16331779156812736602646841)
      ·
        refine ⟨12248834367609552451985131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16331779156812736602646841 12248834367609552451985131)
        ·
          refine ⟨18373251551414328677977697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12248834367609552451985131 18373251551414328677977697)
          ·
            refine ⟨13779938663560746508483273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18373251551414328677977697 13779938663560746508483273)
            ·
              refine ⟨10334953997670559881362455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13779938663560746508483273 10334953997670559881362455)
              ·
                refine ⟨15502430996505839822043683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10334953997670559881362455 15502430996505839822043683)
                ·
                  refine ⟨23253646494758759733065525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15502430996505839822043683 23253646494758759733065525)
                  ·
                    refine ⟨2180029358883633724974893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23253646494758759733065525 2180029358883633724974893)
                    ·
                      refine ⟨817511009581362646865585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180029358883633724974893 817511009581362646865585)
                      ·
                        rfl

theorem cell23_1592097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1592097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592097 prefixEnd_1592097 := by exact prefixLift 1592097
  have htrace : WordTrace (prefixWord ++ tailWord_1592097) baseStart_1592097 baseEnd_1592097 := by
    simpa [prefixWord, tailWord_1592097, baseEnd_1592097] using wordTrace_append hprefix tailTrace_1592097
  have hstable : (prefixWord ++ tailWord_1592097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592097).length < 2 ^ (prefixWord ++ tailWord_1592097).sum := by decide
  have hdescent : baseEnd_1592097 < baseStart_1592097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592098 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_1592098 : Nat := 118140960795 + 1592098 * 2 ^ 59
def prefixEnd_1592098 : Nat := 4983230072969 + 3 ^ 40 * 1592098 * 2
def baseEnd_1592098 : Nat := 817511523062017142953081

theorem tailTrace_1592098 : CollatzResearch.WordTrace tailWord_1592098 prefixEnd_1592098 817511523062017142953081 := by
  unfold tailWord_1592098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517146146527082383938237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38712389724072219690501965 14517146146527082383938237)
  ·
    refine ⟨5443929804947655893976839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14517146146527082383938237 5443929804947655893976839)
    ·
      refine ⟨8165894707421483840965259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443929804947655893976839 8165894707421483840965259)
      ·
        refine ⟨12248842061132225761447889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8165894707421483840965259 12248842061132225761447889)
        ·
          refine ⟨9186631545849169321085917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12248842061132225761447889 9186631545849169321085917)
          ·
            refine ⟨3444986829693438495407219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9186631545849169321085917 3444986829693438495407219)
            ·
              refine ⟨5167480244540157743110829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444986829693438495407219 5167480244540157743110829)
              ·
                refine ⟨1937805091702559153666561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5167480244540157743110829 1937805091702559153666561)
                ·
                  refine ⟨1453353818776919365249921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937805091702559153666561 1453353818776919365249921)
                  ·
                    refine ⟨1090015364082689523937441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453353818776919365249921 1090015364082689523937441)
                    ·
                      refine ⟨817511523062017142953081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090015364082689523937441 817511523062017142953081)
                      ·
                        rfl

theorem cell23_1592098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_1592098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592098 prefixEnd_1592098 := by exact prefixLift 1592098
  have htrace : WordTrace (prefixWord ++ tailWord_1592098) baseStart_1592098 baseEnd_1592098 := by
    simpa [prefixWord, tailWord_1592098, baseEnd_1592098] using wordTrace_append hprefix tailTrace_1592098
  have hstable : (prefixWord ++ tailWord_1592098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592098).length < 2 ^ (prefixWord ++ tailWord_1592098).sum := by decide
  have hdescent : baseEnd_1592098 < baseStart_1592098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592127 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1592127 : Nat := 118140960795 + 1592127 * 2 ^ 59
def prefixEnd_1592127 : Nat := 4983230072969 + 3 ^ 40 * 1592127 * 2
def baseEnd_1592127 : Nat := 817526414000997529490447

theorem tailTrace_1592127 : CollatzResearch.WordTrace tailWord_1592127 prefixEnd_1592127 817526414000997529490447 := by
  unfold tailWord_1592127
  simp only [CollatzResearch.WordTrace]
  refine ⟨58069642303003267488558635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38713094868668844992372423 58069642303003267488558635)
  ·
    refine ⟨87104463454504901232837953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58069642303003267488558635 87104463454504901232837953)
    ·
      refine ⟨65328347590878675924628465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87104463454504901232837953 65328347590878675924628465)
      ·
        refine ⟨48996260693159006943471349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65328347590878675924628465 48996260693159006943471349)
        ·
          refine ⟨4593399439983656900950439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48996260693159006943471349 4593399439983656900950439)
          ·
            refine ⟨6890099159975485351425659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593399439983656900950439 6890099159975485351425659)
            ·
              refine ⟨10335148739963228027138489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890099159975485351425659 10335148739963228027138489)
              ·
                refine ⟨7751361554972421020353867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10335148739963228027138489 7751361554972421020353867)
                ·
                  refine ⟨11627042332458631530530801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751361554972421020353867 11627042332458631530530801)
                  ·
                    refine ⟨8720281749343973647898101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11627042332458631530530801 8720281749343973647898101)
                    ·
                      refine ⟨817526414000997529490447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8720281749343973647898101 817526414000997529490447)
                      ·
                        rfl

theorem cell23_1592127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1592127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592127 prefixEnd_1592127 := by exact prefixLift 1592127
  have htrace : WordTrace (prefixWord ++ tailWord_1592127) baseStart_1592127 baseEnd_1592127 := by
    simpa [prefixWord, tailWord_1592127, baseEnd_1592127] using wordTrace_append hprefix tailTrace_1592127
  have hstable : (prefixWord ++ tailWord_1592127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592127).length < 2 ^ (prefixWord ++ tailWord_1592127).sum := by decide
  have hdescent : baseEnd_1592127 < baseStart_1592127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592132 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1592132 : Nat := 118140960795 + 1592132 * 2 ^ 59
def prefixEnd_1592132 : Nat := 4983230072969 + 3 ^ 40 * 1592132 * 2
def baseEnd_1592132 : Nat := 817528981404270009927925

theorem tailTrace_1592132 : CollatzResearch.WordTrace tailWord_1592132 prefixEnd_1592132 817528981404270009927925 := by
  unfold tailWord_1592132
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034912333992576671245325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38713216445323435561660433 29034912333992576671245325)
  ·
    refine ⟨10888092125247216251716997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29034912333992576671245325 10888092125247216251716997)
    ·
      refine ⟨2041517273483853047196937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10888092125247216251716997 2041517273483853047196937)
      ·
        refine ⟨1531137955112889785397703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2041517273483853047196937 1531137955112889785397703)
        ·
          refine ⟨2296706932669334678096555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531137955112889785397703 2296706932669334678096555)
          ·
            refine ⟨3445060399004002017144833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296706932669334678096555 3445060399004002017144833)
            ·
              refine ⟨2583795299253001512858625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445060399004002017144833 2583795299253001512858625)
              ·
                refine ⟨1937846474439751134643969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583795299253001512858625 1937846474439751134643969)
                ·
                  refine ⟨1453384855829813350982977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937846474439751134643969 1453384855829813350982977)
                  ·
                    refine ⟨1090038641872360013237233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453384855829813350982977 1090038641872360013237233)
                    ·
                      refine ⟨817528981404270009927925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090038641872360013237233 817528981404270009927925)
                      ·
                        rfl

theorem cell23_1592132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1592132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592132 prefixEnd_1592132 := by exact prefixLift 1592132
  have htrace : WordTrace (prefixWord ++ tailWord_1592132) baseStart_1592132 baseEnd_1592132 := by
    simpa [prefixWord, tailWord_1592132, baseEnd_1592132] using wordTrace_append hprefix tailTrace_1592132
  have hstable : (prefixWord ++ tailWord_1592132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592132).length < 2 ^ (prefixWord ++ tailWord_1592132).sum := by decide
  have hdescent : baseEnd_1592132 < baseStart_1592132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592147 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 7, 4]
def baseStart_1592147 : Nat := 118140960795 + 1592147 * 2 ^ 59
def prefixEnd_1592147 : Nat := 4983230072969 + 3 ^ 40 * 1592147 * 2
def baseEnd_1592147 : Nat := 272512227871362483746785

theorem tailTrace_1592147 : CollatzResearch.WordTrace tailWord_1592147 prefixEnd_1592147 272512227871362483746785 := by
  unfold tailWord_1592147
  simp only [CollatzResearch.WordTrace]
  refine ⟨58070371762930810904286695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38713581175287207269524463 58070371762930810904286695)
  ·
    refine ⟨87105557644396216356430043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58070371762930810904286695 87105557644396216356430043)
    ·
      refine ⟨130658336466594324534645065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87105557644396216356430043 130658336466594324534645065)
      ·
        refine ⟨97993752349945743400983799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130658336466594324534645065 97993752349945743400983799)
        ·
          refine ⟨146990628524918615101475699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97993752349945743400983799 146990628524918615101475699)
          ·
            refine ⟨220485942787377922652213549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146990628524918615101475699 220485942787377922652213549)
            ·
              refine ⟨82682228545266720994580081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220485942787377922652213549 82682228545266720994580081)
              ·
                refine ⟨62011671408950040745935061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82682228545266720994580081 62011671408950040745935061)
                ·
                  refine ⟨1453398548647266579982853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62011671408950040745935061 1453398548647266579982853)
                  ·
                    refine ⟨272512227871362483746785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453398548647266579982853 272512227871362483746785)
                    ·
                      rfl

theorem cell23_1592147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 4].length) (baseStart_1592147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592147 prefixEnd_1592147 := by exact prefixLift 1592147
  have htrace : WordTrace (prefixWord ++ tailWord_1592147) baseStart_1592147 baseEnd_1592147 := by
    simpa [prefixWord, tailWord_1592147, baseEnd_1592147] using wordTrace_append hprefix tailTrace_1592147
  have hstable : (prefixWord ++ tailWord_1592147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592147).length < 2 ^ (prefixWord ++ tailWord_1592147).sum := by decide
  have hdescent : baseEnd_1592147 < baseStart_1592147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592154 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_1592154 : Nat := 118140960795 + 1592154 * 2 ^ 59
def prefixEnd_1592154 : Nat := 4983230072969 + 3 ^ 40 * 1592154 * 2
def baseEnd_1592154 : Nat := 817540277978668923852823

theorem tailTrace_1592154 : CollatzResearch.WordTrace tailWord_1592154 prefixEnd_1592154 817540277978668923852823 := by
  unfold tailWord_1592154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517656768476362774947879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38713751382603634066527677 14517656768476362774947879)
  ·
    refine ⟨21776485152714544162421819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14517656768476362774947879 21776485152714544162421819)
    ·
      refine ⟨32664727729071816243632729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21776485152714544162421819 32664727729071816243632729)
      ·
        refine ⟨24498545796803862182724547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32664727729071816243632729 24498545796803862182724547)
        ·
          refine ⟨36747818695205793274086821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24498545796803862182724547 36747818695205793274086821)
          ·
            refine ⟨6890216005351086238891279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36747818695205793274086821 6890216005351086238891279)
            ·
              refine ⟨10335324008026629358336919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890216005351086238891279 10335324008026629358336919)
              ·
                refine ⟨15502986012039944037505379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335324008026629358336919 15502986012039944037505379)
                ·
                  refine ⟨23254479018059916056258069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15502986012039944037505379 23254479018059916056258069)
                  ·
                    refine ⟨1090053703971558565137097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23254479018059916056258069 1090053703971558565137097)
                    ·
                      refine ⟨817540277978668923852823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090053703971558565137097 817540277978668923852823)
                      ·
                        rfl

theorem cell23_1592154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_1592154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592154 prefixEnd_1592154 := by exact prefixLift 1592154
  have htrace : WordTrace (prefixWord ++ tailWord_1592154) baseStart_1592154 baseEnd_1592154 := by
    simpa [prefixWord, tailWord_1592154, baseEnd_1592154] using wordTrace_append hprefix tailTrace_1592154
  have hstable : (prefixWord ++ tailWord_1592154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592154).length < 2 ^ (prefixWord ++ tailWord_1592154).sum := by decide
  have hdescent : baseEnd_1592154 < baseStart_1592154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592164 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1592164 : Nat := 118140960795 + 1592164 * 2 ^ 59
def prefixEnd_1592164 : Nat := 4983230072969 + 3 ^ 40 * 1592164 * 2
def baseEnd_1592164 : Nat := 272515137595071294909259

theorem tailTrace_1592164 : CollatzResearch.WordTrace tailWord_1592164 prefixEnd_1592164 272515137595071294909259 := by
  unfold tailWord_1592164
  simp only [CollatzResearch.WordTrace]
  refine ⟨29035495901934611403827773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38713994535912815205103697 29035495901934611403827773)
  ·
    refine ⟨10888310963225479276435415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29035495901934611403827773 10888310963225479276435415)
    ·
      refine ⟨16332466444838218914653123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10888310963225479276435415 16332466444838218914653123)
      ·
        refine ⟨24498699667257328371979685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16332466444838218914653123 24498699667257328371979685)
        ·
          refine ⟨4593506187610749069746191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24498699667257328371979685 4593506187610749069746191)
          ·
            refine ⟨6890259281416123604619287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593506187610749069746191 6890259281416123604619287)
            ·
              refine ⟨10335388922124185406928931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890259281416123604619287 10335388922124185406928931)
              ·
                refine ⟨15503083383186278110393397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335388922124185406928931 15503083383186278110393397)
                ·
                  refine ⟨1453414067173713572849381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15503083383186278110393397 1453414067173713572849381)
                  ·
                    refine ⟨272515137595071294909259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453414067173713572849381 272515137595071294909259)
                    ·
                      rfl

theorem cell23_1592164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1592164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592164 prefixEnd_1592164 := by exact prefixLift 1592164
  have htrace : WordTrace (prefixWord ++ tailWord_1592164) baseStart_1592164 baseEnd_1592164 := by
    simpa [prefixWord, tailWord_1592164, baseEnd_1592164] using wordTrace_append hprefix tailTrace_1592164
  have hstable : (prefixWord ++ tailWord_1592164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592164).length < 2 ^ (prefixWord ++ tailWord_1592164).sum := by decide
  have hdescent : baseEnd_1592164 < baseStart_1592164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592197 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1592197 : Nat := 118140960795 + 1592197 * 2 ^ 59
def prefixEnd_1592197 : Nat := 4983230072969 + 3 ^ 40 * 1592197 * 2
def baseEnd_1592197 : Nat := 817562357646812255615125

theorem tailTrace_1592197 : CollatzResearch.WordTrace tailWord_1592197 prefixEnd_1592197 817562357646812255615125 := by
  unfold tailWord_1592197
  simp only [CollatzResearch.WordTrace]
  refine ⟨58072195412749669443606845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38714796941833112962404563 58072195412749669443606845)
  ·
    refine ⟨21777073279781126041352567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58072195412749669443606845 21777073279781126041352567)
    ·
      refine ⟨32665609919671689062028851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21777073279781126041352567 32665609919671689062028851)
      ·
        refine ⟨48998414879507533593043277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32665609919671689062028851 48998414879507533593043277)
        ·
          refine ⟨18374405579815325097391229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48998414879507533593043277 18374405579815325097391229)
          ·
            refine ⟨6890402092430746911521711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18374405579815325097391229 6890402092430746911521711)
            ·
              refine ⟨10335603138646120367282567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890402092430746911521711 10335603138646120367282567)
              ·
                refine ⟨15503404707969180550923851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335603138646120367282567 15503404707969180550923851)
                ·
                  refine ⟨23255107061953770826385777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15503404707969180550923851 23255107061953770826385777)
                  ·
                    refine ⟨17441330296465328119789333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23255107061953770826385777 17441330296465328119789333)
                    ·
                      refine ⟨817562357646812255615125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17441330296465328119789333 817562357646812255615125)
                      ·
                        rfl

theorem cell23_1592197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1592197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592197 prefixEnd_1592197 := by exact prefixLift 1592197
  have htrace : WordTrace (prefixWord ++ tailWord_1592197) baseStart_1592197 baseEnd_1592197 := by
    simpa [prefixWord, tailWord_1592197, baseEnd_1592197] using wordTrace_append hprefix tailTrace_1592197
  have hstable : (prefixWord ++ tailWord_1592197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592197).length < 2 ^ (prefixWord ++ tailWord_1592197).sum := by decide
  have hdescent : baseEnd_1592197 < baseStart_1592197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592221 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1592221 : Nat := 118140960795 + 1592221 * 2 ^ 59
def prefixEnd_1592221 : Nat := 4983230072969 + 3 ^ 40 * 1592221 * 2
def baseEnd_1592221 : Nat := 817574681182520161715015

theorem tailTrace_1592221 : CollatzResearch.WordTrace tailWord_1592221 prefixEnd_1592221 817574681182520161715015 := by
  unfold tailWord_1592221
  simp only [CollatzResearch.WordTrace]
  refine ⟨58073070764662721542480517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38715380509775147694987011 58073070764662721542480517)
  ·
    refine ⟨10888700768374260289215097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58073070764662721542480517 10888700768374260289215097)
    ·
      refine ⟨8166525576280695216911323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10888700768374260289215097 8166525576280695216911323)
      ·
        refine ⟨12249788364421042825366985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166525576280695216911323 12249788364421042825366985)
        ·
          refine ⟨9187341273315782119025239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12249788364421042825366985 9187341273315782119025239)
          ·
            refine ⟨13781011909973673178537859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187341273315782119025239 13781011909973673178537859)
            ·
              refine ⟨20671517864960509767806789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13781011909973673178537859 20671517864960509767806789)
              ·
                refine ⟨3875909599680095581463773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20671517864960509767806789 3875909599680095581463773)
                ·
                  refine ⟨1453466099880035843048915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3875909599680095581463773 1453466099880035843048915)
                  ·
                    refine ⟨2180199149820053764573373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453466099880035843048915 2180199149820053764573373)
                    ·
                      refine ⟨817574681182520161715015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180199149820053764573373 817574681182520161715015)
                      ·
                        rfl

theorem cell23_1592221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1592221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592221 prefixEnd_1592221 := by exact prefixLift 1592221
  have htrace : WordTrace (prefixWord ++ tailWord_1592221) baseStart_1592221 baseEnd_1592221 := by
    simpa [prefixWord, tailWord_1592221, baseEnd_1592221] using wordTrace_append hprefix tailTrace_1592221
  have hstable : (prefixWord ++ tailWord_1592221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592221).length < 2 ^ (prefixWord ++ tailWord_1592221).sum := by decide
  have hdescent : baseEnd_1592221 < baseStart_1592221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592224 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_1592224 : Nat := 118140960795 + 1592224 * 2 ^ 59
def prefixEnd_1592224 : Nat := 4983230072969 + 3 ^ 40 * 1592224 * 2
def baseEnd_1592224 : Nat := 272525407208161216659167

theorem tailTrace_1592224 : CollatzResearch.WordTrace tailWord_1592224 prefixEnd_1592224 272525407208161216659167 := by
  unfold tailWord_1592224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29036590091825926527419863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38715453455767902036559817 29036590091825926527419863)
  ·
    refine ⟨43554885137738889791129795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29036590091825926527419863 43554885137738889791129795)
    ·
      refine ⟨65332327706608334686694693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43554885137738889791129795 65332327706608334686694693)
      ·
        refine ⟨12249811444989062753755255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65332327706608334686694693 12249811444989062753755255)
        ·
          refine ⟨18374717167483594130632883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249811444989062753755255 18374717167483594130632883)
          ·
            refine ⟨27562075751225391195949325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18374717167483594130632883 27562075751225391195949325)
            ·
              refine ⟨10335778406709521698480997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27562075751225391195949325 10335778406709521698480997)
              ·
                refine ⟨1937958451258035318465187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10335778406709521698480997 1937958451258035318465187)
                ·
                  refine ⟨2906937676887052977697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937958451258035318465187 2906937676887052977697781)
                  ·
                    refine ⟨272525407208161216659167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2906937676887052977697781 272525407208161216659167)
                    ·
                      rfl

theorem cell23_1592224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_1592224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592224 prefixEnd_1592224 := by exact prefixLift 1592224
  have htrace : WordTrace (prefixWord ++ tailWord_1592224) baseStart_1592224 baseEnd_1592224 := by
    simpa [prefixWord, tailWord_1592224, baseEnd_1592224] using wordTrace_append hprefix tailTrace_1592224
  have hstable : (prefixWord ++ tailWord_1592224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592224).length < 2 ^ (prefixWord ++ tailWord_1592224).sum := by decide
  have hdescent : baseEnd_1592224 < baseStart_1592224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592262 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1592262 : Nat := 118140960795 + 1592262 * 2 ^ 59
def prefixEnd_1592262 : Nat := 4983230072969 + 3 ^ 40 * 1592262 * 2
def baseEnd_1592262 : Nat := 90843970432150500144703

theorem tailTrace_1592262 : CollatzResearch.WordTrace tailWord_1592262 prefixEnd_1592262 90843970432150500144703 := by
  unfold tailWord_1592262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814830192422318298272595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38716377438342790363148693 1814830192422318298272595)
  ·
    refine ⟨2722245288633477447408893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814830192422318298272595 2722245288633477447408893)
    ·
      refine ⟨1020841983237554042778335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2722245288633477447408893 1020841983237554042778335)
      ·
        refine ⟨1531262974856331064167503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020841983237554042778335 1531262974856331064167503)
        ·
          refine ⟨2296894462284496596251255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531262974856331064167503 2296894462284496596251255)
          ·
            refine ⟨3445341693426744894376883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296894462284496596251255 3445341693426744894376883)
            ·
              refine ⟨5168012540140117341565325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445341693426744894376883 5168012540140117341565325)
              ·
                refine ⟨1938004702552544003086997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168012540140117341565325 1938004702552544003086997)
                ·
                  refine ⟨90843970432150500144703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1938004702552544003086997 90843970432150500144703)
                  ·
                    rfl

theorem cell23_1592262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1592262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592262 prefixEnd_1592262 := by exact prefixLift 1592262
  have htrace : WordTrace (prefixWord ++ tailWord_1592262) baseStart_1592262 baseEnd_1592262 := by
    simpa [prefixWord, tailWord_1592262, baseEnd_1592262] using wordTrace_append hprefix tailTrace_1592262
  have hstable : (prefixWord ++ tailWord_1592262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592262).length < 2 ^ (prefixWord ++ tailWord_1592262).sum := by decide
  have hdescent : baseEnd_1592262 < baseStart_1592262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592267 : List Nat := [1, 1, 1, 1, 3, 5, 1, 10]
def baseStart_1592267 : Nat := 118140960795 + 1592267 * 2 ^ 59
def prefixEnd_1592267 : Nat := 4983230072969 + 3 ^ 40 * 1592267 * 2
def baseEnd_1592267 : Nat := 30281418566393591916289

theorem tailTrace_1592267 : CollatzResearch.WordTrace tailWord_1592267 prefixEnd_1592267 30281418566393591916289 := by
  unfold tailWord_1592267
  simp only [CollatzResearch.WordTrace]
  refine ⟨58074748522496071398655055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38716499014997380932436703 58074748522496071398655055)
  ·
    refine ⟨87112122783744107097982583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58074748522496071398655055 87112122783744107097982583)
    ·
      refine ⟨130668184175616160646973875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87112122783744107097982583 130668184175616160646973875)
      ·
        refine ⟨196002276263424240970460813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130668184175616160646973875 196002276263424240970460813)
        ·
          refine ⟨73500853598784090363922805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196002276263424240970460813 73500853598784090363922805)
          ·
            refine ⟨6890705024886008471617763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73500853598784090363922805 6890705024886008471617763)
            ·
              refine ⟨10336057537329012707426645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890705024886008471617763 10336057537329012707426645)
              ·
                refine ⟨30281418566393591916289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10336057537329012707426645 30281418566393591916289)
                ·
                  rfl

theorem cell23_1592267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 10].length) (baseStart_1592267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592267 prefixEnd_1592267 := by exact prefixLift 1592267
  have htrace : WordTrace (prefixWord ++ tailWord_1592267) baseStart_1592267 baseEnd_1592267 := by
    simpa [prefixWord, tailWord_1592267, baseEnd_1592267] using wordTrace_append hprefix tailTrace_1592267
  have hstable : (prefixWord ++ tailWord_1592267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592267).length < 2 ^ (prefixWord ++ tailWord_1592267).sum := by decide
  have hdescent : baseEnd_1592267 < baseStart_1592267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592271 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 2, 4]
def baseStart_1592271 : Nat := 118140960795 + 1592271 * 2 ^ 59
def prefixEnd_1592271 : Nat := 4983230072969 + 3 ^ 40 * 1592271 * 2
def baseEnd_1592271 : Nat := 272533451738414988696595

theorem tailTrace_1592271 : CollatzResearch.WordTrace tailWord_1592271 prefixEnd_1592271 272533451738414988696595 := by
  unfold tailWord_1592271
  simp only [CollatzResearch.WordTrace]
  refine ⟨58074894414481580081800667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38716596276321053387867111 58074894414481580081800667)
  ·
    refine ⟨87112341621722370122701001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58074894414481580081800667 87112341621722370122701001)
    ·
      refine ⟨65334256216291777592025751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87112341621722370122701001 65334256216291777592025751)
      ·
        refine ⟨98001384324437666388038627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65334256216291777592025751 98001384324437666388038627)
        ·
          refine ⟨147002076486656499582057941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98001384324437666388038627 147002076486656499582057941)
          ·
            refine ⟨3445361167656011708954483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147002076486656499582057941 3445361167656011708954483)
            ·
              refine ⟨5168041751484017563431725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445361167656011708954483 5168041751484017563431725)
              ·
                refine ⟨1938015656806506586286897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168041751484017563431725 1938015656806506586286897)
                ·
                  refine ⟨1453511742604879939715173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938015656806506586286897 1453511742604879939715173)
                  ·
                    refine ⟨272533451738414988696595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453511742604879939715173 272533451738414988696595)
                    ·
                      rfl

theorem cell23_1592271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_1592271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592271 prefixEnd_1592271 := by exact prefixLift 1592271
  have htrace : WordTrace (prefixWord ++ tailWord_1592271) baseStart_1592271 baseEnd_1592271 := by
    simpa [prefixWord, tailWord_1592271, baseEnd_1592271] using wordTrace_append hprefix tailTrace_1592271
  have hstable : (prefixWord ++ tailWord_1592271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592271).length < 2 ^ (prefixWord ++ tailWord_1592271).sum := by decide
  have hdescent : baseEnd_1592271 < baseStart_1592271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592278 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1592278 : Nat := 118140960795 + 1592278 * 2 ^ 59
def prefixEnd_1592278 : Nat := 4983230072969 + 3 ^ 40 * 1592278 * 2
def baseEnd_1592278 : Nat := 817603949579826438702253

theorem tailTrace_1592278 : CollatzResearch.WordTrace tailWord_1592278 prefixEnd_1592278 817603949579826438702253 := by
  unfold tailWord_1592278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629696857841013767331593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38716766483637480184870325 3629696857841013767331593)
  ·
    refine ⟨2722272643380760325498695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3629696857841013767331593 2722272643380760325498695)
    ·
      refine ⟨4083408965071140488248043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722272643380760325498695 4083408965071140488248043)
      ·
        refine ⟨6125113447606710732372065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083408965071140488248043 6125113447606710732372065)
        ·
          refine ⟨4593835085705033049279049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6125113447606710732372065 4593835085705033049279049)
          ·
            refine ⟨3445376314278774786959287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593835085705033049279049 3445376314278774786959287)
            ·
              refine ⟨5168064471418162180438931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445376314278774786959287 5168064471418162180438931)
              ·
                refine ⟨7752096707127243270658397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168064471418162180438931 7752096707127243270658397)
                ·
                  refine ⟨2907036265172716226496899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7752096707127243270658397 2907036265172716226496899)
                  ·
                    refine ⟨4360554397759074339745349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907036265172716226496899 4360554397759074339745349)
                    ·
                      refine ⟨817603949579826438702253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4360554397759074339745349 817603949579826438702253)
                      ·
                        rfl

theorem cell23_1592278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1592278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592278 prefixEnd_1592278 := by exact prefixLift 1592278
  have htrace : WordTrace (prefixWord ++ tailWord_1592278) baseStart_1592278 baseEnd_1592278 := by
    simpa [prefixWord, tailWord_1592278, baseEnd_1592278] using wordTrace_append hprefix tailTrace_1592278
  have hstable : (prefixWord ++ tailWord_1592278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592278).length < 2 ^ (prefixWord ++ tailWord_1592278).sum := by decide
  have hdescent : baseEnd_1592278 < baseStart_1592278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592281 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_1592281 : Nat := 118140960795 + 1592281 * 2 ^ 59
def prefixEnd_1592281 : Nat := 4983230072969 + 3 ^ 40 * 1592281 * 2
def baseEnd_1592281 : Nat := 817605490021789926964739

theorem tailTrace_1592281 : CollatzResearch.WordTrace tailWord_1592281 prefixEnd_1592281 817605490021789926964739 := by
  unfold tailWord_1592281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58075259144445351789664697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38716839429630234526443131 58075259144445351789664697)
  ·
    refine ⟨43556444358334013842248523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58075259144445351789664697 43556444358334013842248523)
    ·
      refine ⟨65334666537501020763372785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43556444358334013842248523 65334666537501020763372785)
      ·
        refine ⟨49000999903125765572529589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65334666537501020763372785 49000999903125765572529589)
        ·
          refine ⟨4593843740918040522424649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49000999903125765572529589 4593843740918040522424649)
          ·
            refine ⟨3445382805688530391818487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593843740918040522424649 3445382805688530391818487)
            ·
              refine ⟨5168074208532795587727731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445382805688530391818487 5168074208532795587727731)
              ·
                refine ⟨7752111312799193381591597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168074208532795587727731 7752111312799193381591597)
                ·
                  refine ⟨2907041742299697518096849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7752111312799193381591597 2907041742299697518096849)
                  ·
                    refine ⟨2180281306724773138572637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2907041742299697518096849 2180281306724773138572637)
                    ·
                      refine ⟨817605490021789926964739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180281306724773138572637 817605490021789926964739)
                      ·
                        rfl

theorem cell23_1592281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_1592281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592281 prefixEnd_1592281 := by exact prefixLift 1592281
  have htrace : WordTrace (prefixWord ++ tailWord_1592281) baseStart_1592281 baseEnd_1592281 := by
    simpa [prefixWord, tailWord_1592281, baseEnd_1592281] using wordTrace_append hprefix tailTrace_1592281
  have hstable : (prefixWord ++ tailWord_1592281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592281).length < 2 ^ (prefixWord ++ tailWord_1592281).sum := by decide
  have hdescent : baseEnd_1592281 < baseStart_1592281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592297 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_1592297 : Nat := 118140960795 + 1592297 * 2 ^ 59
def prefixEnd_1592297 : Nat := 4983230072969 + 3 ^ 40 * 1592297 * 2
def baseEnd_1592297 : Nat := 272537901904087288121555

theorem tailTrace_1592297 : CollatzResearch.WordTrace tailWord_1592297 prefixEnd_1592297 272537901904087288121555 := by
  unfold tailWord_1592297
  simp only [CollatzResearch.WordTrace]
  refine ⟨58075842712387386522247145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38717228474924924348164763 58075842712387386522247145)
  ·
    refine ⟨43556882034290539891685359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58075842712387386522247145 43556882034290539891685359)
    ·
      refine ⟨65335323051435809837528039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43556882034290539891685359 65335323051435809837528039)
      ·
        refine ⟨98002984577153714756292059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65335323051435809837528039 98002984577153714756292059)
        ·
          refine ⟨147004476865730572134438089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98002984577153714756292059 147004476865730572134438089)
          ·
            refine ⟨110253357649297929100828567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147004476865730572134438089 110253357649297929100828567)
            ·
              refine ⟨165380036473946893651242851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110253357649297929100828567 165380036473946893651242851)
              ·
                refine ⟨248070054710920340476864277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165380036473946893651242851 248070054710920340476864277)
                ·
                  refine ⟨11628283814574390959853013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248070054710920340476864277 11628283814574390959853013)
                  ·
                    refine ⟨272537901904087288121555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11628283814574390959853013 272537901904087288121555)
                    ·
                      rfl

theorem cell23_1592297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_1592297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592297 prefixEnd_1592297 := by exact prefixLift 1592297
  have htrace : WordTrace (prefixWord ++ tailWord_1592297) baseStart_1592297 baseEnd_1592297 := by
    simpa [prefixWord, tailWord_1592297, baseEnd_1592297] using wordTrace_append hprefix tailTrace_1592297
  have hstable : (prefixWord ++ tailWord_1592297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592297).length < 2 ^ (prefixWord ++ tailWord_1592297).sum := by decide
  have hdescent : baseEnd_1592297 < baseStart_1592297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592306 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1592306 : Nat := 118140960795 + 1592306 * 2 ^ 59
def prefixEnd_1592306 : Nat := 4983230072969 + 3 ^ 40 * 1592306 * 2
def baseEnd_1592306 : Nat := 817618327038152329152125

theorem tailTrace_1592306 : CollatzResearch.WordTrace tailWord_1592306 prefixEnd_1592306 817618327038152329152125 := by
  unfold tailWord_1592306
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519042742338695264831193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38717447312903187372883181 14519042742338695264831193)
  ·
    refine ⟨10889282056754021448623395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14519042742338695264831193 10889282056754021448623395)
    ·
      refine ⟨16333923085131032172935093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889282056754021448623395 16333923085131032172935093)
      ·
        refine ⟨1531305289231034266212665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16333923085131032172935093 1531305289231034266212665)
        ·
          refine ⟨1148478966923275699659499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531305289231034266212665 1148478966923275699659499)
          ·
            refine ⟨1722718450384913549489249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148478966923275699659499 1722718450384913549489249)
            ·
              refine ⟨1292038837788685162116937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722718450384913549489249 1292038837788685162116937)
              ·
                refine ⟨969029128341513871587703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292038837788685162116937 969029128341513871587703)
                ·
                  refine ⟨1453543692512270807381555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969029128341513871587703 1453543692512270807381555)
                  ·
                    refine ⟨2180315538768406211072333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453543692512270807381555 2180315538768406211072333)
                    ·
                      refine ⟨817618327038152329152125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180315538768406211072333 817618327038152329152125)
                      ·
                        rfl

theorem cell23_1592306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1592306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592306 prefixEnd_1592306 := by exact prefixLift 1592306
  have htrace : WordTrace (prefixWord ++ tailWord_1592306) baseStart_1592306 baseEnd_1592306 := by
    simpa [prefixWord, tailWord_1592306, baseEnd_1592306] using wordTrace_append hprefix tailTrace_1592306
  have hstable : (prefixWord ++ tailWord_1592306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592306).length < 2 ^ (prefixWord ++ tailWord_1592306).sum := by decide
  have hdescent : baseEnd_1592306 < baseStart_1592306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592307 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1592307 : Nat := 118140960795 + 1592307 * 2 ^ 59
def prefixEnd_1592307 : Nat := 4983230072969 + 3 ^ 40 * 1592307 * 2
def baseEnd_1592307 : Nat := 817618840518806825239619

theorem tailTrace_1592307 : CollatzResearch.WordTrace tailWord_1592307 prefixEnd_1592307 817618840518806825239619 := by
  unfold tailWord_1592307
  simp only [CollatzResearch.WordTrace]
  refine ⟨58076207442351158230111175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38717471628234105486740783 58076207442351158230111175)
  ·
    refine ⟨87114311163526737345166763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58076207442351158230111175 87114311163526737345166763)
    ·
      refine ⟨130671466745290106017750145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87114311163526737345166763 130671466745290106017750145)
      ·
        refine ⟨98003600058967579513312609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130671466745290106017750145 98003600058967579513312609)
        ·
          refine ⟨73502700044225684634984457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98003600058967579513312609 73502700044225684634984457)
          ·
            refine ⟨55127025033169263476238343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73502700044225684634984457 55127025033169263476238343)
            ·
              refine ⟨82690537549753895214357515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55127025033169263476238343 82690537549753895214357515)
              ·
                refine ⟨124035806324630842821536273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82690537549753895214357515 124035806324630842821536273)
                ·
                  refine ⟨93026854743473132116152205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124035806324630842821536273 93026854743473132116152205)
                  ·
                    refine ⟨34885070528802424543557077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93026854743473132116152205 34885070528802424543557077)
                    ·
                      refine ⟨817618840518806825239619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34885070528802424543557077 817618840518806825239619)
                      ·
                        rfl

theorem cell23_1592307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1592307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592307 prefixEnd_1592307 := by exact prefixLift 1592307
  have htrace : WordTrace (prefixWord ++ tailWord_1592307) baseStart_1592307 baseEnd_1592307 := by
    simpa [prefixWord, tailWord_1592307, baseEnd_1592307] using wordTrace_append hprefix tailTrace_1592307
  have hstable : (prefixWord ++ tailWord_1592307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592307).length < 2 ^ (prefixWord ++ tailWord_1592307).sum := by decide
  have hdescent : baseEnd_1592307 < baseStart_1592307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592318 : List Nat := [4, 2, 2, 2, 2, 2, 1, 8]
def baseStart_1592318 : Nat := 118140960795 + 1592318 * 2 ^ 59
def prefixEnd_1592318 : Nat := 4983230072969 + 3 ^ 40 * 1592318 * 2
def baseEnd_1592318 : Nat := 30282388474296528970447

theorem tailTrace_1592318 : CollatzResearch.WordTrace tailWord_1592318 prefixEnd_1592318 30282388474296528970447 := by
  unfold tailWord_1592318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259576080663913388595201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38717739096874204739174405 7259576080663913388595201)
  ·
    refine ⟨5444682060497935041446401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7259576080663913388595201 5444682060497935041446401)
    ·
      refine ⟨4083511545373451281084801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5444682060497935041446401 4083511545373451281084801)
      ·
        refine ⟨3062633659030088460813601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4083511545373451281084801 3062633659030088460813601)
        ·
          refine ⟨2296975244272566345610201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062633659030088460813601 2296975244272566345610201)
          ·
            refine ⟨1722731433204424759207651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296975244272566345610201 1722731433204424759207651)
            ·
              refine ⟨2584097149806637138811477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722731433204424759207651 2584097149806637138811477)
              ·
                refine ⟨30282388474296528970447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2584097149806637138811477 30282388474296528970447)
                ·
                  rfl

theorem cell23_1592318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_1592318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592318 prefixEnd_1592318 := by exact prefixLift 1592318
  have htrace : WordTrace (prefixWord ++ tailWord_1592318) baseStart_1592318 baseEnd_1592318 := by
    simpa [prefixWord, tailWord_1592318, baseEnd_1592318] using wordTrace_append hprefix tailTrace_1592318
  have hstable : (prefixWord ++ tailWord_1592318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592318).length < 2 ^ (prefixWord ++ tailWord_1592318).sum := by decide
  have hdescent : baseEnd_1592318 < baseStart_1592318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592328 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1592328 : Nat := 118140960795 + 1592328 * 2 ^ 59
def prefixEnd_1592328 : Nat := 4983230072969 + 3 ^ 40 * 1592328 * 2
def baseEnd_1592328 : Nat := 817629623612551243077023

theorem tailTrace_1592328 : CollatzResearch.WordTrace tailWord_1592328 prefixEnd_1592328 817629623612551243077023 := by
  unfold tailWord_1592328
  simp only [CollatzResearch.WordTrace]
  refine ⟨29038486687637539408312819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38717982250183385877750425 29038486687637539408312819)
  ·
    refine ⟨43557730031456309112469229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29038486687637539408312819 43557730031456309112469229)
    ·
      refine ⟨16334148761796115917175961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43557730031456309112469229 16334148761796115917175961)
      ·
        refine ⟨12250611571347086937881971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16334148761796115917175961 12250611571347086937881971)
        ·
          refine ⟨18375917357020630406822957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12250611571347086937881971 18375917357020630406822957)
          ·
            refine ⟨6890969008882736402558609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18375917357020630406822957 6890969008882736402558609)
            ·
              refine ⟨5168226756662052301918957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890969008882736402558609 5168226756662052301918957)
              ·
                refine ⟨1938085033748269613219609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168226756662052301918957 1938085033748269613219609)
                ·
                  refine ⟨1453563775311202209914707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938085033748269613219609 1453563775311202209914707)
                  ·
                    refine ⟨2180345662966803314872061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453563775311202209914707 2180345662966803314872061)
                    ·
                      refine ⟨817629623612551243077023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180345662966803314872061 817629623612551243077023)
                      ·
                        rfl

theorem cell23_1592328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1592328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592328 prefixEnd_1592328 := by exact prefixLift 1592328
  have htrace : WordTrace (prefixWord ++ tailWord_1592328) baseStart_1592328 baseEnd_1592328 := by
    simpa [prefixWord, tailWord_1592328, baseEnd_1592328] using wordTrace_append hprefix tailTrace_1592328
  have hstable : (prefixWord ++ tailWord_1592328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592328).length < 2 ^ (prefixWord ++ tailWord_1592328).sum := by decide
  have hdescent : baseEnd_1592328 < baseStart_1592328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592355 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 1, 3, 2]
def baseStart_1592355 : Nat := 118140960795 + 1592355 * 2 ^ 59
def prefixEnd_1592355 : Nat := 4983230072969 + 3 ^ 40 * 1592355 * 2
def baseEnd_1592355 : Nat := 817643487590222637439399

theorem tailTrace_1592355 : CollatzResearch.WordTrace tailWord_1592355 prefixEnd_1592355 817643487590222637439399 := by
  unfold tailWord_1592355
  simp only [CollatzResearch.WordTrace]
  refine ⟨58077958146177262427858519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38718638764118174951905679 58077958146177262427858519)
  ·
    refine ⟨87116937219265893641787779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58077958146177262427858519 87116937219265893641787779)
    ·
      refine ⟨130675405828898840462681669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87116937219265893641787779 130675405828898840462681669)
      ·
        refine ⟨24501638592918532586752813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130675405828898840462681669 24501638592918532586752813)
        ·
          refine ⟨9188114472344449720032305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24501638592918532586752813 9188114472344449720032305)
          ·
            refine ⟨6891085854258337290024229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9188114472344449720032305 6891085854258337290024229)
            ·
              refine ⟨1292078597673438241879543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6891085854258337290024229 1292078597673438241879543)
              ·
                refine ⟨1938117896510157362819315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292078597673438241879543 1938117896510157362819315)
                ·
                  refine ⟨2907176844765236044228973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938117896510157362819315 2907176844765236044228973)
                  ·
                    refine ⟨1090191316786963516585865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907176844765236044228973 1090191316786963516585865)
                    ·
                      refine ⟨817643487590222637439399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090191316786963516585865 817643487590222637439399)
                      ·
                        rfl

theorem cell23_1592355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_1592355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592355 prefixEnd_1592355 := by exact prefixLift 1592355
  have htrace : WordTrace (prefixWord ++ tailWord_1592355) baseStart_1592355 baseEnd_1592355 := by
    simpa [prefixWord, tailWord_1592355, baseEnd_1592355] using wordTrace_append hprefix tailTrace_1592355
  have hstable : (prefixWord ++ tailWord_1592355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592355).length < 2 ^ (prefixWord ++ tailWord_1592355).sum := by decide
  have hdescent : baseEnd_1592355 < baseStart_1592355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592362 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1592362 : Nat := 118140960795 + 1592362 * 2 ^ 59
def prefixEnd_1592362 : Nat := 4983230072969 + 3 ^ 40 * 1592362 * 2
def baseEnd_1592362 : Nat := 817647081954804110051867

theorem tailTrace_1592362 : CollatzResearch.WordTrace tailWord_1592362 prefixEnd_1592362 817647081954804110051867 := by
  unfold tailWord_1592362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519553364287975655840835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38718808971434601748908893 14519553364287975655840835)
  ·
    refine ⟨21779330046431963483761253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14519553364287975655840835 21779330046431963483761253)
    ·
      refine ⟨4083624383705993153205235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21779330046431963483761253 4083624383705993153205235)
      ·
        refine ⟨6125436575558989729807853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083624383705993153205235 6125436575558989729807853)
        ·
          refine ⟨2297038715834621148677945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6125436575558989729807853 2297038715834621148677945)
          ·
            refine ⟨1722779036875965861508459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297038715834621148677945 1722779036875965861508459)
            ·
              refine ⟨2584168555313948792262689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722779036875965861508459 2584168555313948792262689)
              ·
                refine ⟨1938126416485461594197017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584168555313948792262689 1938126416485461594197017)
                ·
                  refine ⟨1453594812364096195647763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938126416485461594197017 1453594812364096195647763)
                  ·
                    refine ⟨2180392218546144293471645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1453594812364096195647763 2180392218546144293471645)
                    ·
                      refine ⟨817647081954804110051867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180392218546144293471645 817647081954804110051867)
                      ·
                        rfl

theorem cell23_1592362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1592362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592362 prefixEnd_1592362 := by exact prefixLift 1592362
  have htrace : WordTrace (prefixWord ++ tailWord_1592362) baseStart_1592362 baseEnd_1592362 := by
    simpa [prefixWord, tailWord_1592362, baseEnd_1592362] using wordTrace_append hprefix tailTrace_1592362
  have hstable : (prefixWord ++ tailWord_1592362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592362).length < 2 ^ (prefixWord ++ tailWord_1592362).sum := by decide
  have hdescent : baseEnd_1592362 < baseStart_1592362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592364 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1592364 : Nat := 118140960795 + 1592364 * 2 ^ 59
def prefixEnd_1592364 : Nat := 4983230072969 + 3 ^ 40 * 1592364 * 2
def baseEnd_1592364 : Nat := 817648108916113102226857

theorem tailTrace_1592364 : CollatzResearch.WordTrace tailWord_1592364 prefixEnd_1592364 817648108916113102226857 := by
  unfold tailWord_1592364
  simp only [CollatzResearch.WordTrace]
  refine ⟨29039143201572328482468073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38718857602096437976624097 29039143201572328482468073)
  ·
    refine ⟨21779357401179246361851055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29039143201572328482468073 21779357401179246361851055)
    ·
      refine ⟨32669036101768869542776583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21779357401179246361851055 32669036101768869542776583)
      ·
        refine ⟨49003554152653304314164875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32669036101768869542776583 49003554152653304314164875)
        ·
          refine ⟨73505331228979956471247313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49003554152653304314164875 73505331228979956471247313)
          ·
            refine ⟨55128998421734967353435485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73505331228979956471247313 55128998421734967353435485)
            ·
              refine ⟨20673374408150612757538307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55128998421734967353435485 20673374408150612757538307)
              ·
                refine ⟨31010061612225919136307461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20673374408150612757538307 31010061612225919136307461)
                ·
                  refine ⟨5814386552292359838057649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31010061612225919136307461 5814386552292359838057649)
                  ·
                    refine ⟨4360789914219269878543237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5814386552292359838057649 4360789914219269878543237)
                    ·
                      refine ⟨817648108916113102226857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4360789914219269878543237 817648108916113102226857)
                      ·
                        rfl

theorem cell23_1592364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1592364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592364 prefixEnd_1592364 := by exact prefixLift 1592364
  have htrace : WordTrace (prefixWord ++ tailWord_1592364) baseStart_1592364 baseEnd_1592364 := by
    simpa [prefixWord, tailWord_1592364, baseEnd_1592364] using wordTrace_append hprefix tailTrace_1592364
  have hstable : (prefixWord ++ tailWord_1592364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592364).length < 2 ^ (prefixWord ++ tailWord_1592364).sum := by decide
  have hdescent : baseEnd_1592364 < baseStart_1592364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592368 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2]
def baseStart_1592368 : Nat := 118140960795 + 1592368 * 2 ^ 59
def prefixEnd_1592368 : Nat := 4983230072969 + 3 ^ 40 * 1592368 * 2
def baseEnd_1592368 : Nat := 817650162838731086576839

theorem tailTrace_1592368 : CollatzResearch.WordTrace tailWord_1592368 prefixEnd_1592368 817650162838731086576839 := by
  unfold tailWord_1592368
  simp only [CollatzResearch.WordTrace]
  refine ⟨29039216147565082824040879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38718954863420110432054505 29039216147565082824040879)
  ·
    refine ⟨43558824221347624236061319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29039216147565082824040879 43558824221347624236061319)
    ·
      refine ⟨65338236332021436354091979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43558824221347624236061319 65338236332021436354091979)
      ·
        refine ⟨98007354498032154531137969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65338236332021436354091979 98007354498032154531137969)
        ·
          refine ⟨73505515873524115898353477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98007354498032154531137969 73505515873524115898353477)
          ·
            refine ⟨13782284226285771730941277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73505515873524115898353477 13782284226285771730941277)
            ·
              refine ⟨5168356584857164399102979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13782284226285771730941277 5168356584857164399102979)
              ·
                refine ⟨7752534877285746598654469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168356584857164399102979 7752534877285746598654469)
                ·
                  refine ⟨1453600289491077487247713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7752534877285746598654469 1453600289491077487247713)
                  ·
                    refine ⟨1090200217118308115435785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453600289491077487247713 1090200217118308115435785)
                    ·
                      refine ⟨817650162838731086576839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090200217118308115435785 817650162838731086576839)
                      ·
                        rfl

theorem cell23_1592368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 2, 2].length) (baseStart_1592368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592368 prefixEnd_1592368 := by exact prefixLift 1592368
  have htrace : WordTrace (prefixWord ++ tailWord_1592368) baseStart_1592368 baseEnd_1592368 := by
    simpa [prefixWord, tailWord_1592368, baseEnd_1592368] using wordTrace_append hprefix tailTrace_1592368
  have hstable : (prefixWord ++ tailWord_1592368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592368).length < 2 ^ (prefixWord ++ tailWord_1592368).sum := by decide
  have hdescent : baseEnd_1592368 < baseStart_1592368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592381 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1592381 : Nat := 118140960795 + 1592381 * 2 ^ 59
def prefixEnd_1592381 : Nat := 4983230072969 + 3 ^ 40 * 1592381 * 2
def baseEnd_1592381 : Nat := 817656838087239535714279

theorem tailTrace_1592381 : CollatzResearch.WordTrace tailWord_1592381 prefixEnd_1592381 817656838087239535714279 := by
  unfold tailWord_1592381
  simp only [CollatzResearch.WordTrace]
  refine ⟨58078906444083068868304997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38719270962722045912203331 58078906444083068868304997)
  ·
    refine ⟨10889794958265575412807187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58078906444083068868304997 10889794958265575412807187)
    ·
      refine ⟨16334692437398363119210781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889794958265575412807187 16334692437398363119210781)
      ·
        refine ⟨6125509664024386169704043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16334692437398363119210781 6125509664024386169704043)
        ·
          refine ⟨9188264496036579254556065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125509664024386169704043 9188264496036579254556065)
          ·
            refine ⟨6891198372027434440917049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9188264496036579254556065 6891198372027434440917049)
            ·
              refine ⟨5168398779020575830687787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6891198372027434440917049 5168398779020575830687787)
              ·
                refine ⟨7752598168530863746031681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168398779020575830687787 7752598168530863746031681)
                ·
                  refine ⟨5814448626398147809523761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7752598168530863746031681 5814448626398147809523761)
                  ·
                    refine ⟨4360836469798610857142821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5814448626398147809523761 4360836469798610857142821)
                    ·
                      refine ⟨817656838087239535714279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4360836469798610857142821 817656838087239535714279)
                      ·
                        rfl

theorem cell23_1592381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1592381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592381 prefixEnd_1592381 := by exact prefixLift 1592381
  have htrace : WordTrace (prefixWord ++ tailWord_1592381) baseStart_1592381 baseEnd_1592381 := by
    simpa [prefixWord, tailWord_1592381, baseEnd_1592381] using wordTrace_append hprefix tailTrace_1592381
  have hstable : (prefixWord ++ tailWord_1592381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592381).length < 2 ^ (prefixWord ++ tailWord_1592381).sum := by decide
  have hdescent : baseEnd_1592381 < baseStart_1592381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592421 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_1592421 : Nat := 118140960795 + 1592421 * 2 ^ 59
def prefixEnd_1592421 : Nat := 4983230072969 + 3 ^ 40 * 1592421 * 2
def baseEnd_1592421 : Nat := 272559125771139793071365

theorem tailTrace_1592421 : CollatzResearch.WordTrace tailWord_1592421 prefixEnd_1592421 272559125771139793071365 := by
  unfold tailWord_1592421
  simp only [CollatzResearch.WordTrace]
  refine ⟨58080365363938155699761117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38720243575958770466507411 58080365363938155699761117)
  ·
    refine ⟨21780137011476808387410419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58080365363938155699761117 21780137011476808387410419)
    ·
      refine ⟨32670205517215212581115629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21780137011476808387410419 32670205517215212581115629)
      ·
        refine ⟨12251327068955704717918361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32670205517215212581115629 12251327068955704717918361)
        ·
          refine ⟨9188495301716778538438771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12251327068955704717918361 9188495301716778538438771)
          ·
            refine ⟨13782742952575167807658157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188495301716778538438771 13782742952575167807658157)
            ·
              refine ⟨5168528607215687927871809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13782742952575167807658157 5168528607215687927871809)
              ·
                refine ⟨3876396455411765945903857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5168528607215687927871809 3876396455411765945903857)
                ·
                  refine ⟨2907297341558824459427893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876396455411765945903857 2907297341558824459427893)
                  ·
                    refine ⟨272559125771139793071365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2907297341558824459427893 272559125771139793071365)
                    ·
                      rfl

theorem cell23_1592421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_1592421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592421 prefixEnd_1592421 := by exact prefixLift 1592421
  have htrace : WordTrace (prefixWord ++ tailWord_1592421) baseStart_1592421 baseEnd_1592421 := by
    simpa [prefixWord, tailWord_1592421, baseEnd_1592421] using wordTrace_append hprefix tailTrace_1592421
  have hstable : (prefixWord ++ tailWord_1592421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592421).length < 2 ^ (prefixWord ++ tailWord_1592421).sum := by decide
  have hdescent : baseEnd_1592421 < baseStart_1592421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592451 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 5, 4]
def baseStart_1592451 : Nat := 118140960795 + 1592451 * 2 ^ 59
def prefixEnd_1592451 : Nat := 4983230072969 + 3 ^ 40 * 1592451 * 2
def baseEnd_1592451 : Nat := 272564260577684753946319

theorem tailTrace_1592451 : CollatzResearch.WordTrace tailWord_1592451 prefixEnd_1592451 272564260577684753946319 := by
  unfold tailWord_1592451
  simp only [CollatzResearch.WordTrace]
  refine ⟨58081459553829470823353207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38720973035886313882235471 58081459553829470823353207)
  ·
    refine ⟨87122189330744206235029811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58081459553829470823353207 87122189330744206235029811)
    ·
      refine ⟨130683283996116309352544717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87122189330744206235029811 130683283996116309352544717)
      ·
        refine ⟨49006231498543616007204269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130683283996116309352544717 49006231498543616007204269)
        ·
          refine ⟨18377336811953856002701601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49006231498543616007204269 18377336811953856002701601)
          ·
            refine ⟨13783002608965392002026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18377336811953856002701601 13783002608965392002026201)
            ·
              refine ⟨10337251956724044001519651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13783002608965392002026201 10337251956724044001519651)
              ·
                refine ⟨15505877935086066002279477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10337251956724044001519651 15505877935086066002279477)
                ·
                  refine ⟨1453676056414318687713701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15505877935086066002279477 1453676056414318687713701)
                  ·
                    refine ⟨272564260577684753946319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453676056414318687713701 272564260577684753946319)
                    ·
                      rfl

theorem cell23_1592451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 4].length) (baseStart_1592451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592451 prefixEnd_1592451 := by exact prefixLift 1592451
  have htrace : WordTrace (prefixWord ++ tailWord_1592451) baseStart_1592451 baseEnd_1592451 := by
    simpa [prefixWord, tailWord_1592451, baseEnd_1592451] using wordTrace_append hprefix tailTrace_1592451
  have hstable : (prefixWord ++ tailWord_1592451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592451).length < 2 ^ (prefixWord ++ tailWord_1592451).sum := by decide
  have hdescent : baseEnd_1592451 < baseStart_1592451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592458 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1592458 : Nat := 118140960795 + 1592458 * 2 ^ 59
def prefixEnd_1592458 : Nat := 4983230072969 + 3 ^ 40 * 1592458 * 2
def baseEnd_1592458 : Nat := 817696376097635734451425

theorem tailTrace_1592458 : CollatzResearch.WordTrace tailWord_1592458 prefixEnd_1592458 817696376097635734451425 := by
  unfold tailWord_1592458
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520428716201027754714507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38721143243202740679238685 14520428716201027754714507)
  ·
    refine ⟨21780643074301541632071761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14520428716201027754714507 21780643074301541632071761)
    ·
      refine ⟨16335482305726156224053821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21780643074301541632071761 16335482305726156224053821)
      ·
        refine ⟨6125805864647308584020183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16335482305726156224053821 6125805864647308584020183)
        ·
          refine ⟨9188708796970962876030275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125805864647308584020183 9188708796970962876030275)
          ·
            refine ⟨13783063195456444314045413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188708796970962876030275 13783063195456444314045413)
            ·
              refine ⟨2584324349148083308883515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13783063195456444314045413 2584324349148083308883515)
              ·
                refine ⟨3876486523722124963325273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584324349148083308883515 3876486523722124963325273)
                ·
                  refine ⟨2907364892791593722493955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876486523722124963325273 2907364892791593722493955)
                  ·
                    refine ⟨4361047339187390583740933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907364892791593722493955 4361047339187390583740933)
                    ·
                      refine ⟨817696376097635734451425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4361047339187390583740933 817696376097635734451425)
                      ·
                        rfl

theorem cell23_1592458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1592458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592458 prefixEnd_1592458 := by exact prefixLift 1592458
  have htrace : WordTrace (prefixWord ++ tailWord_1592458) baseStart_1592458 baseEnd_1592458 := by
    simpa [prefixWord, tailWord_1592458, baseEnd_1592458] using wordTrace_append hprefix tailTrace_1592458
  have hstable : (prefixWord ++ tailWord_1592458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592458).length < 2 ^ (prefixWord ++ tailWord_1592458).sum := by decide
  have hdescent : baseEnd_1592458 < baseStart_1592458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592464 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 8]
def baseStart_1592464 : Nat := 118140960795 + 1592464 * 2 ^ 59
def prefixEnd_1592464 : Nat := 4983230072969 + 3 ^ 40 * 1592464 * 2
def baseEnd_1592464 : Nat := 90855495220173634552933

theorem tailTrace_1592464 : CollatzResearch.WordTrace tailWord_1592464 prefixEnd_1592464 90855495220173634552933 := by
  unfold tailWord_1592464
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040966851391187021788223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38721289135188249362384297 29040966851391187021788223)
  ·
    refine ⟨43561450277086780532682335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29040966851391187021788223 43561450277086780532682335)
    ·
      refine ⟨65342175415630170799023503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43561450277086780532682335 65342175415630170799023503)
      ·
        refine ⟨98013263123445256198535255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65342175415630170799023503 98013263123445256198535255)
        ·
          refine ⟨147019894685167884297802883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98013263123445256198535255 147019894685167884297802883)
          ·
            refine ⟨220529842027751826446704325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147019894685167884297802883 220529842027751826446704325)
            ·
              refine ⟨41349345380203467458757061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220529842027751826446704325 41349345380203467458757061)
              ·
                refine ⟨7753002258788150148516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41349345380203467458757061 7753002258788150148516949)
                ·
                  refine ⟨90855495220173634552933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7753002258788150148516949 90855495220173634552933)
                  ·
                    rfl

theorem cell23_1592464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_1592464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592464 prefixEnd_1592464 := by exact prefixLift 1592464
  have htrace : WordTrace (prefixWord ++ tailWord_1592464) baseStart_1592464 baseEnd_1592464 := by
    simpa [prefixWord, tailWord_1592464, baseEnd_1592464] using wordTrace_append hprefix tailTrace_1592464
  have hstable : (prefixWord ++ tailWord_1592464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592464).length < 2 ^ (prefixWord ++ tailWord_1592464).sum := by decide
  have hdescent : baseEnd_1592464 < baseStart_1592464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592485 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_1592485 : Nat := 118140960795 + 1592485 * 2 ^ 59
def prefixEnd_1592485 : Nat := 4983230072969 + 3 ^ 40 * 1592485 * 2
def baseEnd_1592485 : Nat := 272570080025102376271267

theorem tailTrace_1592485 : CollatzResearch.WordTrace tailWord_1592485 prefixEnd_1592485 272570080025102376271267 := by
  unfold tailWord_1592485
  simp only [CollatzResearch.WordTrace]
  refine ⟨58082699635706294630090909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38721799757137529753393939 58082699635706294630090909)
  ·
    refine ⟨21781012363389860486284091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58082699635706294630090909 21781012363389860486284091)
    ·
      refine ⟨32671518545084790729426137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21781012363389860486284091 32671518545084790729426137)
      ·
        refine ⟨24503638908813593047069603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32671518545084790729426137 24503638908813593047069603)
        ·
          refine ⟨36755458363220389570604405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24503638908813593047069603 36755458363220389570604405)
          ·
            refine ⟨3445824221551911522244163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36755458363220389570604405 3445824221551911522244163)
            ·
              refine ⟨5168736332327867283366245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445824221551911522244163 5168736332327867283366245)
              ·
                refine ⟨969138062311475115631171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5168736332327867283366245 969138062311475115631171)
                ·
                  refine ⟨1453707093467212673446757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969138062311475115631171 1453707093467212673446757)
                  ·
                    refine ⟨272570080025102376271267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453707093467212673446757 272570080025102376271267)
                    ·
                      rfl

theorem cell23_1592485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_1592485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592485 prefixEnd_1592485 := by exact prefixLift 1592485
  have htrace : WordTrace (prefixWord ++ tailWord_1592485) baseStart_1592485 baseEnd_1592485 := by
    simpa [prefixWord, tailWord_1592485, baseEnd_1592485] using wordTrace_append hprefix tailTrace_1592485
  have hstable : (prefixWord ++ tailWord_1592485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592485).length < 2 ^ (prefixWord ++ tailWord_1592485).sum := by decide
  have hdescent : baseEnd_1592485 < baseStart_1592485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592511 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 3, 5]
def baseStart_1592511 : Nat := 118140960795 + 1592511 * 2 ^ 59
def prefixEnd_1592511 : Nat := 4983230072969 + 3 ^ 40 * 1592511 * 2
def baseEnd_1592511 : Nat := 272574530190774675696227

theorem tailTrace_1592511 : CollatzResearch.WordTrace tailWord_1592511 prefixEnd_1592511 272574530190774675696227 := by
  unfold tailWord_1592511
  simp only [CollatzResearch.WordTrace]
  refine ⟨58083647933612101070537387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38722431955741400713691591 58083647933612101070537387)
  ·
    refine ⟨87125471900418151605806081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58083647933612101070537387 87125471900418151605806081)
    ·
      refine ⟨65344103925313613704354561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87125471900418151605806081 65344103925313613704354561)
      ·
        refine ⟨49008077943985210278265921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65344103925313613704354561 49008077943985210278265921)
        ·
          refine ⟨36756058457988907708699441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49008077943985210278265921 36756058457988907708699441)
          ·
            refine ⟨27567043843491680781524581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36756058457988907708699441 27567043843491680781524581)
            ·
              refine ⟨5168820720654690146535859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27567043843491680781524581 5168820720654690146535859)
              ·
                refine ⟨7753231080982035219803789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168820720654690146535859 7753231080982035219803789)
                ·
                  refine ⟨2907461655368263207426421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7753231080982035219803789 2907461655368263207426421)
                  ·
                    refine ⟨272574530190774675696227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2907461655368263207426421 272574530190774675696227)
                    ·
                      rfl

theorem cell23_1592511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_1592511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592511 prefixEnd_1592511 := by exact prefixLift 1592511
  have htrace : WordTrace (prefixWord ++ tailWord_1592511) baseStart_1592511 baseEnd_1592511 := by
    simpa [prefixWord, tailWord_1592511, baseEnd_1592511] using wordTrace_append hprefix tailTrace_1592511
  have hstable : (prefixWord ++ tailWord_1592511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592511).length < 2 ^ (prefixWord ++ tailWord_1592511).sum := by decide
  have hdescent : baseEnd_1592511 < baseStart_1592511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592512 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3]
def baseStart_1592512 : Nat := 118140960795 + 1592512 * 2 ^ 59
def prefixEnd_1592512 : Nat := 4983230072969 + 3 ^ 40 * 1592512 * 2
def baseEnd_1592512 : Nat := 817724104052978523176177

theorem tailTrace_1592512 : CollatzResearch.WordTrace tailWord_1592512 prefixEnd_1592512 817724104052978523176177 := by
  unfold tailWord_1592512
  simp only [CollatzResearch.WordTrace]
  refine ⟨29041842203304239120661895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38722456271072318827549193 29041842203304239120661895)
  ·
    refine ⟨43562763304956358680992843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29041842203304239120661895 43562763304956358680992843)
    ·
      refine ⟨65344144957434538021489265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43562763304956358680992843 65344144957434538021489265)
      ·
        refine ⟨49008108718075903516116949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65344144957434538021489265 49008108718075903516116949)
        ·
          refine ⟨1148627548079903988658991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49008108718075903516116949 1148627548079903988658991)
          ·
            refine ⟨1722941322119855982988487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148627548079903988658991 1722941322119855982988487)
            ·
              refine ⟨2584411983179783974482731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722941322119855982988487 2584411983179783974482731)
              ·
                refine ⟨3876617974769675961724097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584411983179783974482731 3876617974769675961724097)
                ·
                  refine ⟨2907463481077256971293073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876617974769675961724097 2907463481077256971293073)
                  ·
                    refine ⟨2180597610807942728469805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2907463481077256971293073 2180597610807942728469805)
                    ·
                      refine ⟨817724104052978523176177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180597610807942728469805 817724104052978523176177)
                      ·
                        rfl

theorem cell23_1592512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_1592512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592512 prefixEnd_1592512 := by exact prefixLift 1592512
  have htrace : WordTrace (prefixWord ++ tailWord_1592512) baseStart_1592512 baseEnd_1592512 := by
    simpa [prefixWord, tailWord_1592512, baseEnd_1592512] using wordTrace_append hprefix tailTrace_1592512
  have hstable : (prefixWord ++ tailWord_1592512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592512).length < 2 ^ (prefixWord ++ tailWord_1592512).sum := by decide
  have hdescent : baseEnd_1592512 < baseStart_1592512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592532 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 6]
def baseStart_1592532 : Nat := 118140960795 + 1592532 * 2 ^ 59
def prefixEnd_1592532 : Nat := 4983230072969 + 3 ^ 40 * 1592532 * 2
def baseEnd_1592532 : Nat := 90859374851785382769565

theorem tailTrace_1592532 : CollatzResearch.WordTrace tailWord_1592532 prefixEnd_1592532 90859374851785382769565 := by
  unfold tailWord_1592532
  simp only [CollatzResearch.WordTrace]
  refine ⟨29042206933268010828525925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38722942577690681104701233 29042206933268010828525925)
  ·
    refine ⟨5445413799987752030348611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29042206933268010828525925 5445413799987752030348611)
    ·
      refine ⟨8168120699981628045522917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445413799987752030348611 8168120699981628045522917)
      ·
        refine ⟨1531522631246555258535547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8168120699981628045522917 1531522631246555258535547)
        ·
          refine ⟨2297283946869832887803321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531522631246555258535547 2297283946869832887803321)
          ·
            refine ⟨1722962960152374665852491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297283946869832887803321 1722962960152374665852491)
            ·
              refine ⟨2584444440228561998778737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722962960152374665852491 2584444440228561998778737)
              ·
                refine ⟨1938333330171421499084053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584444440228561998778737 1938333330171421499084053)
                ·
                  refine ⟨90859374851785382769565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1938333330171421499084053 90859374851785382769565)
                  ·
                    rfl

theorem cell23_1592532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_1592532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592532 prefixEnd_1592532 := by exact prefixLift 1592532
  have htrace : WordTrace (prefixWord ++ tailWord_1592532) baseStart_1592532 baseEnd_1592532 := by
    simpa [prefixWord, tailWord_1592532, baseEnd_1592532] using wordTrace_append hprefix tailTrace_1592532
  have hstable : (prefixWord ++ tailWord_1592532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592532).length < 2 ^ (prefixWord ++ tailWord_1592532).sum := by decide
  have hdescent : baseEnd_1592532 < baseStart_1592532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592558 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1592558 : Nat := 118140960795 + 1592558 * 2 ^ 59
def prefixEnd_1592558 : Nat := 4983230072969 + 3 ^ 40 * 1592558 * 2
def baseEnd_1592558 : Nat := 272582574721028447733655

theorem tailTrace_1592558 : CollatzResearch.WordTrace tailWord_1592558 prefixEnd_1592558 272582574721028447733655 := by
  unfold tailWord_1592558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7260670270555228512187291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38723574776294552064998885 7260670270555228512187291)
  ·
    refine ⟨10891005405832842768280937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7260670270555228512187291 10891005405832842768280937)
    ·
      refine ⟨8168254054374632076210703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10891005405832842768280937 8168254054374632076210703)
      ·
        refine ⟨12252381081561948114316055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8168254054374632076210703 12252381081561948114316055)
        ·
          refine ⟨18378571622342922171474083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12252381081561948114316055 18378571622342922171474083)
          ·
            refine ⟨27567857433514383257211125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18378571622342922171474083 27567857433514383257211125)
            ·
              refine ⟨2584486634391973430363543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27567857433514383257211125 2584486634391973430363543)
              ·
                refine ⟨3876729951587960145545315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584486634391973430363543 3876729951587960145545315)
                ·
                  refine ⟨5815094927381940218317973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876729951587960145545315 5815094927381940218317973)
                  ·
                    refine ⟨272582574721028447733655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5815094927381940218317973 272582574721028447733655)
                    ·
                      rfl

theorem cell23_1592558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1592558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592558 prefixEnd_1592558 := by exact prefixLift 1592558
  have htrace : WordTrace (prefixWord ++ tailWord_1592558) baseStart_1592558 baseEnd_1592558 := by
    simpa [prefixWord, tailWord_1592558, baseEnd_1592558] using wordTrace_append hprefix tailTrace_1592558
  have hstable : (prefixWord ++ tailWord_1592558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592558).length < 2 ^ (prefixWord ++ tailWord_1592558).sum := by decide
  have hdescent : baseEnd_1592558 < baseStart_1592558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592631 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 6, 6]
def baseStart_1592631 : Nat := 118140960795 + 1592631 * 2 ^ 59
def prefixEnd_1592631 : Nat := 4983230072969 + 3 ^ 40 * 1592631 * 2
def baseEnd_1592631 : Nat := 272595069416954519196043

theorem tailTrace_1592631 : CollatzResearch.WordTrace tailWord_1592631 prefixEnd_1592631 272595069416954519196043 := by
  unfold tailWord_1592631
  simp only [CollatzResearch.WordTrace]
  refine ⟨58088024693177361564905747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38725349795451574376603831 58088024693177361564905747)
  ·
    refine ⟨87132037039766042347358621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58088024693177361564905747 87132037039766042347358621)
    ·
      refine ⟨32674513889912265880259483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87132037039766042347358621 32674513889912265880259483)
      ·
        refine ⟨49011770834868398820389225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32674513889912265880259483 49011770834868398820389225)
        ·
          refine ⟨36758828126151299115291919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49011770834868398820389225 36758828126151299115291919)
          ·
            refine ⟨55138242189226948672937879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36758828126151299115291919 55138242189226948672937879)
            ·
              refine ⟨82707363283840423009406819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55138242189226948672937879 82707363283840423009406819)
              ·
                refine ⟨124061044925760634514110229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82707363283840423009406819 124061044925760634514110229)
                ·
                  refine ⟨5815361480895029742848917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124061044925760634514110229 5815361480895029742848917)
                  ·
                    refine ⟨272595069416954519196043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5815361480895029742848917 272595069416954519196043)
                    ·
                      rfl

theorem cell23_1592631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_1592631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592631 prefixEnd_1592631 := by exact prefixLift 1592631
  have htrace : WordTrace (prefixWord ++ tailWord_1592631) baseStart_1592631 baseEnd_1592631 := by
    simpa [prefixWord, tailWord_1592631, baseEnd_1592631] using wordTrace_append hprefix tailTrace_1592631
  have hstable : (prefixWord ++ tailWord_1592631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592631).length < 2 ^ (prefixWord ++ tailWord_1592631).sum := by decide
  have hdescent : baseEnd_1592631 < baseStart_1592631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592655 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 8, 2, 2]
def baseStart_1592655 : Nat := 118140960795 + 1592655 * 2 ^ 59
def prefixEnd_1592655 : Nat := 4983230072969 + 3 ^ 40 * 1592655 * 2
def baseEnd_1592655 : Nat := 817797531786571463688019

theorem tailTrace_1592655 : CollatzResearch.WordTrace tailWord_1592655 prefixEnd_1592655 817797531786571463688019 := by
  unfold tailWord_1592655
  simp only [CollatzResearch.WordTrace]
  refine ⟨58088900045090413663779419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38725933363393609109186279 58088900045090413663779419)
  ·
    refine ⟨87133350067635620495669129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58088900045090413663779419 87133350067635620495669129)
    ·
      refine ⟨65350012550726715371751847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87133350067635620495669129 65350012550726715371751847)
      ·
        refine ⟨98025018826090073057627771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65350012550726715371751847 98025018826090073057627771)
        ·
          refine ⟨147037528239135109586441657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98025018826090073057627771 147037528239135109586441657)
          ·
            refine ⟨110278146179351332189831243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147037528239135109586441657 110278146179351332189831243)
            ·
              refine ⟨165417219269026998284746865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110278146179351332189831243 165417219269026998284746865)
              ·
                refine ⟨124062914451770248713560149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165417219269026998284746865 124062914451770248713560149)
                ·
                  refine ⟨1453862278731682602112033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 124062914451770248713560149 1453862278731682602112033)
                  ·
                    refine ⟨1090396709048761951584025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453862278731682602112033 1090396709048761951584025)
                    ·
                      refine ⟨817797531786571463688019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090396709048761951584025 817797531786571463688019)
                      ·
                        rfl

theorem cell23_1592655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2, 2].length) (baseStart_1592655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592655 prefixEnd_1592655 := by exact prefixLift 1592655
  have htrace : WordTrace (prefixWord ++ tailWord_1592655) baseStart_1592655 baseEnd_1592655 := by
    simpa [prefixWord, tailWord_1592655, baseEnd_1592655] using wordTrace_append hprefix tailTrace_1592655
  have hstable : (prefixWord ++ tailWord_1592655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592655).length < 2 ^ (prefixWord ++ tailWord_1592655).sum := by decide
  have hdescent : baseEnd_1592655 < baseStart_1592655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592672 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2]
def baseStart_1592672 : Nat := 118140960795 + 1592672 * 2 ^ 59
def prefixEnd_1592672 : Nat := 4983230072969 + 3 ^ 40 * 1592672 * 2
def baseEnd_1592672 : Nat := 817806260957697897175441

theorem tailTrace_1592672 : CollatzResearch.WordTrace tailWord_1592672 prefixEnd_1592672 817806260957697897175441 := by
  unfold tailWord_1592672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29044760043014412783574135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38726346724019217044765513 29044760043014412783574135)
  ·
    refine ⟨43567140064521619175361203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29044760043014412783574135 43567140064521619175361203)
    ·
      refine ⟨65350710096782428763041805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43567140064521619175361203 65350710096782428763041805)
      ·
        refine ⟨24506516286293410786140677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65350710096782428763041805 24506516286293410786140677)
        ·
          refine ⟨4594971803680014522401377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24506516286293410786140677 4594971803680014522401377)
          ·
            refine ⟨3446228852760010891801033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594971803680014522401377 3446228852760010891801033)
            ·
              refine ⟨2584671639570008168850775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3446228852760010891801033 2584671639570008168850775)
              ·
                refine ⟨3877007459355012253276163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584671639570008168850775 3877007459355012253276163)
                ·
                  refine ⟨5815511189032518379914245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877007459355012253276163 5815511189032518379914245)
                  ·
                    refine ⟨1090408347943597196233921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5815511189032518379914245 1090408347943597196233921)
                    ·
                      refine ⟨817806260957697897175441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090408347943597196233921 817806260957697897175441)
                      ·
                        rfl

theorem cell23_1592672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_1592672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592672 prefixEnd_1592672 := by exact prefixLift 1592672
  have htrace : WordTrace (prefixWord ++ tailWord_1592672) baseStart_1592672 baseEnd_1592672 := by
    simpa [prefixWord, tailWord_1592672, baseEnd_1592672] using wordTrace_append hprefix tailTrace_1592672
  have hstable : (prefixWord ++ tailWord_1592672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592672).length < 2 ^ (prefixWord ++ tailWord_1592672).sum := by decide
  have hdescent : baseEnd_1592672 < baseStart_1592672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592688 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_1592688 : Nat := 118140960795 + 1592688 * 2 ^ 59
def prefixEnd_1592688 : Nat := 4983230072969 + 3 ^ 40 * 1592688 * 2
def baseEnd_1592688 : Nat := 817814476648169834575367

theorem tailTrace_1592688 : CollatzResearch.WordTrace tailWord_1592688 prefixEnd_1592688 817814476648169834575367 := by
  unfold tailWord_1592688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29045051826985430149865359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38726735769313906866487145 29045051826985430149865359)
  ·
    refine ⟨43567577740478145224798039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29045051826985430149865359 43567577740478145224798039)
    ·
      refine ⟨65351366610717217837197059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43567577740478145224798039 65351366610717217837197059)
      ·
        refine ⟨98027049916075826755795589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65351366610717217837197059 98027049916075826755795589)
        ·
          refine ⟨18380071859264217516711673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98027049916075826755795589 18380071859264217516711673)
          ·
            refine ⟨13785053894448163137533755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18380071859264217516711673 13785053894448163137533755)
            ·
              refine ⟨20677580841672244706300633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785053894448163137533755 20677580841672244706300633)
              ·
                refine ⟨15508185631254183529725475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20677580841672244706300633 15508185631254183529725475)
                ·
                  refine ⟨23262278446881275294588213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15508185631254183529725475 23262278446881275294588213)
                  ·
                    refine ⟨2180838604395119558867645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23262278446881275294588213 2180838604395119558867645)
                    ·
                      refine ⟨817814476648169834575367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2180838604395119558867645 817814476648169834575367)
                      ·
                        rfl

theorem cell23_1592688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_1592688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592688 prefixEnd_1592688 := by exact prefixLift 1592688
  have htrace : WordTrace (prefixWord ++ tailWord_1592688) baseStart_1592688 baseEnd_1592688 := by
    simpa [prefixWord, tailWord_1592688, baseEnd_1592688] using wordTrace_append hprefix tailTrace_1592688
  have hstable : (prefixWord ++ tailWord_1592688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592688).length < 2 ^ (prefixWord ++ tailWord_1592688).sum := by decide
  have hdescent : baseEnd_1592688 < baseStart_1592688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592693 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1592693 : Nat := 118140960795 + 1592693 * 2 ^ 59
def prefixEnd_1592693 : Nat := 4983230072969 + 3 ^ 40 * 1592693 * 2
def baseEnd_1592693 : Nat := 817817044051442315012845

theorem tailTrace_1592693 : CollatzResearch.WordTrace tailWord_1592693 prefixEnd_1592693 817817044051442315012845 := by
  unfold tailWord_1592693
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090286018952746153662733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38726857345968497435775155 58090286018952746153662733)
  ·
    refine ⟨21783857257107279807623525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58090286018952746153662733 21783857257107279807623525)
    ·
      refine ⟨4084473235707614963929411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21783857257107279807623525 4084473235707614963929411)
      ·
        refine ⟨6126709853561422445894117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084473235707614963929411 6126709853561422445894117)
        ·
          refine ⟨1148758097542766708605147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6126709853561422445894117 1148758097542766708605147)
          ·
            refine ⟨1723137146314150062907721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148758097542766708605147 1723137146314150062907721)
            ·
              refine ⟨1292352859735612547180791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723137146314150062907721 1292352859735612547180791)
              ·
                refine ⟨1938529289603418820771187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292352859735612547180791 1938529289603418820771187)
                ·
                  refine ⟨2907793934405128231156781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938529289603418820771187 2907793934405128231156781)
                  ·
                    refine ⟨1090422725401923086683793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907793934405128231156781 1090422725401923086683793)
                    ·
                      refine ⟨817817044051442315012845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090422725401923086683793 817817044051442315012845)
                      ·
                        rfl

theorem cell23_1592693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1592693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592693 prefixEnd_1592693 := by exact prefixLift 1592693
  have htrace : WordTrace (prefixWord ++ tailWord_1592693) baseStart_1592693 baseEnd_1592693 := by
    simpa [prefixWord, tailWord_1592693, baseEnd_1592693] using wordTrace_append hprefix tailTrace_1592693
  have hstable : (prefixWord ++ tailWord_1592693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592693).length < 2 ^ (prefixWord ++ tailWord_1592693).sum := by decide
  have hdescent : baseEnd_1592693 < baseStart_1592693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592695 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 5]
def baseStart_1592695 : Nat := 118140960795 + 1592695 * 2 ^ 59
def prefixEnd_1592695 : Nat := 4983230072969 + 3 ^ 40 * 1592695 * 2
def baseEnd_1592695 : Nat := 90868674556972367465315

theorem tailTrace_1592695 : CollatzResearch.WordTrace tailWord_1592695 prefixEnd_1592695 90868674556972367465315 := by
  unfold tailWord_1592695
  simp only [CollatzResearch.WordTrace]
  refine ⟨58090358964945500495235539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38726905976630333663490359 58090358964945500495235539)
  ·
    refine ⟨87135538447418250742853309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58090358964945500495235539 87135538447418250742853309)
    ·
      refine ⟨32675826917781844028569991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87135538447418250742853309 32675826917781844028569991)
      ·
        refine ⟨49013740376672766042854987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32675826917781844028569991 49013740376672766042854987)
        ·
          refine ⟨73520610565009149064282481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49013740376672766042854987 73520610565009149064282481)
          ·
            refine ⟨55140457923756861798211861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73520610565009149064282481 55140457923756861798211861)
            ·
              refine ⟨2584708965176102896791181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55140457923756861798211861 2584708965176102896791181)
              ·
                refine ⟨969265861941038586296693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584708965176102896791181 969265861941038586296693)
                ·
                  refine ⟨90868674556972367465315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969265861941038586296693 90868674556972367465315)
                  ·
                    rfl

theorem cell23_1592695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 5].length) (baseStart_1592695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592695 prefixEnd_1592695 := by exact prefixLift 1592695
  have htrace : WordTrace (prefixWord ++ tailWord_1592695) baseStart_1592695 baseEnd_1592695 := by
    simpa [prefixWord, tailWord_1592695, baseEnd_1592695] using wordTrace_append hprefix tailTrace_1592695
  have hstable : (prefixWord ++ tailWord_1592695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592695).length < 2 ^ (prefixWord ++ tailWord_1592695).sum := by decide
  have hdescent : baseEnd_1592695 < baseStart_1592695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592706 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1592706 : Nat := 118140960795 + 1592706 * 2 ^ 59
def prefixEnd_1592706 : Nat := 4983230072969 + 3 ^ 40 * 1592706 * 2
def baseEnd_1592706 : Nat := 817823719299950764150285

theorem tailTrace_1592706 : CollatzResearch.WordTrace tailWord_1592706 prefixEnd_1592706 817823719299950764150285 := by
  unfold tailWord_1592706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522690041976412343471493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38727173445270432915923981 14522690041976412343471493)
  ·
    refine ⟨2723004382870577314400905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14522690041976412343471493 2723004382870577314400905)
    ·
      refine ⟨2042253287152932985800679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2723004382870577314400905 2042253287152932985800679)
      ·
        refine ⟨3063379930729399478701019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042253287152932985800679 3063379930729399478701019)
        ·
          refine ⟨4595069896094099218051529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063379930729399478701019 4595069896094099218051529)
          ·
            refine ⟨3446302422070574413538647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595069896094099218051529 3446302422070574413538647)
            ·
              refine ⟨5169453633105861620307971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446302422070574413538647 5169453633105861620307971)
              ·
                refine ⟨7754180449658792430461957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169453633105861620307971 7754180449658792430461957)
                ·
                  refine ⟨1453908834311023580711617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7754180449658792430461957 1453908834311023580711617)
                  ·
                    refine ⟨1090431625733267685533713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1453908834311023580711617 1090431625733267685533713)
                    ·
                      refine ⟨817823719299950764150285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090431625733267685533713 817823719299950764150285)
                      ·
                        rfl

theorem cell23_1592706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1592706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592706 prefixEnd_1592706 := by exact prefixLift 1592706
  have htrace : WordTrace (prefixWord ++ tailWord_1592706) baseStart_1592706 baseEnd_1592706 := by
    simpa [prefixWord, tailWord_1592706, baseEnd_1592706] using wordTrace_append hprefix tailTrace_1592706
  have hstable : (prefixWord ++ tailWord_1592706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592706).length < 2 ^ (prefixWord ++ tailWord_1592706).sum := by decide
  have hdescent : baseEnd_1592706 < baseStart_1592706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592768 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 8]
def baseStart_1592768 : Nat := 118140960795 + 1592768 * 2 ^ 59
def prefixEnd_1592768 : Nat := 4983230072969 + 3 ^ 40 * 1592768 * 2
def baseEnd_1592768 : Nat := 90872839455614391286111

theorem tailTrace_1592768 : CollatzResearch.WordTrace tailWord_1592768 prefixEnd_1592768 90872839455614391286111 := by
  unfold tailWord_1592768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29046510746840516981321479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38728680995787355975095305 29046510746840516981321479)
  ·
    refine ⟨43569766120260775471982219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29046510746840516981321479 43569766120260775471982219)
    ·
      refine ⟨65354649180391163207973329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43569766120260775471982219 65354649180391163207973329)
      ·
        refine ⟨49015986885293372405979997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65354649180391163207973329 49015986885293372405979997)
        ·
          refine ⟨18380995081985014652242499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49015986885293372405979997 18380995081985014652242499)
          ·
            refine ⟨27571492622977521978363749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18380995081985014652242499 27571492622977521978363749)
            ·
              refine ⟨5169654866808285370943203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27571492622977521978363749 5169654866808285370943203)
              ·
                refine ⟨7754482300212428056414805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169654866808285370943203 7754482300212428056414805)
                ·
                  refine ⟨90872839455614391286111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7754482300212428056414805 90872839455614391286111)
                  ·
                    rfl

theorem cell23_1592768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_1592768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592768 prefixEnd_1592768 := by exact prefixLift 1592768
  have htrace : WordTrace (prefixWord ++ tailWord_1592768) baseStart_1592768 baseEnd_1592768 := by
    simpa [prefixWord, tailWord_1592768, baseEnd_1592768] using wordTrace_append hprefix tailTrace_1592768
  have hstable : (prefixWord ++ tailWord_1592768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592768).length < 2 ^ (prefixWord ++ tailWord_1592768).sum := by decide
  have hdescent : baseEnd_1592768 < baseStart_1592768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592815 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 1, 5]
def baseStart_1592815 : Nat := 118140960795 + 1592815 * 2 ^ 59
def prefixEnd_1592815 : Nat := 4983230072969 + 3 ^ 40 * 1592815 * 2
def baseEnd_1592815 : Nat := 272626562897096945895761

theorem tailTrace_1592815 : CollatzResearch.WordTrace tailWord_1592815 prefixEnd_1592815 272626562897096945895761 := by
  unfold tailWord_1592815
  simp only [CollatzResearch.WordTrace]
  refine ⟨58094735724510760989603899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38729823816340507326402599 58094735724510760989603899)
  ·
    refine ⟨87142103586766141484405849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58094735724510760989603899 87142103586766141484405849)
    ·
      refine ⟨65356577690074606113304387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87142103586766141484405849 65356577690074606113304387)
      ·
        refine ⟨98034866535111909169956581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65356577690074606113304387 98034866535111909169956581)
        ·
          refine ⟨18381537475333482969366859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98034866535111909169956581 18381537475333482969366859)
          ·
            refine ⟨27572306213000224454050289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18381537475333482969366859 27572306213000224454050289)
            ·
              refine ⟨20679229659750168340537717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27572306213000224454050289 20679229659750168340537717)
              ·
                refine ⟨1938677780601578281925411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20679229659750168340537717 1938677780601578281925411)
                ·
                  refine ⟨2908016670902367422888117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938677780601578281925411 2908016670902367422888117)
                  ·
                    refine ⟨272626562897096945895761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2908016670902367422888117 272626562897096945895761)
                    ·
                      rfl

theorem cell23_1592815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_1592815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592815 prefixEnd_1592815 := by exact prefixLift 1592815
  have htrace : WordTrace (prefixWord ++ tailWord_1592815) baseStart_1592815 baseEnd_1592815 := by
    simpa [prefixWord, tailWord_1592815, baseEnd_1592815] using wordTrace_append hprefix tailTrace_1592815
  have hstable : (prefixWord ++ tailWord_1592815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592815).length < 2 ^ (prefixWord ++ tailWord_1592815).sum := by decide
  have hdescent : baseEnd_1592815 < baseStart_1592815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592856 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_1592856 : Nat := 118140960795 + 1592856 * 2 ^ 59
def prefixEnd_1592856 : Nat := 4983230072969 + 3 ^ 40 * 1592856 * 2
def baseEnd_1592856 : Nat := 817900741398125177274595

theorem tailTrace_1592856 : CollatzResearch.WordTrace tailWord_1592856 prefixEnd_1592856 817900741398125177274595 := by
  unfold tailWord_1592856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048115558681112495923211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38730820744908149994564281 29048115558681112495923211)
  ·
    refine ⟨43572173338021668743884817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048115558681112495923211 43572173338021668743884817)
    ·
      refine ⟨32679130003516251557913613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43572173338021668743884817 32679130003516251557913613)
      ·
        refine ⟨12254673751318594334217605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32679130003516251557913613 12254673751318594334217605)
        ·
          refine ⟨2297751328372236437665801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12254673751318594334217605 2297751328372236437665801)
          ·
            refine ⟨1723313496279177328249351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297751328372236437665801 1723313496279177328249351)
            ·
              refine ⟨2584970244418765992374027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723313496279177328249351 2584970244418765992374027)
              ·
                refine ⟨3877455366628148988561041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584970244418765992374027 3877455366628148988561041)
                ·
                  refine ⟨2908091524971111741420781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877455366628148988561041 2908091524971111741420781)
                  ·
                    refine ⟨1090534321864166903032793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908091524971111741420781 1090534321864166903032793)
                    ·
                      refine ⟨817900741398125177274595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090534321864166903032793 817900741398125177274595)
                      ·
                        rfl

theorem cell23_1592856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_1592856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592856 prefixEnd_1592856 := by exact prefixLift 1592856
  have htrace : WordTrace (prefixWord ++ tailWord_1592856) baseStart_1592856 baseEnd_1592856 := by
    simpa [prefixWord, tailWord_1592856, baseEnd_1592856] using wordTrace_append hprefix tailTrace_1592856
  have hstable : (prefixWord ++ tailWord_1592856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592856).length < 2 ^ (prefixWord ++ tailWord_1592856).sum := by decide
  have hdescent : baseEnd_1592856 < baseStart_1592856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592929 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_1592929 : Nat := 118140960795 + 1592929 * 2 ^ 59
def prefixEnd_1592929 : Nat := 4983230072969 + 3 ^ 40 * 1592929 * 2
def baseEnd_1592929 : Nat := 817938225485903391661759

theorem tailTrace_1592929 : CollatzResearch.WordTrace tailWord_1592929 prefixEnd_1592929 817938225485903391661759 := by
  unfold tailWord_1592929
  simp only [CollatzResearch.WordTrace]
  refine ⟨58098893646097758459253841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38732595764065172306169227 58098893646097758459253841)
  ·
    refine ⟨43574170234573318844440381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58098893646097758459253841 43574170234573318844440381)
    ·
      refine ⟨16340313837964994566665143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43574170234573318844440381 16340313837964994566665143)
      ·
        refine ⟨24510470756947491849997715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16340313837964994566665143 24510470756947491849997715)
        ·
          refine ⟨36765706135421237774996573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24510470756947491849997715 36765706135421237774996573)
          ·
            refine ⟨13787139800782964165623715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36765706135421237774996573 13787139800782964165623715)
            ·
              refine ⟨20680709701174446248435573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13787139800782964165623715 20680709701174446248435573)
              ·
                refine ⟨1938816534485104335790835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20680709701174446248435573 1938816534485104335790835)
                ·
                  refine ⟨2908224801727656503686253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938816534485104335790835 2908224801727656503686253)
                  ·
                    refine ⟨1090584300647871188882345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908224801727656503686253 1090584300647871188882345)
                    ·
                      refine ⟨817938225485903391661759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090584300647871188882345 817938225485903391661759)
                      ·
                        rfl

theorem cell23_1592929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_1592929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592929 prefixEnd_1592929 := by exact prefixLift 1592929
  have htrace : WordTrace (prefixWord ++ tailWord_1592929) baseStart_1592929 baseEnd_1592929 := by
    simpa [prefixWord, tailWord_1592929, baseEnd_1592929] using wordTrace_append hprefix tailTrace_1592929
  have hstable : (prefixWord ++ tailWord_1592929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592929).length < 2 ^ (prefixWord ++ tailWord_1592929).sum := by decide
  have hdescent : baseEnd_1592929 < baseStart_1592929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592935 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1592935 : Nat := 118140960795 + 1592935 * 2 ^ 59
def prefixEnd_1592935 : Nat := 4983230072969 + 3 ^ 40 * 1592935 * 2
def baseEnd_1592935 : Nat := 272647102123276789395577

theorem tailTrace_1592935 : CollatzResearch.WordTrace tailWord_1592935 prefixEnd_1592935 272647102123276789395577 := by
  unfold tailWord_1592935
  simp only [CollatzResearch.WordTrace]
  refine ⟨58099112484076021483972259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38732741656050680989314839 58099112484076021483972259)
  ·
    refine ⟨87148668726114032225958389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58099112484076021483972259 87148668726114032225958389)
    ·
      refine ⟨8170187693073190521183599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87148668726114032225958389 8170187693073190521183599)
      ·
        refine ⟨12255281539609785781775399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8170187693073190521183599 12255281539609785781775399)
        ·
          refine ⟨18382922309414678672663099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12255281539609785781775399 18382922309414678672663099)
          ·
            refine ⟨27574383464122018008994649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18382922309414678672663099 27574383464122018008994649)
            ·
              refine ⟨20680787598091513506745987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27574383464122018008994649 20680787598091513506745987)
              ·
                refine ⟨31021181397137270260118981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20680787598091513506745987 31021181397137270260118981)
                ·
                  refine ⟨5816471511963238173772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31021181397137270260118981 5816471511963238173772309)
                  ·
                    refine ⟨272647102123276789395577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5816471511963238173772309 272647102123276789395577)
                    ·
                      rfl

theorem cell23_1592935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1592935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592935 prefixEnd_1592935 := by exact prefixLift 1592935
  have htrace : WordTrace (prefixWord ++ tailWord_1592935) baseStart_1592935 baseEnd_1592935 := by
    simpa [prefixWord, tailWord_1592935, baseEnd_1592935] using wordTrace_append hprefix tailTrace_1592935
  have hstable : (prefixWord ++ tailWord_1592935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592935).length < 2 ^ (prefixWord ++ tailWord_1592935).sum := by decide
  have hdescent : baseEnd_1592935 < baseStart_1592935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592955 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_1592955 : Nat := 118140960795 + 1592955 * 2 ^ 59
def prefixEnd_1592955 : Nat := 4983230072969 + 3 ^ 40 * 1592955 * 2
def baseEnd_1592955 : Nat := 817951575982920289936639

theorem tailTrace_1592955 : CollatzResearch.WordTrace tailWord_1592955 prefixEnd_1592955 817951575982920289936639 := by
  unfold tailWord_1592955
  simp only [CollatzResearch.WordTrace]
  refine ⟨58099841944003564899700319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38733227962669043266466879 58099841944003564899700319)
  ·
    refine ⟨87149762916005347349550479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58099841944003564899700319 87149762916005347349550479)
    ·
      refine ⟨130724644374008021024325719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87149762916005347349550479 130724644374008021024325719)
      ·
        refine ⟨196086966561012031536488579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130724644374008021024325719 196086966561012031536488579)
        ·
          refine ⟨294130449841518047304732869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196086966561012031536488579 294130449841518047304732869)
          ·
            refine ⟨55149459345284633869637413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294130449841518047304732869 55149459345284633869637413)
            ·
              refine ⟨10340523627240868850557015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55149459345284633869637413 10340523627240868850557015)
              ·
                refine ⟨15510785440861303275835523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340523627240868850557015 15510785440861303275835523)
                ·
                  refine ⟨23266178161291954913753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15510785440861303275835523 23266178161291954913753285)
                  ·
                    refine ⟨4362408405242241546328741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23266178161291954913753285 4362408405242241546328741)
                    ·
                      refine ⟨817951575982920289936639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4362408405242241546328741 817951575982920289936639)
                      ·
                        rfl

theorem cell23_1592955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_1592955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592955 prefixEnd_1592955 := by exact prefixLift 1592955
  have htrace : WordTrace (prefixWord ++ tailWord_1592955) baseStart_1592955 baseEnd_1592955 := by
    simpa [prefixWord, tailWord_1592955, baseEnd_1592955] using wordTrace_append hprefix tailTrace_1592955
  have hstable : (prefixWord ++ tailWord_1592955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592955).length < 2 ^ (prefixWord ++ tailWord_1592955).sum := by decide
  have hdescent : baseEnd_1592955 < baseStart_1592955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592965 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 9]
def baseStart_1592965 : Nat := 118140960795 + 1592965 * 2 ^ 59
def prefixEnd_1592965 : Nat := 4983230072969 + 3 ^ 40 * 1592965 * 2
def baseEnd_1592965 : Nat := 90884078976607250090177

theorem tailTrace_1592965 : CollatzResearch.WordTrace tailWord_1592965 prefixEnd_1592965 90884078976607250090177 := by
  unfold tailWord_1592965
  simp only [CollatzResearch.WordTrace]
  refine ⟨58100206673967336607564349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38733471115978224405042899 58100206673967336607564349)
  ·
    refine ⟨21787577502737751227836631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58100206673967336607564349 21787577502737751227836631)
    ·
      refine ⟨32681366254106626841754947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21787577502737751227836631 32681366254106626841754947)
      ·
        refine ⟨49022049381159940262632421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32681366254106626841754947 49022049381159940262632421)
        ·
          refine ⟨9191634258967488799243579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49022049381159940262632421 9191634258967488799243579)
          ·
            refine ⟨13787451388451233198865369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9191634258967488799243579 13787451388451233198865369)
            ·
              refine ⟨10340588541338424899149027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13787451388451233198865369 10340588541338424899149027)
              ·
                refine ⟨15510882812007637348723541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340588541338424899149027 15510882812007637348723541)
                ·
                  refine ⟨90884078976607250090177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15510882812007637348723541 90884078976607250090177)
                  ·
                    rfl

theorem cell23_1592965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_1592965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592965 prefixEnd_1592965 := by exact prefixLift 1592965
  have htrace : WordTrace (prefixWord ++ tailWord_1592965) baseStart_1592965 baseEnd_1592965 := by
    simpa [prefixWord, tailWord_1592965, baseEnd_1592965] using wordTrace_append hprefix tailTrace_1592965
  have hstable : (prefixWord ++ tailWord_1592965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592965).length < 2 ^ (prefixWord ++ tailWord_1592965).sum := by decide
  have hdescent : baseEnd_1592965 < baseStart_1592965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592980 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1592980 : Nat := 118140960795 + 1592980 * 2 ^ 59
def prefixEnd_1592980 : Nat := 4983230072969 + 3 ^ 40 * 1592980 * 2
def baseEnd_1592980 : Nat := 817964412999282692124025

theorem tailTrace_1592980 : CollatzResearch.WordTrace tailWord_1592980 prefixEnd_1592980 817964412999282692124025 := by
  unfold tailWord_1592980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29050376884456497084680197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38733835845941996112906929 29050376884456497084680197)
  ·
    refine ⟨5446945665835593203377537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29050376884456497084680197 5446945665835593203377537)
    ·
      refine ⟨4085209249376694902533153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5446945665835593203377537 4085209249376694902533153)
      ·
        refine ⟨3063906937032521176899865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085209249376694902533153 3063906937032521176899865)
        ·
          refine ⟨2297930202774390882674899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3063906937032521176899865 2297930202774390882674899)
          ·
            refine ⟨3446895304161586324012349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297930202774390882674899 3446895304161586324012349)
            ·
              refine ⟨1292585739060594871504631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3446895304161586324012349 1292585739060594871504631)
              ·
                refine ⟨1938878608590892307256947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292585739060594871504631 1938878608590892307256947)
                ·
                  refine ⟨2908317912886338460885421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938878608590892307256947 2908317912886338460885421)
                  ·
                    refine ⟨1090619217332376922832033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2908317912886338460885421 1090619217332376922832033)
                    ·
                      refine ⟨817964412999282692124025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090619217332376922832033 817964412999282692124025)
                      ·
                        rfl

theorem cell23_1592980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1592980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592980 prefixEnd_1592980 := by exact prefixLift 1592980
  have htrace : WordTrace (prefixWord ++ tailWord_1592980) baseStart_1592980 baseEnd_1592980 := by
    simpa [prefixWord, tailWord_1592980, baseEnd_1592980] using wordTrace_append hprefix tailTrace_1592980
  have hstable : (prefixWord ++ tailWord_1592980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592980).length < 2 ^ (prefixWord ++ tailWord_1592980).sum := by decide
  have hdescent : baseEnd_1592980 < baseStart_1592980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1592993 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1592993 : Nat := 118140960795 + 1592993 * 2 ^ 59
def prefixEnd_1592993 : Nat := 4983230072969 + 3 ^ 40 * 1592993 * 2
def baseEnd_1592993 : Nat := 817971088247791141261465

theorem tailTrace_1592993 : CollatzResearch.WordTrace tailWord_1592993 prefixEnd_1592993 817971088247791141261465 := by
  unfold tailWord_1592993
  simp only [CollatzResearch.WordTrace]
  refine ⟨58101227917865897389583633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38734151945243931593055755 58101227917865897389583633)
  ·
    refine ⟨43575920938399423042187725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58101227917865897389583633 43575920938399423042187725)
    ·
      refine ⟨16340970351899783640820397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43575920938399423042187725 16340970351899783640820397)
      ·
        refine ⟨6127863881962418865307649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16340970351899783640820397 6127863881962418865307649)
        ·
          refine ⟨4595897911471814148980737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127863881962418865307649 4595897911471814148980737)
          ·
            refine ⟨3446923433603860611735553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595897911471814148980737 3446923433603860611735553)
            ·
              refine ⟨2585192575202895458801665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3446923433603860611735553 2585192575202895458801665)
              ·
                refine ⟨1938894431402171594101249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585192575202895458801665 1938894431402171594101249)
                ·
                  refine ⟨1454170823551628695575937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1938894431402171594101249 1454170823551628695575937)
                  ·
                    refine ⟨1090628117663721521681953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1454170823551628695575937 1090628117663721521681953)
                    ·
                      refine ⟨817971088247791141261465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090628117663721521681953 817971088247791141261465)
                      ·
                        rfl

theorem cell23_1592993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1592993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1592993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1592993 prefixEnd_1592993 := by exact prefixLift 1592993
  have htrace : WordTrace (prefixWord ++ tailWord_1592993) baseStart_1592993 baseEnd_1592993 := by
    simpa [prefixWord, tailWord_1592993, baseEnd_1592993] using wordTrace_append hprefix tailTrace_1592993
  have hstable : (prefixWord ++ tailWord_1592993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1592993).length < 2 ^ (prefixWord ++ tailWord_1592993).sum := by decide
  have hdescent : baseEnd_1592993 < baseStart_1592993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1592993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593006 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1593006 : Nat := 118140960795 + 1593006 * 2 ^ 59
def prefixEnd_1593006 : Nat := 4983230072969 + 3 ^ 40 * 1593006 * 2
def baseEnd_1593006 : Nat := 817977763496299590398905

theorem tailTrace_1593006 : CollatzResearch.WordTrace tailWord_1593006 prefixEnd_1593006 817977763496299590398905 := by
  unfold tailWord_1593006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262712758352350076225859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38734468044545867073204581 7262712758352350076225859)
  ·
    refine ⟨10894069137528525114338789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7262712758352350076225859 10894069137528525114338789)
    ·
      refine ⟨2042637963286598458938523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10894069137528525114338789 2042637963286598458938523)
      ·
        refine ⟨3063956944929897688407785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042637963286598458938523 3063956944929897688407785)
        ·
          refine ⟨2297967708697423266305839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3063956944929897688407785 2297967708697423266305839)
          ·
            refine ⟨3446951563046134899458759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297967708697423266305839 3446951563046134899458759)
            ·
              refine ⟨5170427344569202349188139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446951563046134899458759 5170427344569202349188139)
              ·
                refine ⟨7755641016853803523782209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170427344569202349188139 7755641016853803523782209)
                ·
                  refine ⟨5816730762640352642836657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755641016853803523782209 5816730762640352642836657)
                  ·
                    refine ⟨4362548071980264482127493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816730762640352642836657 4362548071980264482127493)
                    ·
                      refine ⟨817977763496299590398905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4362548071980264482127493 817977763496299590398905)
                      ·
                        rfl

theorem cell23_1593006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1593006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593006 prefixEnd_1593006 := by exact prefixLift 1593006
  have htrace : WordTrace (prefixWord ++ tailWord_1593006) baseStart_1593006 baseEnd_1593006 := by
    simpa [prefixWord, tailWord_1593006, baseEnd_1593006] using wordTrace_append hprefix tailTrace_1593006
  have hstable : (prefixWord ++ tailWord_1593006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593006).length < 2 ^ (prefixWord ++ tailWord_1593006).sum := by decide
  have hdescent : baseEnd_1593006 < baseStart_1593006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593032 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1593032 : Nat := 118140960795 + 1593032 * 2 ^ 59
def prefixEnd_1593032 : Nat := 4983230072969 + 3 ^ 40 * 1593032 * 2
def baseEnd_1593032 : Nat := 817991113993316488673785

theorem tailTrace_1593032 : CollatzResearch.WordTrace tailWord_1593032 prefixEnd_1593032 817991113993316488673785 := by
  unfold tailWord_1593032
  simp only [CollatzResearch.WordTrace]
  refine ⟨29051325182362303525126675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38735100243149738033502233 29051325182362303525126675)
  ·
    refine ⟨43576987773543455287690013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29051325182362303525126675 43576987773543455287690013)
    ·
      refine ⟨16341370415078795732883755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43576987773543455287690013 16341370415078795732883755)
      ·
        refine ⟨24512055622618193599325633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16341370415078795732883755 24512055622618193599325633)
        ·
          refine ⟨18384041716963645199494225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24512055622618193599325633 18384041716963645199494225)
          ·
            refine ⟨13788031287722733899620669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18384041716963645199494225 13788031287722733899620669)
            ·
              refine ⟨5170511732896025212357751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13788031287722733899620669 5170511732896025212357751)
              ·
                refine ⟨7755767599344037818536627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170511732896025212357751 7755767599344037818536627)
                ·
                  refine ⟨11633651399016056727804941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7755767599344037818536627 11633651399016056727804941)
                  ·
                    refine ⟨4362619274631021272926853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11633651399016056727804941 4362619274631021272926853)
                    ·
                      refine ⟨817991113993316488673785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4362619274631021272926853 817991113993316488673785)
                      ·
                        rfl

theorem cell23_1593032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1593032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593032 prefixEnd_1593032 := by exact prefixLift 1593032
  have htrace : WordTrace (prefixWord ++ tailWord_1593032) baseStart_1593032 baseEnd_1593032 := by
    simpa [prefixWord, tailWord_1593032, baseEnd_1593032] using wordTrace_append hprefix tailTrace_1593032
  have hstable : (prefixWord ++ tailWord_1593032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593032).length < 2 ^ (prefixWord ++ tailWord_1593032).sum := by decide
  have hdescent : baseEnd_1593032 < baseStart_1593032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593049 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 2, 4, 2]
def baseStart_1593049 : Nat := 118140960795 + 1593049 * 2 ^ 59
def prefixEnd_1593049 : Nat := 4983230072969 + 3 ^ 40 * 1593049 * 2
def baseEnd_1593049 : Nat := 817999843164442922161207

theorem tailTrace_1593049 : CollatzResearch.WordTrace tailWord_1593049 prefixEnd_1593049 817999843164442922161207 := by
  unfold tailWord_1593049
  simp only [CollatzResearch.WordTrace]
  refine ⟨58103270405663018953622201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38735513603775345969081467 58103270405663018953622201)
  ·
    refine ⟨43577452804247264215216651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58103270405663018953622201 43577452804247264215216651)
    ·
      refine ⟨65366179206370896322824977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43577452804247264215216651 65366179206370896322824977)
      ·
        refine ⟨49024634404778172242118733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65366179206370896322824977 49024634404778172242118733)
        ·
          refine ⟨18384237901791814590794525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49024634404778172242118733 18384237901791814590794525)
          ·
            refine ⟨6894089213171930471547947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18384237901791814590794525 6894089213171930471547947)
            ·
              refine ⟨10341133819757895707321921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894089213171930471547947 10341133819757895707321921)
              ·
                refine ⟨7755850364818421780491441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10341133819757895707321921 7755850364818421780491441)
                ·
                  refine ⟨5816887773613816335368581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755850364818421780491441 5816887773613816335368581)
                  ·
                    refine ⟨1090666457552590562881609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5816887773613816335368581 1090666457552590562881609)
                    ·
                      refine ⟨817999843164442922161207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090666457552590562881609 817999843164442922161207)
                      ·
                        rfl

theorem cell23_1593049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_1593049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593049 prefixEnd_1593049 := by exact prefixLift 1593049
  have htrace : WordTrace (prefixWord ++ tailWord_1593049) baseStart_1593049 baseEnd_1593049 := by
    simpa [prefixWord, tailWord_1593049, baseEnd_1593049] using wordTrace_append hprefix tailTrace_1593049
  have hstable : (prefixWord ++ tailWord_1593049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593049).length < 2 ^ (prefixWord ++ tailWord_1593049).sum := by decide
  have hdescent : baseEnd_1593049 < baseStart_1593049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593069 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1593069 : Nat := 118140960795 + 1593069 * 2 ^ 59
def prefixEnd_1593069 : Nat := 4983230072969 + 3 ^ 40 * 1593069 * 2
def baseEnd_1593069 : Nat := 818010112777532843911115

theorem tailTrace_1593069 : CollatzResearch.WordTrace tailWord_1593069 prefixEnd_1593069 818010112777532843911115 := by
  unfold tailWord_1593069
  simp only [CollatzResearch.WordTrace]
  refine ⟨58103999865590562369350261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38735999910393708246233507 58103999865590562369350261)
  ·
    refine ⟨5447249987399115222126587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58103999865590562369350261 5447249987399115222126587)
    ·
      refine ⟨8170874981098672833189881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447249987399115222126587 8170874981098672833189881)
      ·
        refine ⟨6128156235824004624892411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8170874981098672833189881 6128156235824004624892411)
        ·
          refine ⟨9192234353736006937338617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128156235824004624892411 9192234353736006937338617)
          ·
            refine ⟨6894175765302005203003963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9192234353736006937338617 6894175765302005203003963)
            ·
              refine ⟨10341263647953007804505945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894175765302005203003963 10341263647953007804505945)
              ·
                refine ⟨7755947735964755853379459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10341263647953007804505945 7755947735964755853379459)
                ·
                  refine ⟨11633921603947133780069189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7755947735964755853379459 11633921603947133780069189)
                  ·
                    refine ⟨2181360300740087583762973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11633921603947133780069189 2181360300740087583762973)
                    ·
                      refine ⟨818010112777532843911115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181360300740087583762973 818010112777532843911115)
                      ·
                        rfl

theorem cell23_1593069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1593069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593069 prefixEnd_1593069 := by exact prefixLift 1593069
  have htrace : WordTrace (prefixWord ++ tailWord_1593069) baseStart_1593069 baseEnd_1593069 := by
    simpa [prefixWord, tailWord_1593069, baseEnd_1593069] using wordTrace_append hprefix tailTrace_1593069
  have hstable : (prefixWord ++ tailWord_1593069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593069).length < 2 ^ (prefixWord ++ tailWord_1593069).sum := by decide
  have hdescent : baseEnd_1593069 < baseStart_1593069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593082 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_1593082 : Nat := 118140960795 + 1593082 * 2 ^ 59
def prefixEnd_1593082 : Nat := 4983230072969 + 3 ^ 40 * 1593082 * 2
def baseEnd_1593082 : Nat := 818016788026041293048555

theorem tailTrace_1593082 : CollatzResearch.WordTrace tailWord_1593082 prefixEnd_1593082 818016788026041293048555 := by
  unfold tailWord_1593082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14526118503635866397393375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38736316009695643726382333 14526118503635866397393375)
  ·
    refine ⟨21789177755453799596090063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14526118503635866397393375 21789177755453799596090063)
    ·
      refine ⟨32683766633180699394135095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21789177755453799596090063 32683766633180699394135095)
      ·
        refine ⟨49025649949771049091202643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32683766633180699394135095 49025649949771049091202643)
        ·
          refine ⟨73538474924656573636803965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49025649949771049091202643 73538474924656573636803965)
          ·
            refine ⟨27576928096746215113801487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73538474924656573636803965 27576928096746215113801487)
            ·
              refine ⟨41365392145119322670702231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27576928096746215113801487 41365392145119322670702231)
              ·
                refine ⟨62048088217678984006053347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41365392145119322670702231 62048088217678984006053347)
                ·
                  refine ⟨93072132326518476009080021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62048088217678984006053347 93072132326518476009080021)
                  ·
                    refine ⟨2181378101402776781462813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 93072132326518476009080021 2181378101402776781462813)
                    ·
                      refine ⟨818016788026041293048555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181378101402776781462813 818016788026041293048555)
                      ·
                        rfl

theorem cell23_1593082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_1593082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593082 prefixEnd_1593082 := by exact prefixLift 1593082
  have htrace : WordTrace (prefixWord ++ tailWord_1593082) baseStart_1593082 baseEnd_1593082 := by
    simpa [prefixWord, tailWord_1593082, baseEnd_1593082] using wordTrace_append hprefix tailTrace_1593082
  have hstable : (prefixWord ++ tailWord_1593082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593082).length < 2 ^ (prefixWord ++ tailWord_1593082).sum := by decide
  have hdescent : baseEnd_1593082 < baseStart_1593082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593099 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 3]
def baseStart_1593099 : Nat := 118140960795 + 1593099 * 2 ^ 59
def prefixEnd_1593099 : Nat := 4983230072969 + 3 ^ 40 * 1593099 * 2
def baseEnd_1593099 : Nat := 818025517197167726535977

theorem tailTrace_1593099 : CollatzResearch.WordTrace tailWord_1593099 prefixEnd_1593099 818025517197167726535977 := by
  unfold tailWord_1593099
  simp only [CollatzResearch.WordTrace]
  refine ⟨58105094055481877492942351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38736729370321251661961567 58105094055481877492942351)
  ·
    refine ⟨87157641083222816239413527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58105094055481877492942351 87157641083222816239413527)
    ·
      refine ⟨130736461624834224359120291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87157641083222816239413527 130736461624834224359120291)
      ·
        refine ⟨196104692437251336538680437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130736461624834224359120291 196104692437251336538680437)
        ·
          refine ⟨18384814915992312800501291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196104692437251336538680437 18384814915992312800501291)
          ·
            refine ⟨27577222373988469200751937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18384814915992312800501291 27577222373988469200751937)
            ·
              refine ⟨20682916780491351900563953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27577222373988469200751937 20682916780491351900563953)
              ·
                refine ⟨15512187585368513925422965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20682916780491351900563953 15512187585368513925422965)
                ·
                  refine ⟨1454267586128298180508403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15512187585368513925422965 1454267586128298180508403)
                  ·
                    refine ⟨2181401379192447270762605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1454267586128298180508403 2181401379192447270762605)
                    ·
                      refine ⟨818025517197167726535977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181401379192447270762605 818025517197167726535977)
                      ·
                        rfl

theorem cell23_1593099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 3].length) (baseStart_1593099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593099 prefixEnd_1593099 := by exact prefixLift 1593099
  have htrace : WordTrace (prefixWord ++ tailWord_1593099) baseStart_1593099 baseEnd_1593099 := by
    simpa [prefixWord, tailWord_1593099, baseEnd_1593099] using wordTrace_append hprefix tailTrace_1593099
  have hstable : (prefixWord ++ tailWord_1593099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593099).length < 2 ^ (prefixWord ++ tailWord_1593099).sum := by decide
  have hdescent : baseEnd_1593099 < baseStart_1593099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593149 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1593149 : Nat := 118140960795 + 1593149 * 2 ^ 59
def prefixEnd_1593149 : Nat := 4983230072969 + 3 ^ 40 * 1593149 * 2
def baseEnd_1593149 : Nat := 272683730409964176970249

theorem tailTrace_1593149 : CollatzResearch.WordTrace tailWord_1593149 prefixEnd_1593149 272683730409964176970249 := by
  unfold tailWord_1593149
  simp only [CollatzResearch.WordTrace]
  refine ⟨58106917705300736032262501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38737945136867157354841667 58106917705300736032262501)
  ·
    refine ⟨10895047069743888006049219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58106917705300736032262501 10895047069743888006049219)
    ·
      refine ⟨16342570604615832009073829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10895047069743888006049219 16342570604615832009073829)
      ·
        refine ⟨3064231988365468501701343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16342570604615832009073829 3064231988365468501701343)
        ·
          refine ⟨4596347982548202752552015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064231988365468501701343 4596347982548202752552015)
          ·
            refine ⟨6894521973822304128828023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596347982548202752552015 6894521973822304128828023)
            ·
              refine ⟨10341782960733456193242035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894521973822304128828023 10341782960733456193242035)
              ·
                refine ⟨15512674441100184289863053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10341782960733456193242035 15512674441100184289863053)
                ·
                  refine ⟨5817252915412569108698645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15512674441100184289863053 5817252915412569108698645)
                  ·
                    refine ⟨272683730409964176970249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5817252915412569108698645 272683730409964176970249)
                    ·
                      rfl

theorem cell23_1593149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1593149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593149 prefixEnd_1593149 := by exact prefixLift 1593149
  have htrace : WordTrace (prefixWord ++ tailWord_1593149) baseStart_1593149 baseEnd_1593149 := by
    simpa [prefixWord, tailWord_1593149, baseEnd_1593149] using wordTrace_append hprefix tailTrace_1593149
  have hstable : (prefixWord ++ tailWord_1593149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593149).length < 2 ^ (prefixWord ++ tailWord_1593149).sum := by decide
  have hdescent : baseEnd_1593149 < baseStart_1593149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593159 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_1593159 : Nat := 118140960795 + 1593159 * 2 ^ 59
def prefixEnd_1593159 : Nat := 4983230072969 + 3 ^ 40 * 1593159 * 2
def baseEnd_1593159 : Nat := 818056326036437491785701

theorem tailTrace_1593159 : CollatzResearch.WordTrace tailWord_1593159 prefixEnd_1593159 818056326036437491785701 := by
  unfold tailWord_1593159
  simp only [CollatzResearch.WordTrace]
  refine ⟨58107282435264507740126531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38738188290176338493417687 58107282435264507740126531)
  ·
    refine ⟨87160923652896761610189797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58107282435264507740126531 87160923652896761610189797)
    ·
      refine ⟨16342673184918142801910587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87160923652896761610189797 16342673184918142801910587)
      ·
        refine ⟨24514009777377214202865881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16342673184918142801910587 24514009777377214202865881)
        ·
          refine ⟨18385507333032910652149411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24514009777377214202865881 18385507333032910652149411)
          ·
            refine ⟨27578260999549365978224117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18385507333032910652149411 27578260999549365978224117)
            ·
              refine ⟨2585461968707753060458511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27578260999549365978224117 2585461968707753060458511)
              ·
                refine ⟨3878192953061629590687767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585461968707753060458511 3878192953061629590687767)
                ·
                  refine ⟨5817289429592444386031651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878192953061629590687767 5817289429592444386031651)
                  ·
                    refine ⟨8725934144388666579047477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817289429592444386031651 8725934144388666579047477)
                    ·
                      refine ⟨818056326036437491785701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8725934144388666579047477 818056326036437491785701)
                      ·
                        rfl

theorem cell23_1593159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_1593159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593159 prefixEnd_1593159 := by exact prefixLift 1593159
  have htrace : WordTrace (prefixWord ++ tailWord_1593159) baseStart_1593159 baseEnd_1593159 := by
    simpa [prefixWord, tailWord_1593159, baseEnd_1593159] using wordTrace_append hprefix tailTrace_1593159
  have hstable : (prefixWord ++ tailWord_1593159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593159).length < 2 ^ (prefixWord ++ tailWord_1593159).sum := by decide
  have hdescent : baseEnd_1593159 < baseStart_1593159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593186 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1593186 : Nat := 118140960795 + 1593186 * 2 ^ 59
def prefixEnd_1593186 : Nat := 4983230072969 + 3 ^ 40 * 1593186 * 2
def baseEnd_1593186 : Nat := 818070190014108886148077

theorem tailTrace_1593186 : CollatzResearch.WordTrace tailWord_1593186 prefixEnd_1593186 818070190014108886148077 := by
  unfold tailWord_1593186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527066801541672837839853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38738844804111127567572941 14527066801541672837839853)
  ·
    refine ⟨5447650050578127314189945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14527066801541672837839853 5447650050578127314189945)
    ·
      refine ⟨4085737537933595485642459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5447650050578127314189945 4085737537933595485642459)
      ·
        refine ⟨6128606306900393228463689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085737537933595485642459 6128606306900393228463689)
        ·
          refine ⟨4596454730175294921347767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128606306900393228463689 4596454730175294921347767)
          ·
            refine ⟨6894682095262942382021651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596454730175294921347767 6894682095262942382021651)
            ·
              refine ⟨10342023142894413573032477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894682095262942382021651 10342023142894413573032477)
              ·
                refine ⟨3878258678585405089887179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10342023142894413573032477 3878258678585405089887179)
                ·
                  refine ⟨5817388017878107634830769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878258678585405089887179 5817388017878107634830769)
                  ·
                    refine ⟨4363041013408580726123077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5817388017878107634830769 4363041013408580726123077)
                    ·
                      refine ⟨818070190014108886148077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4363041013408580726123077 818070190014108886148077)
                      ·
                        rfl

theorem cell23_1593186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1593186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593186 prefixEnd_1593186 := by exact prefixLift 1593186
  have htrace : WordTrace (prefixWord ++ tailWord_1593186) baseStart_1593186 baseEnd_1593186 := by
    simpa [prefixWord, tailWord_1593186, baseEnd_1593186] using wordTrace_append hprefix tailTrace_1593186
  have hstable : (prefixWord ++ tailWord_1593186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593186).length < 2 ^ (prefixWord ++ tailWord_1593186).sum := by decide
  have hdescent : baseEnd_1593186 < baseStart_1593186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593217 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1593217 : Nat := 118140960795 + 1593217 * 2 ^ 59
def prefixEnd_1593217 : Nat := 4983230072969 + 3 ^ 40 * 1593217 * 2
def baseEnd_1593217 : Nat := 272695369304799421620145

theorem tailTrace_1593217 : CollatzResearch.WordTrace tailWord_1593217 prefixEnd_1593217 272695369304799421620145 := by
  unfold tailWord_1593217
  simp only [CollatzResearch.WordTrace]
  refine ⟨58109397869054383645737905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38739598579369589097158603 58109397869054383645737905)
  ·
    refine ⟨43582048401790787734303429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58109397869054383645737905 43582048401790787734303429)
    ·
      refine ⟨8171634075335772700181893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43582048401790787734303429 8171634075335772700181893)
      ·
        refine ⟨1532181389125457381284105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8171634075335772700181893 1532181389125457381284105)
        ·
          refine ⟨1149136041844093035963079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532181389125457381284105 1149136041844093035963079)
          ·
            refine ⟨1723704062766139553944619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149136041844093035963079 1723704062766139553944619)
            ·
              refine ⟨2585556094149209330916929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723704062766139553944619 2585556094149209330916929)
              ·
                refine ⟨1939167070611906998187697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585556094149209330916929 1939167070611906998187697)
                ·
                  refine ⟨1454375302958930248640773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1939167070611906998187697 1454375302958930248640773)
                  ·
                    refine ⟨272695369304799421620145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1454375302958930248640773 272695369304799421620145)
                    ·
                      rfl

theorem cell23_1593217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1593217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593217 prefixEnd_1593217 := by exact prefixLift 1593217
  have htrace : WordTrace (prefixWord ++ tailWord_1593217) baseStart_1593217 baseEnd_1593217 := by
    simpa [prefixWord, tailWord_1593217, baseEnd_1593217] using wordTrace_append hprefix tailTrace_1593217
  have hstable : (prefixWord ++ tailWord_1593217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593217).length < 2 ^ (prefixWord ++ tailWord_1593217).sum := by decide
  have hdescent : baseEnd_1593217 < baseStart_1593217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593223 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_1593223 : Nat := 118140960795 + 1593223 * 2 ^ 59
def prefixEnd_1593223 : Nat := 4983230072969 + 3 ^ 40 * 1593223 * 2
def baseEnd_1593223 : Nat := 818089188798325241385407

theorem tailTrace_1593223 : CollatzResearch.WordTrace tailWord_1593223 prefixEnd_1593223 818089188798325241385407 := by
  unfold tailWord_1593223
  simp only [CollatzResearch.WordTrace]
  refine ⟨58109616707032646670456323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38739744471355097780304215 58109616707032646670456323)
  ·
    refine ⟨87164425060548970005684485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58109616707032646670456323 87164425060548970005684485)
    ·
      refine ⟨16343329698852931876065841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87164425060548970005684485 16343329698852931876065841)
      ·
        refine ⟨12257497274139698907049381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16343329698852931876065841 12257497274139698907049381)
        ·
          refine ⟨2298280738901193545071759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12257497274139698907049381 2298280738901193545071759)
          ·
            refine ⟨3447421108351790317607639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298280738901193545071759 3447421108351790317607639)
            ·
              refine ⟨5171131662527685476411459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447421108351790317607639 5171131662527685476411459)
              ·
                refine ⟨7756697493791528214617189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171131662527685476411459 7756697493791528214617189)
                ·
                  refine ⟨1454380780085911540240723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7756697493791528214617189 1454380780085911540240723)
                  ·
                    refine ⟨2181571170128867310361085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1454380780085911540240723 2181571170128867310361085)
                    ·
                      refine ⟨818089188798325241385407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181571170128867310361085 818089188798325241385407)
                      ·
                        rfl

theorem cell23_1593223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_1593223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593223 prefixEnd_1593223 := by exact prefixLift 1593223
  have htrace : WordTrace (prefixWord ++ tailWord_1593223) baseStart_1593223 baseEnd_1593223 := by
    simpa [prefixWord, tailWord_1593223, baseEnd_1593223] using wordTrace_append hprefix tailTrace_1593223
  have hstable : (prefixWord ++ tailWord_1593223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593223).length < 2 ^ (prefixWord ++ tailWord_1593223).sum := by decide
  have hdescent : baseEnd_1593223 < baseStart_1593223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593239 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 2, 6]
def baseStart_1593239 : Nat := 118140960795 + 1593239 * 2 ^ 59
def prefixEnd_1593239 : Nat := 4983230072969 + 3 ^ 40 * 1593239 * 2
def baseEnd_1593239 : Nat := 272699134829599059595111

theorem tailTrace_1593239 : CollatzResearch.WordTrace tailWord_1593239 prefixEnd_1593239 272699134829599059595111 := by
  unfold tailWord_1593239
  simp only [CollatzResearch.WordTrace]
  refine ⟨58110200274974681403038771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38740133516649787602025847 58110200274974681403038771)
  ·
    refine ⟨87165300412462022104558157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58110200274974681403038771 87165300412462022104558157)
    ·
      refine ⟨32686987654673258289209309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87165300412462022104558157 32686987654673258289209309)
      ·
        refine ⟨12257620370502471858453491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32686987654673258289209309 12257620370502471858453491)
        ·
          refine ⟨18386430555753707787680237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12257620370502471858453491 18386430555753707787680237)
          ·
            refine ⟨6894911458407640420380089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18386430555753707787680237 6894911458407640420380089)
            ·
              refine ⟨5171183593805730315285067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6894911458407640420380089 5171183593805730315285067)
              ·
                refine ⟨7756775390708595472927601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171183593805730315285067 7756775390708595472927601)
                ·
                  refine ⟨5817581543031446604695701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756775390708595472927601 5817581543031446604695701)
                  ·
                    refine ⟨272699134829599059595111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5817581543031446604695701 272699134829599059595111)
                    ·
                      rfl

theorem cell23_1593239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_1593239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593239 prefixEnd_1593239 := by exact prefixLift 1593239
  have htrace : WordTrace (prefixWord ++ tailWord_1593239) baseStart_1593239 baseEnd_1593239 := by
    simpa [prefixWord, tailWord_1593239, baseEnd_1593239] using wordTrace_append hprefix tailTrace_1593239
  have hstable : (prefixWord ++ tailWord_1593239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593239).length < 2 ^ (prefixWord ++ tailWord_1593239).sum := by decide
  have hdescent : baseEnd_1593239 < baseStart_1593239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593240 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1593240 : Nat := 118140960795 + 1593240 * 2 ^ 59
def prefixEnd_1593240 : Nat := 4983230072969 + 3 ^ 40 * 1593240 * 2
def baseEnd_1593240 : Nat := 818097917969451674872829

theorem tailTrace_1593240 : CollatzResearch.WordTrace tailWord_1593240 prefixEnd_1593240 818097917969451674872829 := by
  unfold tailWord_1593240
  simp only [CollatzResearch.WordTrace]
  refine ⟨29055118373985529286912587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38740157831980705715883449 29055118373985529286912587)
  ·
    refine ⟨43582677560978293930368881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29055118373985529286912587 43582677560978293930368881)
    ·
      refine ⟨32687008170733720447776661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43582677560978293930368881 32687008170733720447776661)
      ·
        refine ⟨1532203508003143145989531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32687008170733720447776661 1532203508003143145989531)
        ·
          refine ⟨2298305262004714718984297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532203508003143145989531 2298305262004714718984297)
          ·
            refine ⟨1723728946503536039238223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2298305262004714718984297 1723728946503536039238223)
            ·
              refine ⟨2585593419755304058857335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723728946503536039238223 2585593419755304058857335)
              ·
                refine ⟨3878390129632956088286003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585593419755304058857335 3878390129632956088286003)
                ·
                  refine ⟨5817585194449434132429005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878390129632956088286003 5817585194449434132429005)
                  ·
                    refine ⟨2181594447918537799660877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5817585194449434132429005 2181594447918537799660877)
                    ·
                      refine ⟨818097917969451674872829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181594447918537799660877 818097917969451674872829)
                      ·
                        rfl

theorem cell23_1593240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1593240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593240 prefixEnd_1593240 := by exact prefixLift 1593240
  have htrace : WordTrace (prefixWord ++ tailWord_1593240) baseStart_1593240 baseEnd_1593240 := by
    simpa [prefixWord, tailWord_1593240, baseEnd_1593240] using wordTrace_append hprefix tailTrace_1593240
  have hstable : (prefixWord ++ tailWord_1593240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593240).length < 2 ^ (prefixWord ++ tailWord_1593240).sum := by decide
  have hdescent : baseEnd_1593240 < baseStart_1593240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593316 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1593316 : Nat := 118140960795 + 1593316 * 2 ^ 59
def prefixEnd_1593316 : Nat := 4983230072969 + 3 ^ 40 * 1593316 * 2
def baseEnd_1593316 : Nat := 272712314166397792507493

theorem tailTrace_1593316 : CollatzResearch.WordTrace tailWord_1593316 prefixEnd_1593316 272712314166397792507493 := by
  unfold tailWord_1593316
  simp only [CollatzResearch.WordTrace]
  refine ⟨29056504347847861776795901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38742005797130482369061201 29056504347847861776795901)
  ·
    refine ⟨10896189130442948166298463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29056504347847861776795901 10896189130442948166298463)
    ·
      refine ⟨16344283695664422249447695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896189130442948166298463 16344283695664422249447695)
      ·
        refine ⟨24516425543496633374171543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16344283695664422249447695 24516425543496633374171543)
        ·
          refine ⟨36774638315244950061257315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24516425543496633374171543 36774638315244950061257315)
          ·
            refine ⟨55161957472867425091885973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36774638315244950061257315 55161957472867425091885973)
            ·
              refine ⟨2585716756540660551182155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55161957472867425091885973 2585716756540660551182155)
              ·
                refine ⟨3878575134810990826773233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585716756540660551182155 3878575134810990826773233)
                ·
                  refine ⟨2908931351108243120079925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878575134810990826773233 2908931351108243120079925)
                  ·
                    refine ⟨272712314166397792507493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2908931351108243120079925 272712314166397792507493)
                    ·
                      rfl

theorem cell23_1593316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1593316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593316 prefixEnd_1593316 := by exact prefixLift 1593316
  have htrace : WordTrace (prefixWord ++ tailWord_1593316) baseStart_1593316 baseEnd_1593316 := by
    simpa [prefixWord, tailWord_1593316, baseEnd_1593316] using wordTrace_append hprefix tailTrace_1593316
  have hstable : (prefixWord ++ tailWord_1593316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593316).length < 2 ^ (prefixWord ++ tailWord_1593316).sum := by decide
  have hdescent : baseEnd_1593316 < baseStart_1593316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593326 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1593326 : Nat := 118140960795 + 1593326 * 2 ^ 59
def prefixEnd_1593326 : Nat := 4983230072969 + 3 ^ 40 * 1593326 * 2
def baseEnd_1593326 : Nat := 818142077305738338397433

theorem tailTrace_1593326 : CollatzResearch.WordTrace tailWord_1593326 prefixEnd_1593326 818142077305738338397433 := by
  unfold tailWord_1593326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264171678207436907681979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38742248950439663507637221 7264171678207436907681979)
  ·
    refine ⟨10896257517311155361522969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264171678207436907681979 10896257517311155361522969)
    ·
      refine ⟨8172193137983366521142227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10896257517311155361522969 8172193137983366521142227)
      ·
        refine ⟨12258289706975049781713341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8172193137983366521142227 12258289706975049781713341)
        ·
          refine ⟨4596858640115643668142503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12258289706975049781713341 4596858640115643668142503)
          ·
            refine ⟨6895287960173465502213755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596858640115643668142503 6895287960173465502213755)
            ·
              refine ⟨10342931940260198253320633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6895287960173465502213755 10342931940260198253320633)
              ·
                refine ⟨7757198955195148689990475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10342931940260198253320633 7757198955195148689990475)
                ·
                  refine ⟨11635798432792723034985713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757198955195148689990475 11635798432792723034985713)
                  ·
                    refine ⟨8726848824594542276239285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11635798432792723034985713 8726848824594542276239285)
                    ·
                      refine ⟨818142077305738338397433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8726848824594542276239285 818142077305738338397433)
                      ·
                        rfl

theorem cell23_1593326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1593326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593326 prefixEnd_1593326 := by exact prefixLift 1593326
  have htrace : WordTrace (prefixWord ++ tailWord_1593326) baseStart_1593326 baseEnd_1593326 := by
    simpa [prefixWord, tailWord_1593326, baseEnd_1593326] using wordTrace_append hprefix tailTrace_1593326
  have hstable : (prefixWord ++ tailWord_1593326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593326).length < 2 ^ (prefixWord ++ tailWord_1593326).sum := by decide
  have hdescent : baseEnd_1593326 < baseStart_1593326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593336 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_1593336 : Nat := 118140960795 + 1593336 * 2 ^ 59
def prefixEnd_1593336 : Nat := 4983230072969 + 3 ^ 40 * 1593336 * 2
def baseEnd_1593336 : Nat := 818147212112283299272387

theorem tailTrace_1593336 : CollatzResearch.WordTrace tailWord_1593336 prefixEnd_1593336 818147212112283299272387 := by
  unfold tailWord_1593336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29056869077811633484659931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38742492103748844646213241 29056869077811633484659931)
  ·
    refine ⟨43585303616717450226989897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29056869077811633484659931 43585303616717450226989897)
    ·
      refine ⟨32688977712538087670242423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43585303616717450226989897 32688977712538087670242423)
      ·
        refine ⟨49033466568807131505363635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32688977712538087670242423 49033466568807131505363635)
        ·
          refine ⟨73550199853210697258045453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49033466568807131505363635 73550199853210697258045453)
          ·
            refine ⟨27581324944954011471767045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73550199853210697258045453 27581324944954011471767045)
            ·
              refine ⟨5171498427178877150956321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27581324944954011471767045 5171498427178877150956321)
              ·
                refine ⟨3878623820384157863217241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171498427178877150956321 3878623820384157863217241)
                ·
                  refine ⟨2908967865288118397412931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878623820384157863217241 2908967865288118397412931)
                  ·
                    refine ⟨4363451797932177596119397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908967865288118397412931 4363451797932177596119397)
                    ·
                      refine ⟨818147212112283299272387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4363451797932177596119397 818147212112283299272387)
                      ·
                        rfl

theorem cell23_1593336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_1593336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593336 prefixEnd_1593336 := by exact prefixLift 1593336
  have htrace : WordTrace (prefixWord ++ tailWord_1593336) baseStart_1593336 baseEnd_1593336 := by
    simpa [prefixWord, tailWord_1593336, baseEnd_1593336] using wordTrace_append hprefix tailTrace_1593336
  have hstable : (prefixWord ++ tailWord_1593336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593336).length < 2 ^ (prefixWord ++ tailWord_1593336).sum := by decide
  have hdescent : baseEnd_1593336 < baseStart_1593336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593356 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1593356 : Nat := 118140960795 + 1593356 * 2 ^ 59
def prefixEnd_1593356 : Nat := 4983230072969 + 3 ^ 40 * 1593356 * 2
def baseEnd_1593356 : Nat := 818157481725373221022295

theorem tailTrace_1593356 : CollatzResearch.WordTrace tailWord_1593356 prefixEnd_1593356 818157481725373221022295 := by
  unfold tailWord_1593356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29057233807775405192523961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38742978410367206923365281 29057233807775405192523961)
  ·
    refine ⟨21792925355831553894392971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29057233807775405192523961 21792925355831553894392971)
    ·
      refine ⟨32689388033747330841589457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21792925355831553894392971 32689388033747330841589457)
      ·
        refine ⟨24517041025310498131192093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32689388033747330841589457 24517041025310498131192093)
        ·
          refine ⟨9193890384491436799197035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24517041025310498131192093 9193890384491436799197035)
          ·
            refine ⟨13790835576737155198795553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193890384491436799197035 13790835576737155198795553)
            ·
              refine ⟨10343126682552866399096665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13790835576737155198795553 10343126682552866399096665)
              ·
                refine ⟨7757345011914649799322499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10343126682552866399096665 7757345011914649799322499)
                ·
                  refine ⟨11636017517871974698983749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757345011914649799322499 11636017517871974698983749)
                  ·
                    refine ⟨2181753284600995256059453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11636017517871974698983749 2181753284600995256059453)
                    ·
                      refine ⟨818157481725373221022295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181753284600995256059453 818157481725373221022295)
                      ·
                        rfl

theorem cell23_1593356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1593356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593356 prefixEnd_1593356 := by exact prefixLift 1593356
  have htrace : WordTrace (prefixWord ++ tailWord_1593356) baseStart_1593356 baseEnd_1593356 := by
    simpa [prefixWord, tailWord_1593356, baseEnd_1593356] using wordTrace_append hprefix tailTrace_1593356
  have hstable : (prefixWord ++ tailWord_1593356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593356).length < 2 ^ (prefixWord ++ tailWord_1593356).sum := by decide
  have hdescent : baseEnd_1593356 < baseStart_1593356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593373 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1593373 : Nat := 118140960795 + 1593373 * 2 ^ 59
def prefixEnd_1593373 : Nat := 4983230072969 + 3 ^ 40 * 1593373 * 2
def baseEnd_1593373 : Nat := 818166210896499654509717

theorem tailTrace_1593373 : CollatzResearch.WordTrace tailWord_1593373 prefixEnd_1593373 818166210896499654509717 := by
  unfold tailWord_1593373
  simp only [CollatzResearch.WordTrace]
  refine ⟨58115087656489222288416773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38743391770992814858944515 58115087656489222288416773)
  ·
    refine ⟨10896578935591729179078145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58115087656489222288416773 10896578935591729179078145)
    ·
      refine ⟨8172434201693796884308609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10896578935591729179078145 8172434201693796884308609)
      ·
        refine ⟨6129325651270347663231457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8172434201693796884308609 6129325651270347663231457)
        ·
          refine ⟨4596994238452760747423593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6129325651270347663231457 4596994238452760747423593)
          ·
            refine ⟨3447745678839570560567695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596994238452760747423593 3447745678839570560567695)
            ·
              refine ⟨5171618518259355840851543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447745678839570560567695 5171618518259355840851543)
              ·
                refine ⟨7757427777389033761277315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171618518259355840851543 7757427777389033761277315)
                ·
                  refine ⟨11636141666083550641915973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757427777389033761277315 11636141666083550641915973)
                  ·
                    refine ⟨2181776562390665745359245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11636141666083550641915973 2181776562390665745359245)
                    ·
                      refine ⟨818166210896499654509717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181776562390665745359245 818166210896499654509717)
                      ·
                        rfl

theorem cell23_1593373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1593373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593373 prefixEnd_1593373 := by exact prefixLift 1593373
  have htrace : WordTrace (prefixWord ++ tailWord_1593373) baseStart_1593373 baseEnd_1593373 := by
    simpa [prefixWord, tailWord_1593373, baseEnd_1593373] using wordTrace_append hprefix tailTrace_1593373
  have hstable : (prefixWord ++ tailWord_1593373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593373).length < 2 ^ (prefixWord ++ tailWord_1593373).sum := by decide
  have hdescent : baseEnd_1593373 < baseStart_1593373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593393 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 6]
def baseStart_1593393 : Nat := 118140960795 + 1593393 * 2 ^ 59
def prefixEnd_1593393 : Nat := 4983230072969 + 3 ^ 40 * 1593393 * 2
def baseEnd_1593393 : Nat := 90908497834398841806625

theorem tailTrace_1593393 : CollatzResearch.WordTrace tailWord_1593393 prefixEnd_1593393 90908497834398841806625 := by
  unfold tailWord_1593393
  simp only [CollatzResearch.WordTrace]
  refine ⟨58115817116416765704144833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38743878077611177136096555 58115817116416765704144833)
  ·
    refine ⟨43586862837312574278108625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58115817116416765704144833 43586862837312574278108625)
    ·
      refine ⟨32690147127984430708581469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43586862837312574278108625 32690147127984430708581469)
      ·
        refine ⟨12258805172994161515718051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32690147127984430708581469 12258805172994161515718051)
        ·
          refine ⟨18388207759491242273577077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12258805172994161515718051 18388207759491242273577077)
          ·
            refine ⟨1723894477452303963147851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18388207759491242273577077 1723894477452303963147851)
            ·
              refine ⟨2585841716178455944721777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723894477452303963147851 2585841716178455944721777)
              ·
                refine ⟨1939381287133841958541333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585841716178455944721777 1939381287133841958541333)
                ·
                  refine ⟨90908497834398841806625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1939381287133841958541333 90908497834398841806625)
                  ·
                    rfl

theorem cell23_1593393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_1593393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593393 prefixEnd_1593393 := by exact prefixLift 1593393
  have htrace : WordTrace (prefixWord ++ tailWord_1593393) baseStart_1593393 baseEnd_1593393 := by
    simpa [prefixWord, tailWord_1593393, baseEnd_1593393] using wordTrace_append hprefix tailTrace_1593393
  have hstable : (prefixWord ++ tailWord_1593393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593393).length < 2 ^ (prefixWord ++ tailWord_1593393).sum := by decide
  have hdescent : baseEnd_1593393 < baseStart_1593393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593443 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1593443 : Nat := 118140960795 + 1593443 * 2 ^ 59
def prefixEnd_1593443 : Nat := 4983230072969 + 3 ^ 40 * 1593443 * 2
def baseEnd_1593443 : Nat := 818202154542314380634395

theorem tailTrace_1593443 : CollatzResearch.WordTrace tailWord_1593443 prefixEnd_1593443 818202154542314380634395 := by
  unfold tailWord_1593443
  simp only [CollatzResearch.WordTrace]
  refine ⟨58117640766235624243464983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38745093844157082828976655 58117640766235624243464983)
  ·
    refine ⟨87176461149353436365197475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58117640766235624243464983 87176461149353436365197475)
    ·
      refine ⟨130764691724030154547796213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87176461149353436365197475 130764691724030154547796213)
      ·
        refine ⟨12259189849127826988855895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130764691724030154547796213 12259189849127826988855895)
        ·
          refine ⟨18388784773691740483283843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259189849127826988855895 18388784773691740483283843)
          ·
            refine ⟨27583177160537610724925765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18388784773691740483283843 27583177160537610724925765)
            ·
              refine ⟨5171845717600802010923581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27583177160537610724925765 5171845717600802010923581)
              ·
                refine ⟨1939442144100300754096343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171845717600802010923581 1939442144100300754096343)
                ·
                  refine ⟨2909163216150451131144515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939442144100300754096343 2909163216150451131144515)
                  ·
                    refine ⟨4363744824225676696716773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909163216150451131144515 4363744824225676696716773)
                    ·
                      refine ⟨818202154542314380634395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4363744824225676696716773 818202154542314380634395)
                      ·
                        rfl

theorem cell23_1593443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1593443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593443 prefixEnd_1593443 := by exact prefixLift 1593443
  have htrace : WordTrace (prefixWord ++ tailWord_1593443) baseStart_1593443 baseEnd_1593443 := by
    simpa [prefixWord, tailWord_1593443, baseEnd_1593443] using wordTrace_append hprefix tailTrace_1593443
  have hstable : (prefixWord ++ tailWord_1593443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593443).length < 2 ^ (prefixWord ++ tailWord_1593443).sum := by decide
  have hdescent : baseEnd_1593443 < baseStart_1593443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593453 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1593453 : Nat := 118140960795 + 1593453 * 2 ^ 59
def prefixEnd_1593453 : Nat := 4983230072969 + 3 ^ 40 * 1593453 * 2
def baseEnd_1593453 : Nat := 272735763116286447169783

theorem tailTrace_1593453 : CollatzResearch.WordTrace tailWord_1593453 prefixEnd_1593453 272735763116286447169783 := by
  unfold tailWord_1593453
  simp only [CollatzResearch.WordTrace]
  refine ⟨58118005496199395951329013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38745336997466263967552675 58118005496199395951329013)
  ·
    refine ⟨5448563015268693370437095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58118005496199395951329013 5448563015268693370437095)
    ·
      refine ⟨8172844522903040055655643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448563015268693370437095 8172844522903040055655643)
      ·
        refine ⟨12259266784354560083483465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8172844522903040055655643 12259266784354560083483465)
        ·
          refine ⟨9194450088265920062612599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12259266784354560083483465 9194450088265920062612599)
          ·
            refine ⟨13791675132398880093918899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194450088265920062612599 13791675132398880093918899)
            ·
              refine ⟨20687512698598320140878349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13791675132398880093918899 20687512698598320140878349)
              ·
                refine ⟨7757817261974370052829381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20687512698598320140878349 7757817261974370052829381)
                ·
                  refine ⟨1454590736620194384905509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7757817261974370052829381 1454590736620194384905509)
                  ·
                    refine ⟨272735763116286447169783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1454590736620194384905509 272735763116286447169783)
                    ·
                      rfl

theorem cell23_1593453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1593453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593453 prefixEnd_1593453 := by exact prefixLift 1593453
  have htrace : WordTrace (prefixWord ++ tailWord_1593453) baseStart_1593453 baseEnd_1593453 := by
    simpa [prefixWord, tailWord_1593453, baseEnd_1593453] using wordTrace_append hprefix tailTrace_1593453
  have hstable : (prefixWord ++ tailWord_1593453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593453).length < 2 ^ (prefixWord ++ tailWord_1593453).sum := by decide
  have hdescent : baseEnd_1593453 < baseStart_1593453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593454 : List Nat := [4, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1593454 : Nat := 118140960795 + 1593454 * 2 ^ 59
def prefixEnd_1593454 : Nat := 4983230072969 + 3 ^ 40 * 1593454 * 2
def baseEnd_1593454 : Nat := 818207802829513837596845

theorem tailTrace_1593454 : CollatzResearch.WordTrace tailWord_1593454 prefixEnd_1593454 818207802829513837596845 := by
  unfold tailWord_1593454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264755246149471640264427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38745361312797182081410277 7264755246149471640264427)
  ·
    refine ⟨10897132869224207460396641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264755246149471640264427 10897132869224207460396641)
    ·
      refine ⟨8172849651918155595297481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10897132869224207460396641 8172849651918155595297481)
      ·
        refine ⟨6129637238938616696473111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8172849651918155595297481 6129637238938616696473111)
        ·
          refine ⟨9194455858407925044709667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6129637238938616696473111 9194455858407925044709667)
          ·
            refine ⟨13791683787611887567064501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194455858407925044709667 13791683787611887567064501)
            ·
              refine ⟨1292970355088614459412297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13791683787611887567064501 1292970355088614459412297)
              ·
                refine ⟨969727766316460844559223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292970355088614459412297 969727766316460844559223)
                ·
                  refine ⟨1454591649474691266838835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969727766316460844559223 1454591649474691266838835)
                  ·
                    refine ⟨2181887474212036900258253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1454591649474691266838835 2181887474212036900258253)
                    ·
                      refine ⟨818207802829513837596845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181887474212036900258253 818207802829513837596845)
                      ·
                        rfl

theorem cell23_1593454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1593454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593454 prefixEnd_1593454 := by exact prefixLift 1593454
  have htrace : WordTrace (prefixWord ++ tailWord_1593454) baseStart_1593454 baseEnd_1593454 := by
    simpa [prefixWord, tailWord_1593454, baseEnd_1593454] using wordTrace_append hprefix tailTrace_1593454
  have hstable : (prefixWord ++ tailWord_1593454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593454).length < 2 ^ (prefixWord ++ tailWord_1593454).sum := by decide
  have hdescent : baseEnd_1593454 < baseStart_1593454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593456 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_1593456 : Nat := 118140960795 + 1593456 * 2 ^ 59
def prefixEnd_1593456 : Nat := 4983230072969 + 3 ^ 40 * 1593456 * 2
def baseEnd_1593456 : Nat := 818208829790822829771835

theorem tailTrace_1593456 : CollatzResearch.WordTrace tailWord_1593456 prefixEnd_1593456 818208829790822829771835 := by
  unfold tailWord_1593456
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059057457594263731844111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38745409943459018309125481 29059057457594263731844111)
  ·
    refine ⟨43588586186391395597766167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29059057457594263731844111 43588586186391395597766167)
    ·
      refine ⟨65382879279587093396649251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43588586186391395597766167 65382879279587093396649251)
      ·
        refine ⟨98074318919380640094973877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65382879279587093396649251 98074318919380640094973877)
        ·
          refine ⟨9194467398691935008903801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98074318919380640094973877 9194467398691935008903801)
          ·
            refine ⟨6895850549018951256677851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9194467398691935008903801 6895850549018951256677851)
            ·
              refine ⟨10343775823528426885016777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6895850549018951256677851 10343775823528426885016777)
              ·
                refine ⟨7757831867646320163762583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10343775823528426885016777 7757831867646320163762583)
                ·
                  refine ⟨11636747801469480245643875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757831867646320163762583 11636747801469480245643875)
                  ·
                    refine ⟨17455121702204220368465813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11636747801469480245643875 17455121702204220368465813)
                    ·
                      refine ⟨818208829790822829771835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17455121702204220368465813 818208829790822829771835)
                      ·
                        rfl

theorem cell23_1593456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_1593456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593456 prefixEnd_1593456 := by exact prefixLift 1593456
  have htrace : WordTrace (prefixWord ++ tailWord_1593456) baseStart_1593456 baseEnd_1593456 := by
    simpa [prefixWord, tailWord_1593456, baseEnd_1593456] using wordTrace_append hprefix tailTrace_1593456
  have hstable : (prefixWord ++ tailWord_1593456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593456).length < 2 ^ (prefixWord ++ tailWord_1593456).sum := by decide
  have hdescent : baseEnd_1593456 < baseStart_1593456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593480 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1593480 : Nat := 118140960795 + 1593480 * 2 ^ 59
def prefixEnd_1593480 : Nat := 4983230072969 + 3 ^ 40 * 1593480 * 2
def baseEnd_1593480 : Nat := 818221153326530735871725

theorem tailTrace_1593480 : CollatzResearch.WordTrace tailWord_1593480 prefixEnd_1593480 818221153326530735871725 := by
  unfold tailWord_1593480
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059495133550789781280947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38745993511401053041707929 29059495133550789781280947)
  ·
    refine ⟨43589242700326184671921421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29059495133550789781280947 43589242700326184671921421)
    ·
      refine ⟨16345966012622319251970533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43589242700326184671921421 16345966012622319251970533)
      ·
        refine ⟨3064868627366684859744475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16345966012622319251970533 3064868627366684859744475)
        ·
          refine ⟨4597302941050027289616713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064868627366684859744475 4597302941050027289616713)
          ·
            refine ⟨3447977205787520467212535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597302941050027289616713 3447977205787520467212535)
            ·
              refine ⟨5171965808681280700818803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447977205787520467212535 5171965808681280700818803)
              ·
                refine ⟨7757948713021921051228205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171965808681280700818803 7757948713021921051228205)
                ·
                  refine ⟨2909230767383220394210577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7757948713021921051228205 2909230767383220394210577)
                  ·
                    refine ⟨2181923075537415295657933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2909230767383220394210577 2181923075537415295657933)
                    ·
                      refine ⟨818221153326530735871725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181923075537415295657933 818221153326530735871725)
                      ·
                        rfl

theorem cell23_1593480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1593480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593480 prefixEnd_1593480 := by exact prefixLift 1593480
  have htrace : WordTrace (prefixWord ++ tailWord_1593480) baseStart_1593480 baseEnd_1593480 := by
    simpa [prefixWord, tailWord_1593480, baseEnd_1593480] using wordTrace_append hprefix tailTrace_1593480
  have hstable : (prefixWord ++ tailWord_1593480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593480).length < 2 ^ (prefixWord ++ tailWord_1593480).sum := by decide
  have hdescent : baseEnd_1593480 < baseStart_1593480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593493 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_1593493 : Nat := 118140960795 + 1593493 * 2 ^ 59
def prefixEnd_1593493 : Nat := 4983230072969 + 3 ^ 40 * 1593493 * 2
def baseEnd_1593493 : Nat := 818227828575039185009165

theorem tailTrace_1593493 : CollatzResearch.WordTrace tailWord_1593493 prefixEnd_1593493 818227828575039185009165 := by
  unfold tailWord_1593493
  simp only [CollatzResearch.WordTrace]
  refine ⟨58119464416054482782785133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38746309610702988521856755 58119464416054482782785133)
  ·
    refine ⟨21794799156020431043544425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58119464416054482782785133 21794799156020431043544425)
    ·
      refine ⟨16346099367015323282658319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21794799156020431043544425 16346099367015323282658319)
      ·
        refine ⟨24519149050522984923987479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16346099367015323282658319 24519149050522984923987479)
        ·
          refine ⟨36778723575784477385981219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24519149050522984923987479 36778723575784477385981219)
          ·
            refine ⟨55168085363676716078971829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36778723575784477385981219 55168085363676716078971829)
            ·
              refine ⟨5172008002844692132403609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55168085363676716078971829 5172008002844692132403609)
              ·
                refine ⟨3879006002133519099302707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5172008002844692132403609 3879006002133519099302707)
                ·
                  refine ⟨5818509003200278648954061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879006002133519099302707 5818509003200278648954061)
                  ·
                    refine ⟨2181940876200104493357773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5818509003200278648954061 2181940876200104493357773)
                    ·
                      refine ⟨818227828575039185009165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2181940876200104493357773 818227828575039185009165)
                      ·
                        rfl

theorem cell23_1593493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_1593493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593493 prefixEnd_1593493 := by exact prefixLift 1593493
  have htrace : WordTrace (prefixWord ++ tailWord_1593493) baseStart_1593493 baseEnd_1593493 := by
    simpa [prefixWord, tailWord_1593493, baseEnd_1593493] using wordTrace_append hprefix tailTrace_1593493
  have hstable : (prefixWord ++ tailWord_1593493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593493).length < 2 ^ (prefixWord ++ tailWord_1593493).sum := by decide
  have hdescent : baseEnd_1593493 < baseStart_1593493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593511 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1593511 : Nat := 118140960795 + 1593511 * 2 ^ 59
def prefixEnd_1593511 : Nat := 4983230072969 + 3 ^ 40 * 1593511 * 2
def baseEnd_1593511 : Nat := 818237071226820114584083

theorem tailTrace_1593511 : CollatzResearch.WordTrace tailWord_1593511 prefixEnd_1593511 818237071226820114584083 := by
  unfold tailWord_1593511
  simp only [CollatzResearch.WordTrace]
  refine ⟨58120120929989271856940387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38746747286659514571293591 58120120929989271856940387)
  ·
    refine ⟨87180181394983907785410581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58120120929989271856940387 87180181394983907785410581)
    ·
      refine ⟨4086571002889870677441121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87180181394983907785410581 4086571002889870677441121)
      ·
        refine ⟨3064928252167403008080841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4086571002889870677441121 3064928252167403008080841)
        ·
          refine ⟨2298696189125552256060631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064928252167403008080841 2298696189125552256060631)
          ·
            refine ⟨3448044283688328384090947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298696189125552256060631 3448044283688328384090947)
            ·
              refine ⟨5172066425532492576136421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448044283688328384090947 5172066425532492576136421)
              ·
                refine ⟨969762454787342358025579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5172066425532492576136421 969762454787342358025579)
                ·
                  refine ⟨1454643682181013537038369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969762454787342358025579 1454643682181013537038369)
                  ·
                    refine ⟨1090982761635760152778777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1454643682181013537038369 1090982761635760152778777)
                    ·
                      refine ⟨818237071226820114584083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1090982761635760152778777 818237071226820114584083)
                      ·
                        rfl

theorem cell23_1593511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1593511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593511 prefixEnd_1593511 := by exact prefixLift 1593511
  have htrace : WordTrace (prefixWord ++ tailWord_1593511) baseStart_1593511 baseEnd_1593511 := by
    simpa [prefixWord, tailWord_1593511, baseEnd_1593511] using wordTrace_append hprefix tailTrace_1593511
  have hstable : (prefixWord ++ tailWord_1593511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593511).length < 2 ^ (prefixWord ++ tailWord_1593511).sum := by decide
  have hdescent : baseEnd_1593511 < baseStart_1593511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593554 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1593554 : Nat := 118140960795 + 1593554 * 2 ^ 59
def prefixEnd_1593554 : Nat := 4983230072969 + 3 ^ 40 * 1593554 * 2
def baseEnd_1593554 : Nat := 818259150894963446346385

theorem tailTrace_1593554 : CollatzResearch.WordTrace tailWord_1593554 prefixEnd_1593554 818259150894963446346385 := by
  unfold tailWord_1593554
  simp only [CollatzResearch.WordTrace]
  refine ⟨14530422317208372550188929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38747792845888993467170477 14530422317208372550188929)
  ·
    refine ⟨10897816737906279412641697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14530422317208372550188929 10897816737906279412641697)
    ·
      refine ⟨8173362553429709559481273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10897816737906279412641697 8173362553429709559481273)
      ·
        refine ⟨6130021915072282169610955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8173362553429709559481273 6130021915072282169610955)
        ·
          refine ⟨9195032872608423254416433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130021915072282169610955 9195032872608423254416433)
          ·
            refine ⟨6896274654456317440812325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9195032872608423254416433 6896274654456317440812325)
            ·
              refine ⟨1293051497710559520152311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6896274654456317440812325 1293051497710559520152311)
              ·
                refine ⟨1939577246565839280228467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293051497710559520152311 1939577246565839280228467)
                ·
                  refine ⟨2909365869848758920342701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939577246565839280228467 2909365869848758920342701)
                  ·
                    refine ⟨1091012201193284595128513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909365869848758920342701 1091012201193284595128513)
                    ·
                      refine ⟨818259150894963446346385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091012201193284595128513 818259150894963446346385)
                      ·
                        rfl

theorem cell23_1593554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1593554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593554 prefixEnd_1593554 := by exact prefixLift 1593554
  have htrace : WordTrace (prefixWord ++ tailWord_1593554) baseStart_1593554 baseEnd_1593554 := by
    simpa [prefixWord, tailWord_1593554, baseEnd_1593554] using wordTrace_append hprefix tailTrace_1593554
  have hstable : (prefixWord ++ tailWord_1593554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593554).length < 2 ^ (prefixWord ++ tailWord_1593554).sum := by decide
  have hdescent : baseEnd_1593554 < baseStart_1593554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593573 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 7]
def baseStart_1593573 : Nat := 118140960795 + 1593573 * 2 ^ 59
def prefixEnd_1593573 : Nat := 4983230072969 + 3 ^ 40 * 1593573 * 2
def baseEnd_1593573 : Nat := 90918767447488763556533

theorem tailTrace_1593573 : CollatzResearch.WordTrace tailWord_1593573 prefixEnd_1593573 90918767447488763556533 := by
  unfold tailWord_1593573
  simp only [CollatzResearch.WordTrace]
  refine ⟨58122382255764656445697373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38748254837176437630464915 58122382255764656445697373)
  ·
    refine ⟨21795893345911746167136515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58122382255764656445697373 21795893345911746167136515)
    ·
      refine ⟨32693840018867619250704773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21795893345911746167136515 32693840018867619250704773)
      ·
        refine ⟨6130095003537678609507145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32693840018867619250704773 6130095003537678609507145)
        ·
          refine ⟨4597571252653258957130359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6130095003537678609507145 4597571252653258957130359)
          ·
            refine ⟨6896356878979888435695539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597571252653258957130359 6896356878979888435695539)
            ·
              refine ⟨10344535318469832653543309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896356878979888435695539 10344535318469832653543309)
              ·
                refine ⟨3879200744426187245078741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10344535318469832653543309 3879200744426187245078741)
                ·
                  refine ⟨90918767447488763556533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3879200744426187245078741 90918767447488763556533)
                  ·
                    rfl

theorem cell23_1593573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_1593573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593573 prefixEnd_1593573 := by exact prefixLift 1593573
  have htrace : WordTrace (prefixWord ++ tailWord_1593573) baseStart_1593573 baseEnd_1593573 := by
    simpa [prefixWord, tailWord_1593573, baseEnd_1593573] using wordTrace_append hprefix tailTrace_1593573
  have hstable : (prefixWord ++ tailWord_1593573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593573).length < 2 ^ (prefixWord ++ tailWord_1593573).sum := by decide
  have hdescent : baseEnd_1593573 < baseStart_1593573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593603 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 2, 5]
def baseStart_1593603 : Nat := 118140960795 + 1593603 * 2 ^ 59
def prefixEnd_1593603 : Nat := 4983230072969 + 3 ^ 40 * 1593603 * 2
def baseEnd_1593603 : Nat := 272761437149011251544553

theorem tailTrace_1593603 : CollatzResearch.WordTrace tailWord_1593603 prefixEnd_1593603 272761437149011251544553 := by
  unfold tailWord_1593603
  simp only [CollatzResearch.WordTrace]
  refine ⟨58123476445655971569289463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38748984297103981046192975 58123476445655971569289463)
  ·
    refine ⟨87185214668483957353934195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58123476445655971569289463 87185214668483957353934195)
    ·
      refine ⟨130777822002725936030901293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87185214668483957353934195 130777822002725936030901293)
      ·
        refine ⟨49041683251022226011587985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130777822002725936030901293 49041683251022226011587985)
        ·
          refine ⟨36781262438266669508690989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49041683251022226011587985 36781262438266669508690989)
          ·
            refine ⟨13792973414350001065759121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36781262438266669508690989 13792973414350001065759121)
            ·
              refine ⟨10344730060762500799319341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13792973414350001065759121 10344730060762500799319341)
              ·
                refine ⟨3879273772785937799744753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10344730060762500799319341 3879273772785937799744753)
                ·
                  refine ⟨2909455329589453349808565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879273772785937799744753 2909455329589453349808565)
                  ·
                    refine ⟨272761437149011251544553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2909455329589453349808565 272761437149011251544553)
                    ·
                      rfl

theorem cell23_1593603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 5].length) (baseStart_1593603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593603 prefixEnd_1593603 := by exact prefixLift 1593603
  have htrace : WordTrace (prefixWord ++ tailWord_1593603) baseStart_1593603 baseEnd_1593603 := by
    simpa [prefixWord, tailWord_1593603, baseEnd_1593603] using wordTrace_append hprefix tailTrace_1593603
  have hstable : (prefixWord ++ tailWord_1593603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593603).length < 2 ^ (prefixWord ++ tailWord_1593603).sum := by decide
  have hdescent : baseEnd_1593603 < baseStart_1593603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593657 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1593657 : Nat := 118140960795 + 1593657 * 2 ^ 59
def prefixEnd_1593657 : Nat := 4983230072969 + 3 ^ 40 * 1593657 * 2
def baseEnd_1593657 : Nat := 818312039402376543358411

theorem tailTrace_1593657 : CollatzResearch.WordTrace tailWord_1593657 prefixEnd_1593657 818312039402376543358411 := by
  unfold tailWord_1593657
  simp only [CollatzResearch.WordTrace]
  refine ⟨58125445987460338791755225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38750297324973559194503483 58125445987460338791755225)
  ·
    refine ⟨43594084490595254093816419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58125445987460338791755225 43594084490595254093816419)
    ·
      refine ⟨65391126735892881140724629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43594084490595254093816419 65391126735892881140724629)
      ·
        refine ⟨3065209065744978803471467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65391126735892881140724629 3065209065744978803471467)
        ·
          refine ⟨4597813598617468205207201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065209065744978803471467 4597813598617468205207201)
          ·
            refine ⟨3448360198963101153905401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597813598617468205207201 3448360198963101153905401)
            ·
              refine ⟨2586270149222325865429051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448360198963101153905401 2586270149222325865429051)
              ·
                refine ⟨3879405223833488798143577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586270149222325865429051 3879405223833488798143577)
                ·
                  refine ⟨2909553917875116598607683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879405223833488798143577 2909553917875116598607683)
                  ·
                    refine ⟨4364330876812674897911525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909553917875116598607683 4364330876812674897911525)
                    ·
                      refine ⟨818312039402376543358411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4364330876812674897911525 818312039402376543358411)
                      ·
                        rfl

theorem cell23_1593657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1593657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593657 prefixEnd_1593657 := by exact prefixLift 1593657
  have htrace : WordTrace (prefixWord ++ tailWord_1593657) baseStart_1593657 baseEnd_1593657 := by
    simpa [prefixWord, tailWord_1593657, baseEnd_1593657] using wordTrace_append hprefix tailTrace_1593657
  have hstable : (prefixWord ++ tailWord_1593657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593657).length < 2 ^ (prefixWord ++ tailWord_1593657).sum := by decide
  have hdescent : baseEnd_1593657 < baseStart_1593657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593680 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 6]
def baseStart_1593680 : Nat := 118140960795 + 1593680 * 2 ^ 59
def prefixEnd_1593680 : Nat := 4983230072969 + 3 ^ 40 * 1593680 * 2
def baseEnd_1593680 : Nat := 90924872161936661485645

theorem tailTrace_1593680 : CollatzResearch.WordTrace tailWord_1593680 prefixEnd_1593680 90924872161936661485645 := by
  unfold tailWord_1593680
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063142433188506859921247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38750856577584675813228329 29063142433188506859921247)
  ·
    refine ⟨43594713649782760289881871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29063142433188506859921247 43594713649782760289881871)
    ·
      refine ⟨65392070474674140434822807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43594713649782760289881871 65392070474674140434822807)
      ·
        refine ⟨98088105712011210652234211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65392070474674140434822807 98088105712011210652234211)
        ·
          refine ⟨147132158568016815978351317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98088105712011210652234211 147132158568016815978351317)
          ·
            refine ⟨3448409966437894124492609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147132158568016815978351317 3448409966437894124492609)
            ·
              refine ⟨2586307474828420593369457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448409966437894124492609 2586307474828420593369457)
              ·
                refine ⟨1939730606121315445027093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586307474828420593369457 1939730606121315445027093)
                ·
                  refine ⟨90924872161936661485645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1939730606121315445027093 90924872161936661485645)
                  ·
                    rfl

theorem cell23_1593680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_1593680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593680 prefixEnd_1593680 := by exact prefixLift 1593680
  have htrace : WordTrace (prefixWord ++ tailWord_1593680) baseStart_1593680 baseEnd_1593680 := by
    simpa [prefixWord, tailWord_1593680, baseEnd_1593680] using wordTrace_append hprefix tailTrace_1593680
  have hstable : (prefixWord ++ tailWord_1593680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593680).length < 2 ^ (prefixWord ++ tailWord_1593680).sum := by decide
  have hdescent : baseEnd_1593680 < baseStart_1593680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593684 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_1593684 : Nat := 118140960795 + 1593684 * 2 ^ 59
def prefixEnd_1593684 : Nat := 4983230072969 + 3 ^ 40 * 1593684 * 2
def baseEnd_1593684 : Nat := 272775301126682645906929

theorem tailTrace_1593684 : CollatzResearch.WordTrace tailWord_1593684 prefixEnd_1593684 272775301126682645906929 := by
  unfold tailWord_1593684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063215379181261201494053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38750953838908348268658737 29063215379181261201494053)
  ·
    refine ⟨5449352883596486475280135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29063215379181261201494053 5449352883596486475280135)
    ·
      refine ⟨8174029325394729712920203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5449352883596486475280135 8174029325394729712920203)
      ·
        refine ⟨12261043988092094569380305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174029325394729712920203 12261043988092094569380305)
        ·
          refine ⟨9195782991069070927035229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12261043988092094569380305 9195782991069070927035229)
          ·
            refine ⟨3448418621650901597638211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9195782991069070927035229 3448418621650901597638211)
            ·
              refine ⟨5172627932476352396457317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448418621650901597638211 5172627932476352396457317)
              ·
                refine ⟨969867737339316074335747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5172627932476352396457317 969867737339316074335747)
                ·
                  refine ⟨1454801606008974111503621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969867737339316074335747 1454801606008974111503621)
                  ·
                    refine ⟨272775301126682645906929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1454801606008974111503621 272775301126682645906929)
                    ·
                      rfl

theorem cell23_1593684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_1593684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593684 prefixEnd_1593684 := by exact prefixLift 1593684
  have htrace : WordTrace (prefixWord ++ tailWord_1593684) baseStart_1593684 baseEnd_1593684 := by
    simpa [prefixWord, tailWord_1593684, baseEnd_1593684] using wordTrace_append hprefix tailTrace_1593684
  have hstable : (prefixWord ++ tailWord_1593684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593684).length < 2 ^ (prefixWord ++ tailWord_1593684).sum := by decide
  have hdescent : baseEnd_1593684 < baseStart_1593684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593718 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1593718 : Nat := 118140960795 + 1593718 * 2 ^ 59
def prefixEnd_1593718 : Nat := 4983230072969 + 3 ^ 40 * 1593718 * 2
def baseEnd_1593718 : Nat := 272781120574100268231877

theorem tailTrace_1593718 : CollatzResearch.WordTrace tailWord_1593718 prefixEnd_1593718 272781120574100268231877 := by
  unfold tailWord_1593718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632979427514959138107863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38751780560159564139817205 3632979427514959138107863)
  ·
    refine ⟨5449469141272438707161795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632979427514959138107863 5449469141272438707161795)
    ·
      refine ⟨8174203711908658060742693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5449469141272438707161795 8174203711908658060742693)
      ·
        refine ⟨1532663195982873386389255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8174203711908658060742693 1532663195982873386389255)
        ·
          refine ⟨2298994793974310079583883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532663195982873386389255 2298994793974310079583883)
          ·
            refine ⟨3448492190961465119375825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298994793974310079583883 3448492190961465119375825)
            ·
              refine ⟨2586369143221098839531869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448492190961465119375825 2586369143221098839531869)
              ·
                refine ⟨969888428707912064824451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586369143221098839531869 969888428707912064824451)
                ·
                  refine ⟨1454832643061868097236677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969888428707912064824451 1454832643061868097236677)
                  ·
                    refine ⟨272781120574100268231877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1454832643061868097236677 272781120574100268231877)
                    ·
                      rfl

theorem cell23_1593718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1593718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593718 prefixEnd_1593718 := by exact prefixLift 1593718
  have htrace : WordTrace (prefixWord ++ tailWord_1593718) baseStart_1593718 baseEnd_1593718 := by
    simpa [prefixWord, tailWord_1593718, baseEnd_1593718] using wordTrace_append hprefix tailTrace_1593718
  have hstable : (prefixWord ++ tailWord_1593718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593718).length < 2 ^ (prefixWord ++ tailWord_1593718).sum := by decide
  have hdescent : baseEnd_1593718 < baseStart_1593718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593753 : List Nat := [1, 2, 1, 2, 1, 4, 2, 10]
def baseStart_1593753 : Nat := 118140960795 + 1593753 * 2 ^ 59
def prefixEnd_1593753 : Nat := 4983230072969 + 3 ^ 40 * 1593753 * 2
def baseEnd_1593753 : Nat := 30309679020192895102147

theorem tailTrace_1593753 : CollatzResearch.WordTrace tailWord_1593753 prefixEnd_1593753 30309679020192895102147 := by
  unfold tailWord_1593753
  simp only [CollatzResearch.WordTrace]
  refine ⟨58128947395112547187249913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38752631596741698124833275 58128947395112547187249913)
  ·
    refine ⟨43596710546334410390437435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58128947395112547187249913 43596710546334410390437435)
    ·
      refine ⟨65395065819501615585656153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43596710546334410390437435 65395065819501615585656153)
      ·
        refine ⟨49046299364626211689242115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65395065819501615585656153 49046299364626211689242115)
        ·
          refine ⟨73569449046939317533863173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49046299364626211689242115 73569449046939317533863173)
          ·
            refine ⟨13794271696301122037599345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73569449046939317533863173 13794271696301122037599345)
            ·
              refine ⟨10345703772225841528199509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13794271696301122037599345 10345703772225841528199509)
              ·
                refine ⟨30309679020192895102147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10345703772225841528199509 30309679020192895102147)
                ·
                  rfl

theorem cell23_1593753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 10].length) (baseStart_1593753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593753 prefixEnd_1593753 := by exact prefixLift 1593753
  have htrace : WordTrace (prefixWord ++ tailWord_1593753) baseStart_1593753 baseEnd_1593753 := by
    simpa [prefixWord, tailWord_1593753, baseEnd_1593753] using wordTrace_append hprefix tailTrace_1593753
  have hstable : (prefixWord ++ tailWord_1593753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593753).length < 2 ^ (prefixWord ++ tailWord_1593753).sum := by decide
  have hdescent : baseEnd_1593753 < baseStart_1593753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593760 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1593760 : Nat := 118140960795 + 1593760 * 2 ^ 59
def prefixEnd_1593760 : Nat := 4983230072969 + 3 ^ 40 * 1593760 * 2
def baseEnd_1593760 : Nat := 818364927909789640370437

theorem tailTrace_1593760 : CollatzResearch.WordTrace tailWord_1593760 prefixEnd_1593760 818364927909789640370437 := by
  unfold tailWord_1593760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29064601353043593691377367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38752801804058124921836489 29064601353043593691377367)
  ·
    refine ⟨43596902029565390537066051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29064601353043593691377367 43596902029565390537066051)
    ·
      refine ⟨65395353044348085805599077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43596902029565390537066051 65395353044348085805599077)
      ·
        refine ⟨12261628695815266088549827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65395353044348085805599077 12261628695815266088549827)
        ·
          refine ⟨18392443043722899132824741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12261628695815266088549827 18392443043722899132824741)
          ·
            refine ⟨3448583070698043587404639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18392443043722899132824741 3448583070698043587404639)
            ·
              refine ⟨5172874606047065381106959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448583070698043587404639 5172874606047065381106959)
              ·
                refine ⟨7759311909070598071660439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172874606047065381106959 7759311909070598071660439)
                ·
                  refine ⟨11638967863605897107490659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759311909070598071660439 11638967863605897107490659)
                  ·
                    refine ⟨17458451795408845661235989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11638967863605897107490659 17458451795408845661235989)
                    ·
                      refine ⟨818364927909789640370437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17458451795408845661235989 818364927909789640370437)
                      ·
                        rfl

theorem cell23_1593760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1593760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593760 prefixEnd_1593760 := by exact prefixLift 1593760
  have htrace : WordTrace (prefixWord ++ tailWord_1593760) baseStart_1593760 baseEnd_1593760 := by
    simpa [prefixWord, tailWord_1593760, baseEnd_1593760] using wordTrace_append hprefix tailTrace_1593760
  have hstable : (prefixWord ++ tailWord_1593760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593760).length < 2 ^ (prefixWord ++ tailWord_1593760).sum := by decide
  have hdescent : baseEnd_1593760 < baseStart_1593760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593764 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_1593764 : Nat := 118140960795 + 1593764 * 2 ^ 59
def prefixEnd_1593764 : Nat := 4983230072969 + 3 ^ 40 * 1593764 * 2
def baseEnd_1593764 : Nat := 818366981832407624720419

theorem tailTrace_1593764 : CollatzResearch.WordTrace tailWord_1593764 prefixEnd_1593764 818366981832407624720419 := by
  unfold tailWord_1593764
  simp only [CollatzResearch.WordTrace]
  refine ⟨29064674299036348032950173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38752899065381797377266897 29064674299036348032950173)
  ·
    refine ⟨10899252862138630512356315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29064674299036348032950173 10899252862138630512356315)
    ·
      refine ⟨16348879293207945768534473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10899252862138630512356315 16348879293207945768534473)
      ·
        refine ⟨12261659469905959326400855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16348879293207945768534473 12261659469905959326400855)
        ·
          refine ⟨18392489204858938989601283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12261659469905959326400855 18392489204858938989601283)
          ·
            refine ⟨27588733807288408484401925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18392489204858938989601283 27588733807288408484401925)
            ·
              refine ⟨5172887588866576590825361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27588733807288408484401925 5172887588866576590825361)
              ·
                refine ⟨3879665691649932443119021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5172887588866576590825361 3879665691649932443119021)
                ·
                  refine ⟨1454874634368724666169633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3879665691649932443119021 1454874634368724666169633)
                  ·
                    refine ⟨1091155975776543499627225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1454874634368724666169633 1091155975776543499627225)
                    ·
                      refine ⟨818366981832407624720419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091155975776543499627225 818366981832407624720419)
                      ·
                        rfl

theorem cell23_1593764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_1593764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593764 prefixEnd_1593764 := by exact prefixLift 1593764
  have htrace : WordTrace (prefixWord ++ tailWord_1593764) baseStart_1593764 baseEnd_1593764 := by
    simpa [prefixWord, tailWord_1593764, baseEnd_1593764] using wordTrace_append hprefix tailTrace_1593764
  have hstable : (prefixWord ++ tailWord_1593764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593764).length < 2 ^ (prefixWord ++ tailWord_1593764).sum := by decide
  have hdescent : baseEnd_1593764 < baseStart_1593764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593807 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 3, 3, 2]
def baseStart_1593807 : Nat := 118140960795 + 1593807 * 2 ^ 59
def prefixEnd_1593807 : Nat := 4983230072969 + 3 ^ 40 * 1593807 * 2
def baseEnd_1593807 : Nat := 818389061500550956482721

theorem tailTrace_1593807 : CollatzResearch.WordTrace tailWord_1593807 prefixEnd_1593807 818389061500550956482721 := by
  unfold tailWord_1593807
  simp only [CollatzResearch.WordTrace]
  refine ⟨58130916936916914409715675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38753944624611276273143783 58130916936916914409715675)
  ·
    refine ⟨87196375405375371614573513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58130916936916914409715675 87196375405375371614573513)
    ·
      refine ⟨65397281554031528710930135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87196375405375371614573513 65397281554031528710930135)
      ·
        refine ⟨98095922331047293066395203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65397281554031528710930135 98095922331047293066395203)
        ·
          refine ⟨147143883496570939599592805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98095922331047293066395203 147143883496570939599592805)
          ·
            refine ⟨27589478155607051174923651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147143883496570939599592805 27589478155607051174923651)
            ·
              refine ⟨41384217233410576762385477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27589478155607051174923651 41384217233410576762385477)
              ·
                refine ⟨7759540731264483142947277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41384217233410576762385477 7759540731264483142947277)
                ·
                  refine ⟨2909827774224181178605229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7759540731264483142947277 2909827774224181178605229)
                  ·
                    refine ⟨1091185415334067941976961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909827774224181178605229 1091185415334067941976961)
                    ·
                      refine ⟨818389061500550956482721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091185415334067941976961 818389061500550956482721)
                      ·
                        rfl

theorem cell23_1593807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3, 2].length) (baseStart_1593807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593807 prefixEnd_1593807 := by exact prefixLift 1593807
  have htrace : WordTrace (prefixWord ++ tailWord_1593807) baseStart_1593807 baseEnd_1593807 := by
    simpa [prefixWord, tailWord_1593807, baseEnd_1593807] using wordTrace_append hprefix tailTrace_1593807
  have hstable : (prefixWord ++ tailWord_1593807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593807).length < 2 ^ (prefixWord ++ tailWord_1593807).sum := by decide
  have hdescent : baseEnd_1593807 < baseStart_1593807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593814 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1593814 : Nat := 118140960795 + 1593814 * 2 ^ 59
def prefixEnd_1593814 : Nat := 4983230072969 + 3 ^ 40 * 1593814 * 2
def baseEnd_1593814 : Nat := 818392655865132429095189

theorem tailTrace_1593814 : CollatzResearch.WordTrace tailWord_1593814 prefixEnd_1593814 818392655865132429095189 := by
  unfold tailWord_1593814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633198265493222162826281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38754114831927703070146997 3633198265493222162826281)
  ·
    refine ⟨2724898699119916622119711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3633198265493222162826281 2724898699119916622119711)
    ·
      refine ⟨4087348048679874933179567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724898699119916622119711 4087348048679874933179567)
      ·
        refine ⟨6131022073019812399769351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087348048679874933179567 6131022073019812399769351)
        ·
          refine ⟨9196533109529718599654027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131022073019812399769351 9196533109529718599654027)
          ·
            refine ⟨13794799664294577899481041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196533109529718599654027 13794799664294577899481041)
            ·
              refine ⟨10346099748220933424610781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13794799664294577899481041 10346099748220933424610781)
              ·
                refine ⟨3879787405582850034229043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10346099748220933424610781 3879787405582850034229043)
                ·
                  refine ⟨5819681108374275051343565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879787405582850034229043 5819681108374275051343565)
                  ·
                    refine ⟨2182380415640353144253837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5819681108374275051343565 2182380415640353144253837)
                    ·
                      refine ⟨818392655865132429095189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2182380415640353144253837 818392655865132429095189)
                      ·
                        rfl

theorem cell23_1593814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1593814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593814 prefixEnd_1593814 := by exact prefixLift 1593814
  have htrace : WordTrace (prefixWord ++ tailWord_1593814) baseStart_1593814 baseEnd_1593814 := by
    simpa [prefixWord, tailWord_1593814, baseEnd_1593814] using wordTrace_append hprefix tailTrace_1593814
  have hstable : (prefixWord ++ tailWord_1593814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593814).length < 2 ^ (prefixWord ++ tailWord_1593814).sum := by decide
  have hdescent : baseEnd_1593814 < baseStart_1593814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593840 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_1593840 : Nat := 118140960795 + 1593840 * 2 ^ 59
def prefixEnd_1593840 : Nat := 4983230072969 + 3 ^ 40 * 1593840 * 2
def baseEnd_1593840 : Nat := 818406006362149327370069

theorem tailTrace_1593840 : CollatzResearch.WordTrace tailWord_1593840 prefixEnd_1593840 818406006362149327370069 := by
  unfold tailWord_1593840
  simp only [CollatzResearch.WordTrace]
  refine ⟨29066060272898680522833487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38754747030531574030444649 29066060272898680522833487)
  ·
    refine ⟨43599090409348020784250231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29066060272898680522833487 43599090409348020784250231)
    ·
      refine ⟨65398635614022031176375347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43599090409348020784250231 65398635614022031176375347)
      ·
        refine ⟨98097953421033046764563021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65398635614022031176375347 98097953421033046764563021)
        ·
          refine ⟨36786732532887392536711133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98097953421033046764563021 36786732532887392536711133)
          ·
            refine ⟨13795024699832772201266675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36786732532887392536711133 13795024699832772201266675)
            ·
              refine ⟨20692537049749158301900013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13795024699832772201266675 20692537049749158301900013)
              ·
                refine ⟨7759701393655934363212505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20692537049749158301900013 7759701393655934363212505)
                ·
                  refine ⟨5819776045241950772409379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7759701393655934363212505 5819776045241950772409379)
                  ·
                    refine ⟨8729664067862926158614069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5819776045241950772409379 8729664067862926158614069)
                    ·
                      refine ⟨818406006362149327370069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8729664067862926158614069 818406006362149327370069)
                      ·
                        rfl

theorem cell23_1593840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_1593840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593840 prefixEnd_1593840 := by exact prefixLift 1593840
  have htrace : WordTrace (prefixWord ++ tailWord_1593840) baseStart_1593840 baseEnd_1593840 := by
    simpa [prefixWord, tailWord_1593840, baseEnd_1593840] using wordTrace_append hprefix tailTrace_1593840
  have hstable : (prefixWord ++ tailWord_1593840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593840).length < 2 ^ (prefixWord ++ tailWord_1593840).sum := by decide
  have hdescent : baseEnd_1593840 < baseStart_1593840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593841 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_1593841 : Nat := 118140960795 + 1593841 * 2 ^ 59
def prefixEnd_1593841 : Nat := 4983230072969 + 3 ^ 40 * 1593841 * 2
def baseEnd_1593841 : Nat := 818406519842803823457565

theorem tailTrace_1593841 : CollatzResearch.WordTrace tailWord_1593841 prefixEnd_1593841 818406519842803823457565 := by
  unfold tailWord_1593841
  simp only [CollatzResearch.WordTrace]
  refine ⟨58132157018793738216453377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38754771345862492144302251 58132157018793738216453377)
  ·
    refine ⟨43599117764095303662340033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58132157018793738216453377 43599117764095303662340033)
    ·
      refine ⟨32699338323071477746755025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43599117764095303662340033 32699338323071477746755025)
      ·
        refine ⟨24524503742303608310066269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32699338323071477746755025 24524503742303608310066269)
        ·
          refine ⟨9196688903363853116274851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24524503742303608310066269 9196688903363853116274851)
          ·
            refine ⟨13795033355045779674412277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196688903363853116274851 13795033355045779674412277)
            ·
              refine ⟨1293284377035541844476151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13795033355045779674412277 1293284377035541844476151)
              ·
                refine ⟨1939926565553312766714227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293284377035541844476151 1939926565553312766714227)
                ·
                  refine ⟨2909889848329969150071341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939926565553312766714227 2909889848329969150071341)
                  ·
                    refine ⟨1091208693123738431276753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909889848329969150071341 1091208693123738431276753)
                    ·
                      refine ⟨818406519842803823457565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091208693123738431276753 818406519842803823457565)
                      ·
                        rfl

theorem cell23_1593841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_1593841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593841 prefixEnd_1593841 := by exact prefixLift 1593841
  have htrace : WordTrace (prefixWord ++ tailWord_1593841) baseStart_1593841 baseEnd_1593841 := by
    simpa [prefixWord, tailWord_1593841, baseEnd_1593841] using wordTrace_append hprefix tailTrace_1593841
  have hstable : (prefixWord ++ tailWord_1593841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593841).length < 2 ^ (prefixWord ++ tailWord_1593841).sum := by decide
  have hdescent : baseEnd_1593841 < baseStart_1593841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593857 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1593857 : Nat := 118140960795 + 1593857 * 2 ^ 59
def prefixEnd_1593857 : Nat := 4983230072969 + 3 ^ 40 * 1593857 * 2
def baseEnd_1593857 : Nat := 818414735533275760857491

theorem tailTrace_1593857 : CollatzResearch.WordTrace tailWord_1593857 prefixEnd_1593857 818414735533275760857491 := by
  unfold tailWord_1593857
  simp only [CollatzResearch.WordTrace]
  refine ⟨58132740586735772949035825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38755160391157181966023883 58132740586735772949035825)
  ·
    refine ⟨43599555440051829711776869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58132740586735772949035825 43599555440051829711776869)
    ·
      refine ⟨8174916645009718070958163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43599555440051829711776869 8174916645009718070958163)
      ·
        refine ⟨12262374967514577106437245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174916645009718070958163 12262374967514577106437245)
        ·
          refine ⟨4598390612817966414913967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12262374967514577106437245 4598390612817966414913967)
          ·
            refine ⟨6897585919226949622370951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598390612817966414913967 6897585919226949622370951)
            ·
              refine ⟨10346378878840424433556427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897585919226949622370951 10346378878840424433556427)
              ·
                refine ⟨15519568318260636650334641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346378878840424433556427 15519568318260636650334641)
                ·
                  refine ⟨11639676238695477487750981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15519568318260636650334641 11639676238695477487750981)
                  ·
                    refine ⟨2182439294755402028953309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11639676238695477487750981 2182439294755402028953309)
                    ·
                      refine ⟨818414735533275760857491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2182439294755402028953309 818414735533275760857491)
                      ·
                        rfl

theorem cell23_1593857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1593857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593857 prefixEnd_1593857 := by exact prefixLift 1593857
  have htrace : WordTrace (prefixWord ++ tailWord_1593857) baseStart_1593857 baseEnd_1593857 := by
    simpa [prefixWord, tailWord_1593857, baseEnd_1593857] using wordTrace_append hprefix tailTrace_1593857
  have hstable : (prefixWord ++ tailWord_1593857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593857).length < 2 ^ (prefixWord ++ tailWord_1593857).sum := by decide
  have hdescent : baseEnd_1593857 < baseStart_1593857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593867 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4]
def baseStart_1593867 : Nat := 118140960795 + 1593867 * 2 ^ 59
def prefixEnd_1593867 : Nat := 4983230072969 + 3 ^ 40 * 1593867 * 2
def baseEnd_1593867 : Nat := 818419870339820721732445

theorem tailTrace_1593867 : CollatzResearch.WordTrace tailWord_1593867 prefixEnd_1593867 818419870339820721732445 := by
  unfold tailWord_1593867
  simp only [CollatzResearch.WordTrace]
  refine ⟨58133105316699544656899855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38755403544466363104599903 58133105316699544656899855)
  ·
    refine ⟨87199657975049316985349783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58133105316699544656899855 87199657975049316985349783)
    ·
      refine ⟨130799486962573975478024675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87199657975049316985349783 130799486962573975478024675)
      ·
        refine ⟨196199230443860963217037013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130799486962573975478024675 196199230443860963217037013)
        ·
          refine ⟨4598419463527991325399305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 196199230443860963217037013 4598419463527991325399305)
          ·
            refine ⟨3448814597645993494049479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4598419463527991325399305 3448814597645993494049479)
            ·
              refine ⟨5173221896468990241074219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448814597645993494049479 5173221896468990241074219)
              ·
                refine ⟨7759832844703485361611329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173221896468990241074219 7759832844703485361611329)
                ·
                  refine ⟨5819874633527614021208497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7759832844703485361611329 5819874633527614021208497)
                  ·
                    refine ⟨4364905975145710515906373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5819874633527614021208497 4364905975145710515906373)
                    ·
                      refine ⟨818419870339820721732445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4364905975145710515906373 818419870339820721732445)
                      ·
                        rfl

theorem cell23_1593867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_1593867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593867 prefixEnd_1593867 := by exact prefixLift 1593867
  have htrace : WordTrace (prefixWord ++ tailWord_1593867) baseStart_1593867 baseEnd_1593867 := by
    simpa [prefixWord, tailWord_1593867, baseEnd_1593867] using wordTrace_append hprefix tailTrace_1593867
  have hstable : (prefixWord ++ tailWord_1593867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593867).length < 2 ^ (prefixWord ++ tailWord_1593867).sum := by decide
  have hdescent : baseEnd_1593867 < baseStart_1593867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593892 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1593892 : Nat := 118140960795 + 1593892 * 2 ^ 59
def prefixEnd_1593892 : Nat := 4983230072969 + 3 ^ 40 * 1593892 * 2
def baseEnd_1593892 : Nat := 818432707356183123919831

theorem tailTrace_1593892 : CollatzResearch.WordTrace tailWord_1593892 prefixEnd_1593892 818432707356183123919831 := by
  unfold tailWord_1593892
  simp only [CollatzResearch.WordTrace]
  refine ⟨29067008570804486963279965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38756011427739315951039953 29067008570804486963279965)
  ·
    refine ⟨10900128214051682611229987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29067008570804486963279965 10900128214051682611229987)
    ·
      refine ⟨16350192321077523916844981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900128214051682611229987 16350192321077523916844981)
      ·
        refine ⟨1532830530101017867204217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16350192321077523916844981 1532830530101017867204217)
        ·
          refine ⟨1149622897575763400403163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532830530101017867204217 1149622897575763400403163)
          ·
            refine ⟨1724434346363645100604745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149622897575763400403163 1724434346363645100604745)
            ·
              refine ⟨1293325759772733825453559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724434346363645100604745 1293325759772733825453559)
              ·
                refine ⟨1939988639659100738180339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293325759772733825453559 1939988639659100738180339)
                ·
                  refine ⟨2909982959488651107270509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939988639659100738180339 2909982959488651107270509)
                  ·
                    refine ⟨1091243609808244165226441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2909982959488651107270509 1091243609808244165226441)
                    ·
                      refine ⟨818432707356183123919831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091243609808244165226441 818432707356183123919831)
                      ·
                        rfl

theorem cell23_1593892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1593892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593892 prefixEnd_1593892 := by exact prefixLift 1593892
  have htrace : WordTrace (prefixWord ++ tailWord_1593892) baseStart_1593892 baseEnd_1593892 := by
    simpa [prefixWord, tailWord_1593892, baseEnd_1593892] using wordTrace_append hprefix tailTrace_1593892
  have hstable : (prefixWord ++ tailWord_1593892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593892).length < 2 ^ (prefixWord ++ tailWord_1593892).sum := by decide
  have hdescent : baseEnd_1593892 < baseStart_1593892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593900 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1593900 : Nat := 118140960795 + 1593900 * 2 ^ 59
def prefixEnd_1593900 : Nat := 4983230072969 + 3 ^ 40 * 1593900 * 2
def baseEnd_1593900 : Nat := 818436815201419092619793

theorem tailTrace_1593900 : CollatzResearch.WordTrace tailWord_1593900 prefixEnd_1593900 818436815201419092619793 := by
  unfold tailWord_1593900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29067154462789995646425577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38756205950386660861900769 29067154462789995646425577)
  ·
    refine ⟨21800365847092496734819183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29067154462789995646425577 21800365847092496734819183)
    ·
      refine ⟨32700548770638745102228775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21800365847092496734819183 32700548770638745102228775)
      ·
        refine ⟨49050823155958117653343163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32700548770638745102228775 49050823155958117653343163)
        ·
          refine ⟨73576234733937176480014745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49050823155958117653343163 73576234733937176480014745)
          ·
            refine ⟨55182176050452882360011059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73576234733937176480014745 55182176050452882360011059)
            ·
              refine ⟨82773264075679323540016589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55182176050452882360011059 82773264075679323540016589)
              ·
                refine ⟨31039974028379746327506221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82773264075679323540016589 31039974028379746327506221)
                ·
                  refine ⟨11639990260642404872814833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31039974028379746327506221 11639990260642404872814833)
                  ·
                    refine ⟨8729992695481803654611125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11639990260642404872814833 8729992695481803654611125)
                    ·
                      refine ⟨818436815201419092619793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8729992695481803654611125 818436815201419092619793)
                      ·
                        rfl

theorem cell23_1593900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1593900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593900 prefixEnd_1593900 := by exact prefixLift 1593900
  have htrace : WordTrace (prefixWord ++ tailWord_1593900) baseStart_1593900 baseEnd_1593900 := by
    simpa [prefixWord, tailWord_1593900, baseEnd_1593900] using wordTrace_append hprefix tailTrace_1593900
  have hstable : (prefixWord ++ tailWord_1593900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593900).length < 2 ^ (prefixWord ++ tailWord_1593900).sum := by decide
  have hdescent : baseEnd_1593900 < baseStart_1593900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593927 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1593927 : Nat := 118140960795 + 1593927 * 2 ^ 59
def prefixEnd_1593927 : Nat := 4983230072969 + 3 ^ 40 * 1593927 * 2
def baseEnd_1593927 : Nat := 818450679179090486982169

theorem tailTrace_1593927 : CollatzResearch.WordTrace tailWord_1593927 prefixEnd_1593927 818450679179090486982169 := by
  unfold tailWord_1593927
  simp only [CollatzResearch.WordTrace]
  refine ⟨58135293696482174904084035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38756862464321449936056023 58135293696482174904084035)
  ·
    refine ⟨87202940544723262356126053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58135293696482174904084035 87202940544723262356126053)
    ·
      refine ⟨16350551352135611691773635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87202940544723262356126053 16350551352135611691773635)
      ·
        refine ⟨24525827028203417537660453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350551352135611691773635 24525827028203417537660453)
        ·
          refine ⟨4598592567788140788311335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24525827028203417537660453 4598592567788140788311335)
          ·
            refine ⟨6897888851682211182467003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598592567788140788311335 6897888851682211182467003)
            ·
              refine ⟨10346833277523316773700505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897888851682211182467003 10346833277523316773700505)
              ·
                refine ⟨7760124958142487580275379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10346833277523316773700505 7760124958142487580275379)
                ·
                  refine ⟨11640187437213731370413069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7760124958142487580275379 11640187437213731370413069)
                  ·
                    refine ⟨4365070288955149263904901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11640187437213731370413069 4365070288955149263904901)
                    ·
                      refine ⟨818450679179090486982169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4365070288955149263904901 818450679179090486982169)
                      ·
                        rfl

theorem cell23_1593927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1593927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593927 prefixEnd_1593927 := by exact prefixLift 1593927
  have htrace : WordTrace (prefixWord ++ tailWord_1593927) baseStart_1593927 baseEnd_1593927 := by
    simpa [prefixWord, tailWord_1593927, baseEnd_1593927] using wordTrace_append hprefix tailTrace_1593927
  have hstable : (prefixWord ++ tailWord_1593927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593927).length < 2 ^ (prefixWord ++ tailWord_1593927).sum := by decide
  have hdescent : baseEnd_1593927 < baseStart_1593927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1593984 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 6]
def baseStart_1593984 : Nat := 118140960795 + 1593984 * 2 ^ 59
def prefixEnd_1593984 : Nat := 4983230072969 + 3 ^ 40 * 1593984 * 2
def baseEnd_1593984 : Nat := 90942216397377418218823

theorem tailTrace_1593984 : CollatzResearch.WordTrace tailWord_1593984 prefixEnd_1593984 90942216397377418218823 := by
  unfold tailWord_1593984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29068686328637836819454503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38758248438183782425939337 29068686328637836819454503)
  ·
    refine ⟨43603029492956755229181755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29068686328637836819454503 43603029492956755229181755)
    ·
      refine ⟨65404544239435132843772633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43603029492956755229181755 65404544239435132843772633)
      ·
        refine ⟨49053408179576349632829475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65404544239435132843772633 49053408179576349632829475)
        ·
          refine ⟨73580112269364524449244213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49053408179576349632829475 73580112269364524449244213)
          ·
            refine ⟨6898135525252924167116645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73580112269364524449244213 6898135525252924167116645)
            ·
              refine ⟨1293400410984923281334371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6898135525252924167116645 1293400410984923281334371)
              ·
                refine ⟨1940100616477384922001557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293400410984923281334371 1940100616477384922001557)
                ·
                  refine ⟨90942216397377418218823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1940100616477384922001557 90942216397377418218823)
                  ·
                    rfl

theorem cell23_1593984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 6].length) (baseStart_1593984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1593984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1593984 prefixEnd_1593984 := by exact prefixLift 1593984
  have htrace : WordTrace (prefixWord ++ tailWord_1593984) baseStart_1593984 baseEnd_1593984 := by
    simpa [prefixWord, tailWord_1593984, baseEnd_1593984] using wordTrace_append hprefix tailTrace_1593984
  have hstable : (prefixWord ++ tailWord_1593984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1593984).length < 2 ^ (prefixWord ++ tailWord_1593984).sum := by decide
  have hdescent : baseEnd_1593984 < baseStart_1593984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1593984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594034 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_1594034 : Nat := 118140960795 + 1594034 * 2 ^ 59
def prefixEnd_1594034 : Nat := 4983230072969 + 3 ^ 40 * 1594034 * 2
def baseEnd_1594034 : Nat := 818505621609121568344177

theorem tailTrace_1594034 : CollatzResearch.WordTrace tailWord_1594034 prefixEnd_1594034 818505621609121568344177 := by
  unfold tailWord_1594034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534799076773633044557289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38759464204729688118819437 14534799076773633044557289)
  ·
    refine ⟨10901099307580224783417967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14534799076773633044557289 10901099307580224783417967)
    ·
      refine ⟨16351648961370337175126951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901099307580224783417967 16351648961370337175126951)
      ·
        refine ⟨24527473442055505762690427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16351648961370337175126951 24527473442055505762690427)
        ·
          refine ⟨36791210163083258644035641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24527473442055505762690427 36791210163083258644035641)
          ·
            refine ⟨27593407622312443983026731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36791210163083258644035641 27593407622312443983026731)
            ·
              refine ⟨41390111433468665974540097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27593407622312443983026731 41390111433468665974540097)
              ·
                refine ⟨31042583575101499480905073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41390111433468665974540097 31042583575101499480905073)
                ·
                  refine ⟨23281937681326124610678805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31042583575101499480905073 23281937681326124610678805)
                  ·
                    refine ⟨1091340828812162091125569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23281937681326124610678805 1091340828812162091125569)
                    ·
                      refine ⟨818505621609121568344177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091340828812162091125569 818505621609121568344177)
                      ·
                        rfl

theorem cell23_1594034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_1594034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594034 prefixEnd_1594034 := by exact prefixLift 1594034
  have htrace : WordTrace (prefixWord ++ tailWord_1594034) baseStart_1594034 baseEnd_1594034 := by
    simpa [prefixWord, tailWord_1594034, baseEnd_1594034] using wordTrace_append hprefix tailTrace_1594034
  have hstable : (prefixWord ++ tailWord_1594034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594034).length < 2 ^ (prefixWord ++ tailWord_1594034).sum := by decide
  have hdescent : baseEnd_1594034 < baseStart_1594034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594044 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_1594044 : Nat := 118140960795 + 1594044 * 2 ^ 59
def prefixEnd_1594044 : Nat := 4983230072969 + 3 ^ 40 * 1594044 * 2
def baseEnd_1594044 : Nat := 272836918805222176406377

theorem tailTrace_1594044 : CollatzResearch.WordTrace tailWord_1594044 prefixEnd_1594044 272836918805222176406377 := by
  unfold tailWord_1594044
  simp only [CollatzResearch.WordTrace]
  refine ⟨29069780518529151943046593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38759707358038869257395457 29069780518529151943046593)
  ·
    refine ⟨21802335388896863957284945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29069780518529151943046593 21802335388896863957284945)
    ·
      refine ⟨16351751541672647967963709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21802335388896863957284945 16351751541672647967963709)
      ·
        refine ⟨6131906828127242987986391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16351751541672647967963709 6131906828127242987986391)
        ·
          refine ⟨9197860242190864481979587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131906828127242987986391 9197860242190864481979587)
          ·
            refine ⟨13796790363286296722969381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197860242190864481979587 13796790363286296722969381)
            ·
              refine ⟨2586898193116180635556759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13796790363286296722969381 2586898193116180635556759)
              ·
                refine ⟨3880347289674270953335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586898193116180635556759 3880347289674270953335139)
                ·
                  refine ⟨5820520934511406430002709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880347289674270953335139 5820520934511406430002709)
                  ·
                    refine ⟨272836918805222176406377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5820520934511406430002709 272836918805222176406377)
                    ·
                      rfl

theorem cell23_1594044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_1594044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594044 prefixEnd_1594044 := by exact prefixLift 1594044
  have htrace : WordTrace (prefixWord ++ tailWord_1594044) baseStart_1594044 baseEnd_1594044 := by
    simpa [prefixWord, tailWord_1594044, baseEnd_1594044] using wordTrace_append hprefix tailTrace_1594044
  have hstable : (prefixWord ++ tailWord_1594044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594044).length < 2 ^ (prefixWord ++ tailWord_1594044).sum := by decide
  have hdescent : baseEnd_1594044 < baseStart_1594044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594068 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1594068 : Nat := 118140960795 + 1594068 * 2 ^ 59
def prefixEnd_1594068 : Nat := 4983230072969 + 3 ^ 40 * 1594068 * 2
def baseEnd_1594068 : Nat := 818523079951374435319021

theorem tailTrace_1594068 : CollatzResearch.WordTrace tailWord_1594068 prefixEnd_1594068 818523079951374435319021 := by
  unfold tailWord_1594068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29070218194485677992483429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38760290925980903989977905 29070218194485677992483429)
  ·
    refine ⟨5450665911466064623590643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29070218194485677992483429 5450665911466064623590643)
    ·
      refine ⟨8175998867199096935385965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450665911466064623590643 8175998867199096935385965)
      ·
        refine ⟨3065999575199661350769737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8175998867199096935385965 3065999575199661350769737)
        ·
          refine ⟨2299499681399746013077303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3065999575199661350769737 2299499681399746013077303)
          ·
            refine ⟨3449249522099619019615955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299499681399746013077303 3449249522099619019615955)
            ·
              refine ⟨5173874283149428529423933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449249522099619019615955 5173874283149428529423933)
              ·
                refine ⟨1940202856181035698533975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5173874283149428529423933 1940202856181035698533975)
                ·
                  refine ⟨2910304284271553547800963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940202856181035698533975 2910304284271553547800963)
                  ·
                    refine ⟨4365456426407330321701445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2910304284271553547800963 4365456426407330321701445)
                    ·
                      refine ⟨818523079951374435319021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4365456426407330321701445 818523079951374435319021)
                      ·
                        rfl

theorem cell23_1594068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1594068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594068 prefixEnd_1594068 := by exact prefixLift 1594068
  have htrace : WordTrace (prefixWord ++ tailWord_1594068) baseStart_1594068 baseEnd_1594068 := by
    simpa [prefixWord, tailWord_1594068, baseEnd_1594068] using wordTrace_append hprefix tailTrace_1594068
  have hstable : (prefixWord ++ tailWord_1594068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594068).length < 2 ^ (prefixWord ++ tailWord_1594068).sum := by decide
  have hdescent : baseEnd_1594068 < baseStart_1594068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594071 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1594071 : Nat := 118140960795 + 1594071 * 2 ^ 59
def prefixEnd_1594071 : Nat := 4983230072969 + 3 ^ 40 * 1594071 * 2
def baseEnd_1594071 : Nat := 818524620393337923581507

theorem tailTrace_1594071 : CollatzResearch.WordTrace tailWord_1594071 prefixEnd_1594071 818524620393337923581507 := by
  unfold tailWord_1594071
  simp only [CollatzResearch.WordTrace]
  refine ⟨58140545807960487497326067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38760363871973658331550711 58140545807960487497326067)
  ·
    refine ⟨87210818711940731245989101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58140545807960487497326067 87210818711940731245989101)
    ·
      refine ⟨32704057016977774217245913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87210818711940731245989101 32704057016977774217245913)
      ·
        refine ⟨24528042762733330662934435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32704057016977774217245913 24528042762733330662934435)
        ·
          refine ⟨36792064144099995994401653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24528042762733330662934435 36792064144099995994401653)
          ·
            refine ⟨3449256013509374624475155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36792064144099995994401653 3449256013509374624475155)
            ·
              refine ⟨5173884020264061936712733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449256013509374624475155 5173884020264061936712733)
              ·
                refine ⟨1940206507599023226267275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5173884020264061936712733 1940206507599023226267275)
                ·
                  refine ⟨2910309761398534839400913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940206507599023226267275 2910309761398534839400913)
                  ·
                    refine ⟨2182732321048901129550685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910309761398534839400913 2182732321048901129550685)
                    ·
                      refine ⟨818524620393337923581507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2182732321048901129550685 818524620393337923581507)
                      ·
                        rfl

theorem cell23_1594071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1594071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594071 prefixEnd_1594071 := by exact prefixLift 1594071
  have htrace : WordTrace (prefixWord ++ tailWord_1594071) baseStart_1594071 baseEnd_1594071 := by
    simpa [prefixWord, tailWord_1594071, baseEnd_1594071] using wordTrace_append hprefix tailTrace_1594071
  have hstable : (prefixWord ++ tailWord_1594071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594071).length < 2 ^ (prefixWord ++ tailWord_1594071).sum := by decide
  have hdescent : baseEnd_1594071 < baseStart_1594071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594085 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1594085 : Nat := 118140960795 + 1594085 * 2 ^ 59
def prefixEnd_1594085 : Nat := 4983230072969 + 3 ^ 40 * 1594085 * 2
def baseEnd_1594085 : Nat := 818531809122500868806443

theorem tailTrace_1594085 : CollatzResearch.WordTrace tailWord_1594085 prefixEnd_1594085 818531809122500868806443 := by
  unfold tailWord_1594085
  simp only [CollatzResearch.WordTrace]
  refine ⟨58141056429909767888335709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38760704286606511925557139 58141056429909767888335709)
  ·
    refine ⟨21802896161216162958125891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58141056429909767888335709 21802896161216162958125891)
    ·
      refine ⟨32704344241824244437188837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21802896161216162958125891 32704344241824244437188837)
      ·
        refine ⟨6132064545342045831972907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32704344241824244437188837 6132064545342045831972907)
        ·
          refine ⟨9198096818013068747959361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132064545342045831972907 9198096818013068747959361)
          ·
            refine ⟨6898572613509801560969521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9198096818013068747959361 6898572613509801560969521)
            ·
              refine ⟨5173929460132351170727141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898572613509801560969521 5173929460132351170727141)
              ·
                refine ⟨970111773774815844511339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5173929460132351170727141 970111773774815844511339)
                ·
                  refine ⟨1455167660662223766767009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970111773774815844511339 1455167660662223766767009)
                  ·
                    refine ⟨1091375745496667825075257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455167660662223766767009 1091375745496667825075257)
                    ·
                      refine ⟨818531809122500868806443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091375745496667825075257 818531809122500868806443)
                      ·
                        rfl

theorem cell23_1594085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1594085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594085 prefixEnd_1594085 := by exact prefixLift 1594085
  have htrace : WordTrace (prefixWord ++ tailWord_1594085) baseStart_1594085 baseEnd_1594085 := by
    simpa [prefixWord, tailWord_1594085, baseEnd_1594085] using wordTrace_append hprefix tailTrace_1594085
  have hstable : (prefixWord ++ tailWord_1594085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594085).length < 2 ^ (prefixWord ++ tailWord_1594085).sum := by decide
  have hdescent : baseEnd_1594085 < baseStart_1594085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594107 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_1594107 : Nat := 118140960795 + 1594107 * 2 ^ 59
def prefixEnd_1594107 : Nat := 4983230072969 + 3 ^ 40 * 1594107 * 2
def baseEnd_1594107 : Nat := 818543105696899782731341

theorem tailTrace_1594107 : CollatzResearch.WordTrace tailWord_1594107 prefixEnd_1594107 818543105696899782731341 := by
  unfold tailWord_1594107
  simp only [CollatzResearch.WordTrace]
  refine ⟨58141858835830065645636575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38761239223886710430424383 58141858835830065645636575)
  ·
    refine ⟨87212788253745098468454863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58141858835830065645636575 87212788253745098468454863)
    ·
      refine ⟨130819182380617647702682295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87212788253745098468454863 130819182380617647702682295)
      ·
        refine ⟨196228773570926471554023443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130819182380617647702682295 196228773570926471554023443)
        ·
          refine ⟨294343160356389707331035165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196228773570926471554023443 294343160356389707331035165)
          ·
            refine ⟨110378685133646140249138187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294343160356389707331035165 110378685133646140249138187)
            ·
              refine ⟨165568027700469210373707281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110378685133646140249138187 165568027700469210373707281)
              ·
                refine ⟨124176020775351907780280461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165568027700469210373707281 124176020775351907780280461)
                ·
                  refine ⟨46566007790756965417605173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124176020775351907780280461 46566007790756965417605173)
                  ·
                    refine ⟨4365563230383465507900485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46566007790756965417605173 4365563230383465507900485)
                    ·
                      refine ⟨818543105696899782731341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4365563230383465507900485 818543105696899782731341)
                      ·
                        rfl

theorem cell23_1594107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_1594107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594107 prefixEnd_1594107 := by exact prefixLift 1594107
  have htrace : WordTrace (prefixWord ++ tailWord_1594107) baseStart_1594107 baseEnd_1594107 := by
    simpa [prefixWord, tailWord_1594107, baseEnd_1594107] using wordTrace_append hprefix tailTrace_1594107
  have hstable : (prefixWord ++ tailWord_1594107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594107).length < 2 ^ (prefixWord ++ tailWord_1594107).sum := by decide
  have hdescent : baseEnd_1594107 < baseStart_1594107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594117 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1594117 : Nat := 118140960795 + 1594117 * 2 ^ 59
def prefixEnd_1594117 : Nat := 4983230072969 + 3 ^ 40 * 1594117 * 2
def baseEnd_1594117 : Nat := 272849413501148247868765

theorem tailTrace_1594117 : CollatzResearch.WordTrace tailWord_1594117 prefixEnd_1594117 272849413501148247868765 := by
  unfold tailWord_1594117
  simp only [CollatzResearch.WordTrace]
  refine ⟨58142223565793837353500605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38761482377195891569000403 58142223565793837353500605)
  ·
    refine ⟨21803333837172689007562727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58142223565793837353500605 21803333837172689007562727)
    ·
      refine ⟨32705000755759033511344091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21803333837172689007562727 32705000755759033511344091)
      ·
        refine ⟨49057501133638550267016137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32705000755759033511344091 49057501133638550267016137)
        ·
          refine ⟨36793125850228912700262103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49057501133638550267016137 36793125850228912700262103)
          ·
            refine ⟨55189688775343369050393155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36793125850228912700262103 55189688775343369050393155)
            ·
              refine ⟨82784533163015053575589733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55189688775343369050393155 82784533163015053575589733)
              ·
                refine ⟨15522099968065322545423075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82784533163015053575589733 15522099968065322545423075)
                ·
                  refine ⟨23283149952097983818134613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522099968065322545423075 23283149952097983818134613)
                  ·
                    refine ⟨272849413501148247868765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23283149952097983818134613 272849413501148247868765)
                    ·
                      rfl

theorem cell23_1594117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1594117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594117 prefixEnd_1594117 := by exact prefixLift 1594117
  have htrace : WordTrace (prefixWord ++ tailWord_1594117) baseStart_1594117 baseEnd_1594117 := by
    simpa [prefixWord, tailWord_1594117, baseEnd_1594117] using wordTrace_append hprefix tailTrace_1594117
  have hstable : (prefixWord ++ tailWord_1594117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594117).length < 2 ^ (prefixWord ++ tailWord_1594117).sum := by decide
  have hdescent : baseEnd_1594117 < baseStart_1594117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594137 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1594137 : Nat := 118140960795 + 1594137 * 2 ^ 59
def prefixEnd_1594137 : Nat := 4983230072969 + 3 ^ 40 * 1594137 * 2
def baseEnd_1594137 : Nat := 818558510116534665356203

theorem tailTrace_1594137 : CollatzResearch.WordTrace tailWord_1594137 prefixEnd_1594137 818558510116534665356203 := by
  unfold tailWord_1594137
  simp only [CollatzResearch.WordTrace]
  refine ⟨58142953025721380769228665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38761968683814253846152443 58142953025721380769228665)
  ·
    refine ⟨43607214769291035576921499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58142953025721380769228665 43607214769291035576921499)
    ·
      refine ⟨65410822153936553365382249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43607214769291035576921499 65410822153936553365382249)
      ·
        refine ⟨49058116615452415024036687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65410822153936553365382249 49058116615452415024036687)
        ·
          refine ⟨73587174923178622536055031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49058116615452415024036687 73587174923178622536055031)
          ·
            refine ⟨110380762384767933804082547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73587174923178622536055031 110380762384767933804082547)
            ·
              refine ⟨165571143577151900706123821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110380762384767933804082547 165571143577151900706123821)
              ·
                refine ⟨62089178841431962764796433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165571143577151900706123821 62089178841431962764796433)
                ·
                  refine ⟨46566884131073972073597325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62089178841431962764796433 46566884131073972073597325)
                  ·
                    refine ⟨17462581549152739527598997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46566884131073972073597325 17462581549152739527598997)
                    ·
                      refine ⟨818558510116534665356203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17462581549152739527598997 818558510116534665356203)
                      ·
                        rfl

theorem cell23_1594137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1594137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594137 prefixEnd_1594137 := by exact prefixLift 1594137
  have htrace : WordTrace (prefixWord ++ tailWord_1594137) baseStart_1594137 baseEnd_1594137 := by
    simpa [prefixWord, tailWord_1594137, baseEnd_1594137] using wordTrace_append hprefix tailTrace_1594137
  have hstable : (prefixWord ++ tailWord_1594137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594137).length < 2 ^ (prefixWord ++ tailWord_1594137).sum := by decide
  have hdescent : baseEnd_1594137 < baseStart_1594137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594201 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 5, 2]
def baseStart_1594201 : Nat := 118140960795 + 1594201 * 2 ^ 59
def prefixEnd_1594201 : Nat := 4983230072969 + 3 ^ 40 * 1594201 * 2
def baseEnd_1594201 : Nat := 818591372878422414955909

theorem tailTrace_1594201 : CollatzResearch.WordTrace tailWord_1594201 prefixEnd_1594201 818591372878422414955909 := by
  unfold tailWord_1594201
  simp only [CollatzResearch.WordTrace]
  refine ⟨58145287297489519699558457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38763524864993013133038971 58145287297489519699558457)
  ·
    refine ⟨43608965473117139774668843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58145287297489519699558457 43608965473117139774668843)
    ·
      refine ⟨65413448209675709662003265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43608965473117139774668843 65413448209675709662003265)
      ·
        refine ⟨49060086157256782246502449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65413448209675709662003265 49060086157256782246502449)
        ·
          refine ⟨36795064617942586684876837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49060086157256782246502449 36795064617942586684876837)
          ·
            refine ⟨6899074615864235003414407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36795064617942586684876837 6899074615864235003414407)
            ·
              refine ⟨10348611923796352505121611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899074615864235003414407 10348611923796352505121611)
              ·
                refine ⟨15522917885694528757682417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348611923796352505121611 15522917885694528757682417)
                ·
                  refine ⟨11642188414270896568261813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15522917885694528757682417 11642188414270896568261813)
                  ·
                    refine ⟨1091455163837896553274545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11642188414270896568261813 1091455163837896553274545)
                    ·
                      refine ⟨818591372878422414955909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091455163837896553274545 818591372878422414955909)
                      ·
                        rfl

theorem cell23_1594201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_1594201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594201 prefixEnd_1594201 := by exact prefixLift 1594201
  have htrace : WordTrace (prefixWord ++ tailWord_1594201) baseStart_1594201 baseEnd_1594201 := by
    simpa [prefixWord, tailWord_1594201, baseEnd_1594201] using wordTrace_append hprefix tailTrace_1594201
  have hstable : (prefixWord ++ tailWord_1594201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594201).length < 2 ^ (prefixWord ++ tailWord_1594201).sum := by decide
  have hdescent : baseEnd_1594201 < baseStart_1594201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594248 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1594248 : Nat := 118140960795 + 1594248 * 2 ^ 59
def prefixEnd_1594248 : Nat := 4983230072969 + 3 ^ 40 * 1594248 * 2
def baseEnd_1594248 : Nat := 818615506469183731068193

theorem tailTrace_1594248 : CollatzResearch.WordTrace tailWord_1594248 prefixEnd_1594248 818615506469183731068193 := by
  unfold tailWord_1594248
  simp only [CollatzResearch.WordTrace]
  refine ⟨29073500764159623363259699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38764667685546164484346265 29073500764159623363259699)
  ·
    refine ⟨43610251146239435044889549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29073500764159623363259699 43610251146239435044889549)
    ·
      refine ⟨16353844179839788141833581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43610251146239435044889549 16353844179839788141833581)
      ·
        refine ⟨6132691567439920553187593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16353844179839788141833581 6132691567439920553187593)
        ·
          refine ⟨4599518675579940414890695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6132691567439920553187593 4599518675579940414890695)
          ·
            refine ⟨6899278013369910622336043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599518675579940414890695 6899278013369910622336043)
            ·
              refine ⟨10348917020054865933504065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899278013369910622336043 10348917020054865933504065)
              ·
                refine ⟨7761687765041149450128049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10348917020054865933504065 7761687765041149450128049)
                ·
                  refine ⟨5821265823780862087596037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7761687765041149450128049 5821265823780862087596037)
                  ·
                    refine ⟨1091487341958911641424257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5821265823780862087596037 1091487341958911641424257)
                    ·
                      refine ⟨818615506469183731068193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091487341958911641424257 818615506469183731068193)
                      ·
                        rfl

theorem cell23_1594248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1594248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594248 prefixEnd_1594248 := by exact prefixLift 1594248
  have htrace : WordTrace (prefixWord ++ tailWord_1594248) baseStart_1594248 baseEnd_1594248 := by
    simpa [prefixWord, tailWord_1594248, baseEnd_1594248] using wordTrace_append hprefix tailTrace_1594248
  have hstable : (prefixWord ++ tailWord_1594248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594248).length < 2 ^ (prefixWord ++ tailWord_1594248).sum := by decide
  have hdescent : baseEnd_1594248 < baseStart_1594248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594251 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3]
def baseStart_1594251 : Nat := 118140960795 + 1594251 * 2 ^ 59
def prefixEnd_1594251 : Nat := 4983230072969 + 3 ^ 40 * 1594251 * 2
def baseEnd_1594251 : Nat := 818617046911147219330679

theorem tailTrace_1594251 : CollatzResearch.WordTrace tailWord_1594251 prefixEnd_1594251 818617046911147219330679 := by
  unfold tailWord_1594251
  simp only [CollatzResearch.WordTrace]
  refine ⟨58147110947308378238878607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38764740631538918825919071 58147110947308378238878607)
  ·
    refine ⟨87220666420962567358317911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58147110947308378238878607 87220666420962567358317911)
    ·
      refine ⟨130830999631443851037476867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87220666420962567358317911 130830999631443851037476867)
      ·
        refine ⟨196246499447165776556215301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130830999631443851037476867 196246499447165776556215301)
        ·
          refine ⟨36796218646343583104290369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196246499447165776556215301 36796218646343583104290369)
          ·
            refine ⟨27597163984757687328217777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36796218646343583104290369 27597163984757687328217777)
            ·
              refine ⟨20697872988568265496163333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27597163984757687328217777 20697872988568265496163333)
              ·
                refine ⟨3880851185356549780530625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20697872988568265496163333 3880851185356549780530625)
                ·
                  refine ⟨2910638389017412335397969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880851185356549780530625 2910638389017412335397969)
                  ·
                    refine ⟨2182978791763059251548477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910638389017412335397969 2182978791763059251548477)
                    ·
                      refine ⟨818617046911147219330679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2182978791763059251548477 818617046911147219330679)
                      ·
                        rfl

theorem cell23_1594251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3].length) (baseStart_1594251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594251 prefixEnd_1594251 := by exact prefixLift 1594251
  have htrace : WordTrace (prefixWord ++ tailWord_1594251) baseStart_1594251 baseEnd_1594251 := by
    simpa [prefixWord, tailWord_1594251, baseEnd_1594251] using wordTrace_append hprefix tailTrace_1594251
  have hstable : (prefixWord ++ tailWord_1594251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594251).length < 2 ^ (prefixWord ++ tailWord_1594251).sum := by decide
  have hdescent : baseEnd_1594251 < baseStart_1594251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594315 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 3]
def baseStart_1594315 : Nat := 118140960795 + 1594315 * 2 ^ 59
def prefixEnd_1594315 : Nat := 4983230072969 + 3 ^ 40 * 1594315 * 2
def baseEnd_1594315 : Nat := 818649909673034968930385

theorem tailTrace_1594315 : CollatzResearch.WordTrace tailWord_1594315 prefixEnd_1594315 818649909673034968930385 := by
  unfold tailWord_1594315
  simp only [CollatzResearch.WordTrace]
  refine ⟨58149445219076517169208399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38766296812717678112805599 58149445219076517169208399)
  ·
    refine ⟨87224167828614775753812599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58149445219076517169208399 87224167828614775753812599)
    ·
      refine ⟨130836251742922163630718899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87224167828614775753812599 130836251742922163630718899)
      ·
        refine ⟨196254377614383245446078349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130836251742922163630718899 196254377614383245446078349)
        ·
          refine ⟨73595391605393717042279381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196254377614383245446078349 73595391605393717042279381)
          ·
            refine ⟨1724891990751415243178423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73595391605393717042279381 1724891990751415243178423)
            ·
              refine ⟨2587337986127122864767635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724891990751415243178423 2587337986127122864767635)
              ·
                refine ⟨3881006979190684297151453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587337986127122864767635 3881006979190684297151453)
                ·
                  refine ⟨1455377617196506611431795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881006979190684297151453 1455377617196506611431795)
                  ·
                    refine ⟨2183066425794759917147693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455377617196506611431795 2183066425794759917147693)
                    ·
                      refine ⟨818649909673034968930385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183066425794759917147693 818649909673034968930385)
                      ·
                        rfl

theorem cell23_1594315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 3].length) (baseStart_1594315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594315 prefixEnd_1594315 := by exact prefixLift 1594315
  have htrace : WordTrace (prefixWord ++ tailWord_1594315) baseStart_1594315 baseEnd_1594315 := by
    simpa [prefixWord, tailWord_1594315, baseEnd_1594315] using wordTrace_append hprefix tailTrace_1594315
  have hstable : (prefixWord ++ tailWord_1594315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594315).length < 2 ^ (prefixWord ++ tailWord_1594315).sum := by decide
  have hdescent : baseEnd_1594315 < baseStart_1594315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594321 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_1594321 : Nat := 118140960795 + 1594321 * 2 ^ 59
def prefixEnd_1594321 : Nat := 4983230072969 + 3 ^ 40 * 1594321 * 2
def baseEnd_1594321 : Nat := 818652990556961945455357

theorem tailTrace_1594321 : CollatzResearch.WordTrace tailWord_1594321 prefixEnd_1594321 818652990556961945455357 := by
  unfold tailWord_1594321
  simp only [CollatzResearch.WordTrace]
  refine ⟨58149664057054780193926817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38766442704703186795951211 58149664057054780193926817)
  ·
    refine ⟨43612248042791085145445113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58149664057054780193926817 43612248042791085145445113)
    ·
      refine ⟨32709186032093313859083835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43612248042791085145445113 32709186032093313859083835)
      ·
        refine ⟨49063779048139970788625753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32709186032093313859083835 49063779048139970788625753)
        ·
          refine ⟨36797834286104978091469315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49063779048139970788625753 36797834286104978091469315)
          ·
            refine ⟨55196751429157467137203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36797834286104978091469315 55196751429157467137203973)
            ·
              refine ⟨10349390892967025088225745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55196751429157467137203973 10349390892967025088225745)
              ·
                refine ⟨7762043169725268816169309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10349390892967025088225745 7762043169725268816169309)
                ·
                  refine ⟨2910766188646975806063491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7762043169725268816169309 2910766188646975806063491)
                  ·
                    refine ⟨4366149282970463709095237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2910766188646975806063491 4366149282970463709095237)
                    ·
                      refine ⟨818652990556961945455357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4366149282970463709095237 818652990556961945455357)
                      ·
                        rfl

theorem cell23_1594321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_1594321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594321 prefixEnd_1594321 := by exact prefixLift 1594321
  have htrace : WordTrace (prefixWord ++ tailWord_1594321) baseStart_1594321 baseEnd_1594321 := by
    simpa [prefixWord, tailWord_1594321, baseEnd_1594321] using wordTrace_append hprefix tailTrace_1594321
  have hstable : (prefixWord ++ tailWord_1594321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594321).length < 2 ^ (prefixWord ++ tailWord_1594321).sum := by decide
  have hdescent : baseEnd_1594321 < baseStart_1594321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594335 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 1, 5]
def baseStart_1594335 : Nat := 118140960795 + 1594335 * 2 ^ 59
def prefixEnd_1594335 : Nat := 4983230072969 + 3 ^ 40 * 1594335 * 2
def baseEnd_1594335 : Nat := 272886726428708296893431

theorem tailTrace_1594335 : CollatzResearch.WordTrace tailWord_1594335 prefixEnd_1594335 272886726428708296893431 := by
  unfold tailWord_1594335
  simp only [CollatzResearch.WordTrace]
  refine ⟨58150174679004060584936459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38766783119336040389957639 58150174679004060584936459)
  ·
    refine ⟨87225262018506090877404689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58150174679004060584936459 87225262018506090877404689)
    ·
      refine ⟨65418946513879568158053517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87225262018506090877404689 65418946513879568158053517)
      ·
        refine ⟨24532104942704838059270069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65418946513879568158053517 24532104942704838059270069)
        ·
          refine ⟨2299884838378578568056569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24532104942704838059270069 2299884838378578568056569)
          ·
            refine ⟨1724913628783933926042427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299884838378578568056569 1724913628783933926042427)
            ·
              refine ⟨2587370443175900889063641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724913628783933926042427 2587370443175900889063641)
              ·
                refine ⟨1940527832381925666797731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587370443175900889063641 1940527832381925666797731)
                ·
                  refine ⟨2910791748572888500196597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940527832381925666797731 2910791748572888500196597)
                  ·
                    refine ⟨272886726428708296893431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2910791748572888500196597 272886726428708296893431)
                    ·
                      rfl

theorem cell23_1594335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_1594335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594335 prefixEnd_1594335 := by exact prefixLift 1594335
  have htrace : WordTrace (prefixWord ++ tailWord_1594335) baseStart_1594335 baseEnd_1594335 := by
    simpa [prefixWord, tailWord_1594335, baseEnd_1594335] using wordTrace_append hprefix tailTrace_1594335
  have hstable : (prefixWord ++ tailWord_1594335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594335).length < 2 ^ (prefixWord ++ tailWord_1594335).sum := by decide
  have hdescent : baseEnd_1594335 < baseStart_1594335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594351 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_1594351 : Nat := 118140960795 + 1594351 * 2 ^ 59
def prefixEnd_1594351 : Nat := 4983230072969 + 3 ^ 40 * 1594351 * 2
def baseEnd_1594351 : Nat := 818668394976596828080219

theorem tailTrace_1594351 : CollatzResearch.WordTrace tailWord_1594351 prefixEnd_1594351 818668394976596828080219 := by
  unfold tailWord_1594351
  simp only [CollatzResearch.WordTrace]
  refine ⟨58150758246946095317518907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38767172164630730211679271 58150758246946095317518907)
  ·
    refine ⟨87226137370419142976278361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58150758246946095317518907 87226137370419142976278361)
    ·
      refine ⟨65419603027814357232208771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87226137370419142976278361 65419603027814357232208771)
      ·
        refine ⟨98129404541721535848313157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65419603027814357232208771 98129404541721535848313157)
        ·
          refine ⟨18399263351572787971558717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98129404541721535848313157 18399263351572787971558717)
          ·
            refine ⟨6899723756839795489334519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18399263351572787971558717 6899723756839795489334519)
            ·
              refine ⟨10349585635259693234001779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899723756839795489334519 10349585635259693234001779)
              ·
                refine ⟨15524378452889539851002669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10349585635259693234001779 15524378452889539851002669)
                ·
                  refine ⟨5821641919833577444126001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15524378452889539851002669 5821641919833577444126001)
                  ·
                    refine ⟨4366231439875183083094501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821641919833577444126001 4366231439875183083094501)
                    ·
                      refine ⟨818668394976596828080219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4366231439875183083094501 818668394976596828080219)
                      ·
                        rfl

theorem cell23_1594351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_1594351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594351 prefixEnd_1594351 := by exact prefixLift 1594351
  have htrace : WordTrace (prefixWord ++ tailWord_1594351) baseStart_1594351 baseEnd_1594351 := by
    simpa [prefixWord, tailWord_1594351, baseEnd_1594351] using wordTrace_append hprefix tailTrace_1594351
  have hstable : (prefixWord ++ tailWord_1594351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594351).length < 2 ^ (prefixWord ++ tailWord_1594351).sum := by decide
  have hdescent : baseEnd_1594351 < baseStart_1594351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594378 : List Nat := [3, 1, 2, 2, 3, 3, 1, 8]
def baseStart_1594378 : Nat := 118140960795 + 1594378 * 2 ^ 59
def prefixEnd_1594378 : Nat := 4983230072969 + 3 ^ 40 * 1594378 * 2
def baseEnd_1594378 : Nat := 30321565146454378608985

theorem tailTrace_1594378 : CollatzResearch.WordTrace tailWord_1594378 prefixEnd_1594378 30321565146454378608985 := by
  unfold tailWord_1594378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14537935754462069732187947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38767828678565519285834525 14537935754462069732187947)
  ·
    refine ⟨21806903631693104598281921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14537935754462069732187947 21806903631693104598281921)
    ·
      refine ⟨16355177723769828448711441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21806903631693104598281921 16355177723769828448711441)
      ·
        refine ⟨12266383292827371336533581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16355177723769828448711441 12266383292827371336533581)
        ·
          refine ⟨4599893734810264251200093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12266383292827371336533581 4599893734810264251200093)
          ·
            refine ⟨1724960150553849094200035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4599893734810264251200093 1724960150553849094200035)
            ·
              refine ⟨2587440225830773641300053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724960150553849094200035 2587440225830773641300053)
              ·
                refine ⟨30321565146454378608985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2587440225830773641300053 30321565146454378608985)
                ·
                  rfl

theorem cell23_1594378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_1594378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594378 prefixEnd_1594378 := by exact prefixLift 1594378
  have htrace : WordTrace (prefixWord ++ tailWord_1594378) baseStart_1594378 baseEnd_1594378 := by
    simpa [prefixWord, tailWord_1594378, baseEnd_1594378] using wordTrace_append hprefix tailTrace_1594378
  have hstable : (prefixWord ++ tailWord_1594378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594378).length < 2 ^ (prefixWord ++ tailWord_1594378).sum := by decide
  have hdescent : baseEnd_1594378 < baseStart_1594378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594422 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1594422 : Nat := 118140960795 + 1594422 * 2 ^ 59
def prefixEnd_1594422 : Nat := 4983230072969 + 3 ^ 40 * 1594422 * 2
def baseEnd_1594422 : Nat := 818704852103066050292393

theorem tailTrace_1594422 : CollatzResearch.WordTrace tailWord_1594422 prefixEnd_1594422 818704852103066050292393 := by
  unfold tailWord_1594422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634584239355554652709595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38768898553125916295569013 3634584239355554652709595)
  ·
    refine ⟨5451876359033331979064393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634584239355554652709595 5451876359033331979064393)
    ·
      refine ⟨4088907269274998984298295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5451876359033331979064393 4088907269274998984298295)
      ·
        refine ⟨6133360903912498476447443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088907269274998984298295 6133360903912498476447443)
        ·
          refine ⟨9200041355868747714671165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133360903912498476447443 9200041355868747714671165)
          ·
            refine ⟨3450015508450780393001687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9200041355868747714671165 3450015508450780393001687)
            ·
              refine ⟨5175023262676170589502531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450015508450780393001687 5175023262676170589502531)
              ·
                refine ⟨7762534894014255884253797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175023262676170589502531 7762534894014255884253797)
                ·
                  refine ⟨1455475292627672978297587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7762534894014255884253797 1455475292627672978297587)
                  ·
                    refine ⟨2183212938941509467446381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455475292627672978297587 2183212938941509467446381)
                    ·
                      refine ⟨818704852103066050292393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183212938941509467446381 818704852103066050292393)
                      ·
                        rfl

theorem cell23_1594422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1594422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594422 prefixEnd_1594422 := by exact prefixLift 1594422
  have htrace : WordTrace (prefixWord ++ tailWord_1594422) baseStart_1594422 baseEnd_1594422 := by
    simpa [prefixWord, tailWord_1594422, baseEnd_1594422] using wordTrace_append hprefix tailTrace_1594422
  have hstable : (prefixWord ++ tailWord_1594422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594422).length < 2 ^ (prefixWord ++ tailWord_1594422).sum := by decide
  have hdescent : baseEnd_1594422 < baseStart_1594422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594431 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1594431 : Nat := 118140960795 + 1594431 * 2 ^ 59
def prefixEnd_1594431 : Nat := 4983230072969 + 3 ^ 40 * 1594431 * 2
def baseEnd_1594431 : Nat := 818709473428956515079851

theorem tailTrace_1594431 : CollatzResearch.WordTrace tailWord_1594431 prefixEnd_1594431 818709473428956515079851 := by
  unfold tailWord_1594431
  simp only [CollatzResearch.WordTrace]
  refine ⟨58153676086656268980431147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38769117391104179320287431 58153676086656268980431147)
  ·
    refine ⟨87230514129984403470646721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58153676086656268980431147 87230514129984403470646721)
    ·
      refine ⟨65422885597488302602985041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87230514129984403470646721 65422885597488302602985041)
      ·
        refine ⟨49067164198116226952238781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65422885597488302602985041 49067164198116226952238781)
        ·
          refine ⟨18400186574293585107089543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49067164198116226952238781 18400186574293585107089543)
          ·
            refine ⟨27600279861440377660634315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18400186574293585107089543 27600279861440377660634315)
            ·
              refine ⟨41400419792160566490951473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27600279861440377660634315 41400419792160566490951473)
              ·
                refine ⟨31050314844120424868213605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41400419792160566490951473 31050314844120424868213605)
                ·
                  refine ⟨5821934033272579662790051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31050314844120424868213605 5821934033272579662790051)
                  ·
                    refine ⟨8732901049908869494185077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5821934033272579662790051 8732901049908869494185077)
                    ·
                      refine ⟨818709473428956515079851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8732901049908869494185077 818709473428956515079851)
                      ·
                        rfl

theorem cell23_1594431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1594431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594431 prefixEnd_1594431 := by exact prefixLift 1594431
  have htrace : WordTrace (prefixWord ++ tailWord_1594431) baseStart_1594431 baseEnd_1594431 := by
    simpa [prefixWord, tailWord_1594431, baseEnd_1594431] using wordTrace_append hprefix tailTrace_1594431
  have hstable : (prefixWord ++ tailWord_1594431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594431).length < 2 ^ (prefixWord ++ tailWord_1594431).sum := by decide
  have hdescent : baseEnd_1594431 < baseStart_1594431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594441 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_1594441 : Nat := 118140960795 + 1594441 * 2 ^ 59
def prefixEnd_1594441 : Nat := 4983230072969 + 3 ^ 40 * 1594441 * 2
def baseEnd_1594441 : Nat := 818714608235501475954805

theorem tailTrace_1594441 : CollatzResearch.WordTrace tailWord_1594441 prefixEnd_1594441 818714608235501475954805 := by
  unfold tailWord_1594441
  simp only [CollatzResearch.WordTrace]
  refine ⟨58154040816620040688295177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38769360544413360458863451 58154040816620040688295177)
  ·
    refine ⟨43615530612465030516221383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58154040816620040688295177 43615530612465030516221383)
    ·
      refine ⟨65423295918697545774332075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43615530612465030516221383 65423295918697545774332075)
      ·
        refine ⟨98134943878046318661498113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65423295918697545774332075 98134943878046318661498113)
        ·
          refine ⟨73601207908534738996123585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98134943878046318661498113 73601207908534738996123585)
          ·
            refine ⟨55200905931401054247092689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73601207908534738996123585 55200905931401054247092689)
            ·
              refine ⟨41400679448550790685319517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55200905931401054247092689 41400679448550790685319517)
              ·
                refine ⟨15525254793206546506994819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41400679448550790685319517 15525254793206546506994819)
                ·
                  refine ⟨23287882189809819760492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15525254793206546506994819 23287882189809819760492229)
                  ·
                    refine ⟨4366477910589341205092293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23287882189809819760492229 4366477910589341205092293)
                    ·
                      refine ⟨818714608235501475954805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4366477910589341205092293 818714608235501475954805)
                      ·
                        rfl

theorem cell23_1594441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_1594441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594441 prefixEnd_1594441 := by exact prefixLift 1594441
  have htrace : WordTrace (prefixWord ++ tailWord_1594441) baseStart_1594441 baseEnd_1594441 := by
    simpa [prefixWord, tailWord_1594441, baseEnd_1594441] using wordTrace_append hprefix tailTrace_1594441
  have hstable : (prefixWord ++ tailWord_1594441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594441).length < 2 ^ (prefixWord ++ tailWord_1594441).sum := by decide
  have hdescent : baseEnd_1594441 < baseStart_1594441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594481 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_1594481 : Nat := 118140960795 + 1594481 * 2 ^ 59
def prefixEnd_1594481 : Nat := 4983230072969 + 3 ^ 40 * 1594481 * 2
def baseEnd_1594481 : Nat := 272911715820560439818207

theorem tailTrace_1594481 : CollatzResearch.WordTrace tailWord_1594481 prefixEnd_1594481 272911715820560439818207 := by
  unfold tailWord_1594481
  simp only [CollatzResearch.WordTrace]
  refine ⟨58155499736475127519751297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38770333157650085013167531 58155499736475127519751297)
  ·
    refine ⟨43616624802356345639813473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58155499736475127519751297 43616624802356345639813473)
    ·
      refine ⟨32712468601767259229860105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43616624802356345639813473 32712468601767259229860105)
      ·
        refine ⟨24534351451325444422395079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32712468601767259229860105 24534351451325444422395079)
        ·
          refine ⟨36801527176988166633592619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24534351451325444422395079 36801527176988166633592619)
          ·
            refine ⟨55202290765482249950388929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36801527176988166633592619 55202290765482249950388929)
            ·
              refine ⟨41401718074111687462791697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55202290765482249950388929 41401718074111687462791697)
              ·
                refine ⟨31051288555583765597093773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41401718074111687462791697 31051288555583765597093773)
                ·
                  refine ⟨11644233208343912098910165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31051288555583765597093773 11644233208343912098910165)
                  ·
                    refine ⟨272911715820560439818207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11644233208343912098910165 272911715820560439818207)
                    ·
                      rfl

theorem cell23_1594481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_1594481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594481 prefixEnd_1594481 := by exact prefixLift 1594481
  have htrace : WordTrace (prefixWord ++ tailWord_1594481) baseStart_1594481 baseEnd_1594481 := by
    simpa [prefixWord, tailWord_1594481, baseEnd_1594481] using wordTrace_append hprefix tailTrace_1594481
  have hstable : (prefixWord ++ tailWord_1594481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594481).length < 2 ^ (prefixWord ++ tailWord_1594481).sum := by decide
  have hdescent : baseEnd_1594481 < baseStart_1594481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594521 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1594521 : Nat := 118140960795 + 1594521 * 2 ^ 59
def prefixEnd_1594521 : Nat := 4983230072969 + 3 ^ 40 * 1594521 * 2
def baseEnd_1594521 : Nat := 818755686687861162954437

theorem tailTrace_1594521 : CollatzResearch.WordTrace tailWord_1594521 prefixEnd_1594521 818755686687861162954437 := by
  unfold tailWord_1594521
  simp only [CollatzResearch.WordTrace]
  refine ⟨58156958656330214351207417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38771305770886809567471611 58156958656330214351207417)
  ·
    refine ⟨43617718992247660763405563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58156958656330214351207417 43617718992247660763405563)
    ·
      refine ⟨65426578488371491145108345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43617718992247660763405563 65426578488371491145108345)
      ·
        refine ⟨49069933866278618358831259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65426578488371491145108345 49069933866278618358831259)
        ·
          refine ⟨73604900799417927538246889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49069933866278618358831259 73604900799417927538246889)
          ·
            refine ⟨55203675599563445653685167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73604900799417927538246889 55203675599563445653685167)
            ·
              refine ⟨82805513399345168480527751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55203675599563445653685167 82805513399345168480527751)
              ·
                refine ⟨124208270099017752720791627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82805513399345168480527751 124208270099017752720791627)
                ·
                  refine ⟨186312405148526629081187441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124208270099017752720791627 186312405148526629081187441)
                  ·
                    refine ⟨139734303861394971810890581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186312405148526629081187441 139734303861394971810890581)
                    ·
                      refine ⟨818755686687861162954437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 139734303861394971810890581 818755686687861162954437)
                      ·
                        rfl

theorem cell23_1594521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1594521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594521 prefixEnd_1594521 := by exact prefixLift 1594521
  have htrace : WordTrace (prefixWord ++ tailWord_1594521) baseStart_1594521 baseEnd_1594521 := by
    simpa [prefixWord, tailWord_1594521, baseEnd_1594521] using wordTrace_append hprefix tailTrace_1594521
  have hstable : (prefixWord ++ tailWord_1594521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594521).length < 2 ^ (prefixWord ++ tailWord_1594521).sum := by decide
  have hdescent : baseEnd_1594521 < baseStart_1594521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594585 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 3]
def baseStart_1594585 : Nat := 118140960795 + 1594585 * 2 ^ 59
def prefixEnd_1594585 : Nat := 4983230072969 + 3 ^ 40 * 1594585 * 2
def baseEnd_1594585 : Nat := 818788549449748912554143

theorem tailTrace_1594585 : CollatzResearch.WordTrace tailWord_1594585 prefixEnd_1594585 818788549449748912554143 := by
  unfold tailWord_1594585
  simp only [CollatzResearch.WordTrace]
  refine ⟨58159292928098353281537209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38772861952065568854358139 58159292928098353281537209)
  ·
    refine ⟨43619469696073764961152907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58159292928098353281537209 43619469696073764961152907)
    ·
      refine ⟨65429204544110647441729361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43619469696073764961152907 65429204544110647441729361)
      ·
        refine ⟨49071903408082985581297021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65429204544110647441729361 49071903408082985581297021)
        ·
          refine ⟨18401963778031119592986383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49071903408082985581297021 18401963778031119592986383)
          ·
            refine ⟨27602945667046679389479575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18401963778031119592986383 27602945667046679389479575)
            ·
              refine ⟨41404418500570019084219363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27602945667046679389479575 41404418500570019084219363)
              ·
                refine ⟨62106627750855028626329045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41404418500570019084219363 62106627750855028626329045)
                ·
                  refine ⟨1455624087910664733429587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62106627750855028626329045 1455624087910664733429587)
                  ·
                    refine ⟨2183436131865997100144381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455624087910664733429587 2183436131865997100144381)
                    ·
                      refine ⟨818788549449748912554143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183436131865997100144381 818788549449748912554143)
                      ·
                        rfl

theorem cell23_1594585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_1594585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594585 prefixEnd_1594585 := by exact prefixLift 1594585
  have htrace : WordTrace (prefixWord ++ tailWord_1594585) baseStart_1594585 baseEnd_1594585 := by
    simpa [prefixWord, tailWord_1594585, baseEnd_1594585] using wordTrace_append hprefix tailTrace_1594585
  have hstable : (prefixWord ++ tailWord_1594585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594585).length < 2 ^ (prefixWord ++ tailWord_1594585).sum := by decide
  have hdescent : baseEnd_1594585 < baseStart_1594585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594602 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1594602 : Nat := 118140960795 + 1594602 * 2 ^ 59
def prefixEnd_1594602 : Nat := 4983230072969 + 3 ^ 40 * 1594602 * 2
def baseEnd_1594602 : Nat := 818797278620875346041565

theorem tailTrace_1594602 : CollatzResearch.WordTrace tailWord_1594602 prefixEnd_1594602 818797278620875346041565 := by
  unfold tailWord_1594602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14539978242259191296226515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38773275312691176789937373 14539978242259191296226515)
  ·
    refine ⟨21809967363388786944339773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14539978242259191296226515 21809967363388786944339773)
    ·
      refine ⟨8178737761270795104127415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21809967363388786944339773 8178737761270795104127415)
      ·
        refine ⟨12268106641906192656191123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178737761270795104127415 12268106641906192656191123)
        ·
          refine ⟨18402159962859288984286685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268106641906192656191123 18402159962859288984286685)
          ·
            refine ⟨6900809986072233369107507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18402159962859288984286685 6900809986072233369107507)
            ·
              refine ⟨10351214979108350053661261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900809986072233369107507 10351214979108350053661261)
              ·
                refine ⟨3881705617165631270122973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10351214979108350053661261 3881705617165631270122973)
                ·
                  refine ⟨1455639606437111726296115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881705617165631270122973 1455639606437111726296115)
                  ·
                    refine ⟨2183459409655667589444173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455639606437111726296115 2183459409655667589444173)
                    ·
                      refine ⟨818797278620875346041565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183459409655667589444173 818797278620875346041565)
                      ·
                        rfl

theorem cell23_1594602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1594602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594602 prefixEnd_1594602 := by exact prefixLift 1594602
  have htrace : WordTrace (prefixWord ++ tailWord_1594602) baseStart_1594602 baseEnd_1594602 := by
    simpa [prefixWord, tailWord_1594602, baseEnd_1594602] using wordTrace_append hprefix tailTrace_1594602
  have hstable : (prefixWord ++ tailWord_1594602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594602).length < 2 ^ (prefixWord ++ tailWord_1594602).sum := by decide
  have hdescent : baseEnd_1594602 < baseStart_1594602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594622 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1594622 : Nat := 118140960795 + 1594622 * 2 ^ 59
def prefixEnd_1594622 : Nat := 4983230072969 + 3 ^ 40 * 1594622 * 2
def baseEnd_1594622 : Nat := 272935849411321755930491

theorem tailTrace_1594622 : CollatzResearch.WordTrace tailWord_1594622 prefixEnd_1594622 272935849411321755930491 := by
  unfold tailWord_1594622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270080303620538575079265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38773761619309539067089413 7270080303620538575079265)
  ·
    refine ⟨5452560227715403931309449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7270080303620538575079265 5452560227715403931309449)
    ·
      refine ⟨4089420170786552948482087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5452560227715403931309449 4089420170786552948482087)
      ·
        refine ⟨6134130256179829422723131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089420170786552948482087 6134130256179829422723131)
        ·
          refine ⟨9201195384269744134084697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134130256179829422723131 9201195384269744134084697)
          ·
            refine ⟨6900896538202308100563523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9201195384269744134084697 6900896538202308100563523)
            ·
              refine ⟨10351344807303462150845285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900896538202308100563523 10351344807303462150845285)
              ·
                refine ⟨1940877151369399153283491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10351344807303462150845285 1940877151369399153283491)
                ·
                  refine ⟨2911315727054098729925237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940877151369399153283491 2911315727054098729925237)
                  ·
                    refine ⟨272935849411321755930491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2911315727054098729925237 272935849411321755930491)
                    ·
                      rfl

theorem cell23_1594622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1594622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594622 prefixEnd_1594622 := by exact prefixLift 1594622
  have htrace : WordTrace (prefixWord ++ tailWord_1594622) baseStart_1594622 baseEnd_1594622 := by
    simpa [prefixWord, tailWord_1594622, baseEnd_1594622] using wordTrace_append hprefix tailTrace_1594622
  have hstable : (prefixWord ++ tailWord_1594622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594622).length < 2 ^ (prefixWord ++ tailWord_1594622).sum := by decide
  have hdescent : baseEnd_1594622 < baseStart_1594622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594635 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 4, 4]
def baseStart_1594635 : Nat := 118140960795 + 1594635 * 2 ^ 59
def prefixEnd_1594635 : Nat := 4983230072969 + 3 ^ 40 * 1594635 * 2
def baseEnd_1594635 : Nat := 272938074494157905642971

theorem tailTrace_1594635 : CollatzResearch.WordTrace tailWord_1594635 prefixEnd_1594635 272938074494157905642971 := by
  unfold tailWord_1594635
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161116577917211820857359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38774077718611474547238239 58161116577917211820857359)
  ·
    refine ⟨87241674866875817731286039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58161116577917211820857359 87241674866875817731286039)
    ·
      refine ⟨130862512300313726596929059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87241674866875817731286039 130862512300313726596929059)
      ·
        refine ⟨196293768450470589895393589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130862512300313726596929059 196293768450470589895393589)
        ·
          refine ⟨18402540792231617802693149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196293768450470589895393589 18402540792231617802693149)
          ·
            refine ⟨6900952797086856676009931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18402540792231617802693149 6900952797086856676009931)
            ·
              refine ⟨10351429195630285014014897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900952797086856676009931 10351429195630285014014897)
              ·
                refine ⟨7763571896722713760511173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10351429195630285014014897 7763571896722713760511173)
                ·
                  refine ⟨1455669730635508830095845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7763571896722713760511173 1455669730635508830095845)
                  ·
                    refine ⟨272938074494157905642971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1455669730635508830095845 272938074494157905642971)
                    ·
                      rfl

theorem cell23_1594635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 4].length) (baseStart_1594635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594635 prefixEnd_1594635 := by exact prefixLift 1594635
  have htrace : WordTrace (prefixWord ++ tailWord_1594635) baseStart_1594635 baseEnd_1594635 := by
    simpa [prefixWord, tailWord_1594635, baseEnd_1594635] using wordTrace_append hprefix tailTrace_1594635
  have hstable : (prefixWord ++ tailWord_1594635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594635).length < 2 ^ (prefixWord ++ tailWord_1594635).sum := by decide
  have hdescent : baseEnd_1594635 < baseStart_1594635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594636 : List Nat := [2, 2, 1, 2, 2, 5, 1, 3, 1, 1, 3]
def baseStart_1594636 : Nat := 118140960795 + 1594636 * 2 ^ 59
def prefixEnd_1594636 : Nat := 4983230072969 + 3 ^ 40 * 1594636 * 2
def baseEnd_1594636 : Nat := 818814736963128213016409

theorem tailTrace_1594636 : CollatzResearch.WordTrace tailWord_1594636 prefixEnd_1594636 818814736963128213016409 := by
  unfold tailWord_1594636
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080576525456794495821881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38774102033942392661095841 29080576525456794495821881)
  ·
    refine ⟨21810432394092595871866411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29080576525456794495821881 21810432394092595871866411)
    ·
      refine ⟨32715648591138893807799617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21810432394092595871866411 32715648591138893807799617)
      ·
        refine ⟨24536736443354170355849713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32715648591138893807799617 24536736443354170355849713)
        ·
          refine ⟨18402552332515627766887285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24536736443354170355849713 18402552332515627766887285)
          ·
            refine ⟨1725239281173340103145683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18402552332515627766887285 1725239281173340103145683)
            ·
              refine ⟨2587858921760010154718525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725239281173340103145683 2587858921760010154718525)
              ·
                refine ⟨970447095660003808019447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2587858921760010154718525 970447095660003808019447)
                ·
                  refine ⟨1455670643490005712029171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970447095660003808019447 1455670643490005712029171)
                  ·
                    refine ⟨2183505965235008568043757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455670643490005712029171 2183505965235008568043757)
                    ·
                      refine ⟨818814736963128213016409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183505965235008568043757 818814736963128213016409)
                      ·
                        rfl

theorem cell23_1594636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_1594636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594636 prefixEnd_1594636 := by exact prefixLift 1594636
  have htrace : WordTrace (prefixWord ++ tailWord_1594636) baseStart_1594636 baseEnd_1594636 := by
    simpa [prefixWord, tailWord_1594636, baseEnd_1594636] using wordTrace_append hprefix tailTrace_1594636
  have hstable : (prefixWord ++ tailWord_1594636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594636).length < 2 ^ (prefixWord ++ tailWord_1594636).sum := by decide
  have hdescent : baseEnd_1594636 < baseStart_1594636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594645 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_1594645 : Nat := 118140960795 + 1594645 * 2 ^ 59
def prefixEnd_1594645 : Nat := 4983230072969 + 3 ^ 40 * 1594645 * 2
def baseEnd_1594645 : Nat := 818819358289018677803867

theorem tailTrace_1594645 : CollatzResearch.WordTrace tailWord_1594645 prefixEnd_1594645 818819358289018677803867 := by
  unfold tailWord_1594645
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161481307880983528721389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38774320871920655685814259 58161481307880983528721389)
  ·
    refine ⟨21810555490455368823270521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58161481307880983528721389 21810555490455368823270521)
    ·
      refine ⟨16357916617841526617452891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21810555490455368823270521 16357916617841526617452891)
      ·
        refine ⟨24536874926762289926179337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357916617841526617452891 24536874926762289926179337)
        ·
          refine ⟨18402656195071717444634503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24536874926762289926179337 18402656195071717444634503)
          ·
            refine ⟨27603984292607576166951755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18402656195071717444634503 27603984292607576166951755)
            ·
              refine ⟨41405976438911364250427633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27603984292607576166951755 41405976438911364250427633)
              ·
                refine ⟨31054482329183523187820725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41405976438911364250427633 31054482329183523187820725)
                ·
                  refine ⟨2911357718360955298858193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31054482329183523187820725 2911357718360955298858193)
                  ·
                    refine ⟨2183518288770716474143645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2911357718360955298858193 2183518288770716474143645)
                    ·
                      refine ⟨818819358289018677803867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183518288770716474143645 818819358289018677803867)
                      ·
                        rfl

theorem cell23_1594645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_1594645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594645 prefixEnd_1594645 := by exact prefixLift 1594645
  have htrace : WordTrace (prefixWord ++ tailWord_1594645) baseStart_1594645 baseEnd_1594645 := by
    simpa [prefixWord, tailWord_1594645, baseEnd_1594645] using wordTrace_append hprefix tailTrace_1594645
  have hstable : (prefixWord ++ tailWord_1594645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594645).length < 2 ^ (prefixWord ++ tailWord_1594645).sum := by decide
  have hdescent : baseEnd_1594645 < baseStart_1594645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594648 : List Nat := [2, 1, 2, 3, 1, 3, 11]
def baseStart_1594648 : Nat := 118140960795 + 1594648 * 2 ^ 59
def prefixEnd_1594648 : Nat := 4983230072969 + 3 ^ 40 * 1594648 * 2
def baseEnd_1594648 : Nat := 10108899984333113161313

theorem tailTrace_1594648 : CollatzResearch.WordTrace tailWord_1594648 prefixEnd_1594648 10108899984333113161313 := by
  unfold tailWord_1594648
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080795363435057520540299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38774393817913410027387065 29080795363435057520540299)
  ·
    refine ⟨43621193045152586280810449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29080795363435057520540299 43621193045152586280810449)
    ·
      refine ⟨32715894783864439710607837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43621193045152586280810449 32715894783864439710607837)
      ·
        refine ⟨12268460543949164891477939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32715894783864439710607837 12268460543949164891477939)
        ·
          refine ⟨18402690815923747337216909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268460543949164891477939 18402690815923747337216909)
          ·
            refine ⟨6901009055971405251456341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18402690815923747337216909 6901009055971405251456341)
            ·
              refine ⟨10108899984333113161313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6901009055971405251456341 10108899984333113161313)
              ·
                rfl

theorem cell23_1594648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 11].length) (baseStart_1594648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594648 prefixEnd_1594648 := by exact prefixLift 1594648
  have htrace : WordTrace (prefixWord ++ tailWord_1594648) baseStart_1594648 baseEnd_1594648 := by
    simpa [prefixWord, tailWord_1594648, baseEnd_1594648] using wordTrace_append hprefix tailTrace_1594648
  have hstable : (prefixWord ++ tailWord_1594648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594648).length < 2 ^ (prefixWord ++ tailWord_1594648).sum := by decide
  have hdescent : baseEnd_1594648 < baseStart_1594648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594653 : List Nat := [1, 4, 2, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_1594653 : Nat := 118140960795 + 1594653 * 2 ^ 59
def prefixEnd_1594653 : Nat := 4983230072969 + 3 ^ 40 * 1594653 * 2
def baseEnd_1594653 : Nat := 818823466134254646503831

theorem tailTrace_1594653 : CollatzResearch.WordTrace tailWord_1594653 prefixEnd_1594653 818823466134254646503831 := by
  unfold tailWord_1594653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161773091852000895012613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38774515394568000596675075 58161773091852000895012613)
  ·
    refine ⟨10905332454722250167814865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58161773091852000895012613 10905332454722250167814865)
    ·
      refine ⟨8178999341041687625861149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10905332454722250167814865 8178999341041687625861149)
      ·
        refine ⟨3067124752890632859697931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8178999341041687625861149 3067124752890632859697931)
        ·
          refine ⟨4600687129335949289546897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067124752890632859697931 4600687129335949289546897)
          ·
            refine ⟨3450515347001961967160173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600687129335949289546897 3450515347001961967160173)
            ·
              refine ⟨1293943255125735737685065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450515347001961967160173 1293943255125735737685065)
              ·
                refine ⟨970457441344301803263799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293943255125735737685065 970457441344301803263799)
                ·
                  refine ⟨1455686162016452704895699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970457441344301803263799 1455686162016452704895699)
                  ·
                    refine ⟨2183529243024679057343549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455686162016452704895699 2183529243024679057343549)
                    ·
                      refine ⟨818823466134254646503831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183529243024679057343549 818823466134254646503831)
                      ·
                        rfl

theorem cell23_1594653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_1594653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594653 prefixEnd_1594653 := by exact prefixLift 1594653
  have htrace : WordTrace (prefixWord ++ tailWord_1594653) baseStart_1594653 baseEnd_1594653 := by
    simpa [prefixWord, tailWord_1594653, baseEnd_1594653] using wordTrace_append hprefix tailTrace_1594653
  have hstable : (prefixWord ++ tailWord_1594653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594653).length < 2 ^ (prefixWord ++ tailWord_1594653).sum := by decide
  have hdescent : baseEnd_1594653 < baseStart_1594653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594659 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 3, 2, 2]
def baseStart_1594659 : Nat := 118140960795 + 1594659 * 2 ^ 59
def prefixEnd_1594659 : Nat := 4983230072969 + 3 ^ 40 * 1594659 * 2
def baseEnd_1594659 : Nat := 818826547018181623028803

theorem tailTrace_1594659 : CollatzResearch.WordTrace tailWord_1594659 prefixEnd_1594659 818826547018181623028803 := by
  unfold tailWord_1594659
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161991929830263919731031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38774661286553509279820687 58161991929830263919731031)
  ·
    refine ⟨87242987894745395879596547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58161991929830263919731031 87242987894745395879596547)
    ·
      refine ⟨130864481842118093819394821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87242987894745395879596547 130864481842118093819394821)
      ·
        refine ⟨24537090345397142591136529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130864481842118093819394821 24537090345397142591136529)
        ·
          refine ⟨18402817759047856943352397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24537090345397142591136529 18402817759047856943352397)
          ·
            refine ⟨6901056659642946353757149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18402817759047856943352397 6901056659642946353757149)
            ·
              refine ⟨2587896247366104882658931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6901056659642946353757149 2587896247366104882658931)
              ·
                refine ⟨3881844371049157323988397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587896247366104882658931 3881844371049157323988397)
                ·
                  refine ⟨1455691639143433996495649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881844371049157323988397 1455691639143433996495649)
                  ·
                    refine ⟨1091768729357575497371737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455691639143433996495649 1091768729357575497371737)
                    ·
                      refine ⟨818826547018181623028803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091768729357575497371737 818826547018181623028803)
                      ·
                        rfl

theorem cell23_1594659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_1594659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594659 prefixEnd_1594659 := by exact prefixLift 1594659
  have htrace : WordTrace (prefixWord ++ tailWord_1594659) baseStart_1594659 baseEnd_1594659 := by
    simpa [prefixWord, tailWord_1594659, baseEnd_1594659] using wordTrace_append hprefix tailTrace_1594659
  have hstable : (prefixWord ++ tailWord_1594659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594659).length < 2 ^ (prefixWord ++ tailWord_1594659).sum := by decide
  have hdescent : baseEnd_1594659 < baseStart_1594659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594668 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1594668 : Nat := 118140960795 + 1594668 * 2 ^ 59
def prefixEnd_1594668 : Nat := 4983230072969 + 3 ^ 40 * 1594668 * 2
def baseEnd_1594668 : Nat := 818831168344072087816261

theorem tailTrace_1594668 : CollatzResearch.WordTrace tailWord_1594668 prefixEnd_1594668 818831168344072087816261 := by
  unfold tailWord_1594668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29081160093398829228404329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38774880124531772304539105 29081160093398829228404329)
  ·
    refine ⟨21810870070049121921303247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29081160093398829228404329 21810870070049121921303247)
    ·
      refine ⟨32716305105073682881954871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21810870070049121921303247 32716305105073682881954871)
      ·
        refine ⟨49074457657610524322932307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32716305105073682881954871 49074457657610524322932307)
        ·
          refine ⟨73611686486415786484398461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49074457657610524322932307 73611686486415786484398461)
          ·
            refine ⟨27604382432405919931649423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73611686486415786484398461 27604382432405919931649423)
            ·
              refine ⟨41406573648608879897474135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27604382432405919931649423 41406573648608879897474135)
              ·
                refine ⟨62109860472913319846211203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41406573648608879897474135 62109860472913319846211203)
                ·
                  refine ⟨93164790709369979769316805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62109860472913319846211203 93164790709369979769316805)
                  ·
                    refine ⟨17468398258006871206746901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93164790709369979769316805 17468398258006871206746901)
                    ·
                      refine ⟨818831168344072087816261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17468398258006871206746901 818831168344072087816261)
                      ·
                        rfl

theorem cell23_1594668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1594668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594668 prefixEnd_1594668 := by exact prefixLift 1594668
  have htrace : WordTrace (prefixWord ++ tailWord_1594668) baseStart_1594668 baseEnd_1594668 := by
    simpa [prefixWord, tailWord_1594668, baseEnd_1594668] using wordTrace_append hprefix tailTrace_1594668
  have hstable : (prefixWord ++ tailWord_1594668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594668).length < 2 ^ (prefixWord ++ tailWord_1594668).sum := by decide
  have hdescent : baseEnd_1594668 < baseStart_1594668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594709 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1594709 : Nat := 118140960795 + 1594709 * 2 ^ 59
def prefixEnd_1594709 : Nat := 4983230072969 + 3 ^ 40 * 1594709 * 2
def baseEnd_1594709 : Nat := 818852221050906427403573

theorem tailTrace_1594709 : CollatzResearch.WordTrace tailWord_1594709 prefixEnd_1594709 818852221050906427403573 := by
  unfold tailWord_1594709
  simp only [CollatzResearch.WordTrace]
  refine ⟨58163815579649122459051181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38775877053099414972700787 58163815579649122459051181)
  ·
    refine ⟨21811430842368420922144193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58163815579649122459051181 21811430842368420922144193)
    ·
      refine ⟨16358573131776315691608145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21811430842368420922144193 16358573131776315691608145)
      ·
        refine ⟨12268929848832236768706109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16358573131776315691608145 12268929848832236768706109)
        ·
          refine ⟨4600848693312088788264791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12268929848832236768706109 4600848693312088788264791)
          ·
            refine ⟨6901273039968133182397187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600848693312088788264791 6901273039968133182397187)
            ·
              refine ⟨10351909559952199773595781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901273039968133182397187 10351909559952199773595781)
              ·
                refine ⟨1940983042491037457549209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10351909559952199773595781 1940983042491037457549209)
                ·
                  refine ⟨1455737281868278093161907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1940983042491037457549209 1455737281868278093161907)
                  ·
                    refine ⟨2183605922802417139742861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455737281868278093161907 2183605922802417139742861)
                    ·
                      refine ⟨818852221050906427403573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183605922802417139742861 818852221050906427403573)
                      ·
                        rfl

theorem cell23_1594709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1594709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594709 prefixEnd_1594709 := by exact prefixLift 1594709
  have htrace : WordTrace (prefixWord ++ tailWord_1594709) baseStart_1594709 baseEnd_1594709 := by
    simpa [prefixWord, tailWord_1594709, baseEnd_1594709] using wordTrace_append hprefix tailTrace_1594709
  have hstable : (prefixWord ++ tailWord_1594709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594709).length < 2 ^ (prefixWord ++ tailWord_1594709).sum := by decide
  have hdescent : baseEnd_1594709 < baseStart_1594709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594725 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_1594725 : Nat := 118140960795 + 1594725 * 2 ^ 59
def prefixEnd_1594725 : Nat := 4983230072969 + 3 ^ 40 * 1594725 * 2
def baseEnd_1594725 : Nat := 272953478913792788267833

theorem tailTrace_1594725 : CollatzResearch.WordTrace tailWord_1594725 prefixEnd_1594725 272953478913792788267833 := by
  unfold tailWord_1594725
  simp only [CollatzResearch.WordTrace]
  refine ⟨58164399147591157191633629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38776266098394104794422419 58164399147591157191633629)
  ·
    refine ⟨21811649680346683946862611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58164399147591157191633629 21811649680346683946862611)
    ·
      refine ⟨32717474520520025920293917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21811649680346683946862611 32717474520520025920293917)
      ·
        refine ⟨12269052945195009720110219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32717474520520025920293917 12269052945195009720110219)
        ·
          refine ⟨18403579417792514580165329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12269052945195009720110219 18403579417792514580165329)
          ·
            refine ⟨13802684563344385935123997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18403579417792514580165329 13802684563344385935123997)
            ·
              refine ⟨5176006711254144725671499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13802684563344385935123997 5176006711254144725671499)
              ·
                refine ⟨7764010066881217088507249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176006711254144725671499 7764010066881217088507249)
                ·
                  refine ⟨5823007550160912816380437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7764010066881217088507249 5823007550160912816380437)
                  ·
                    refine ⟨272953478913792788267833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5823007550160912816380437 272953478913792788267833)
                    ·
                      rfl

theorem cell23_1594725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_1594725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594725 prefixEnd_1594725 := by exact prefixLift 1594725
  have htrace : WordTrace (prefixWord ++ tailWord_1594725) baseStart_1594725 baseEnd_1594725 := by
    simpa [prefixWord, tailWord_1594725, baseEnd_1594725] using wordTrace_append hprefix tailTrace_1594725
  have hstable : (prefixWord ++ tailWord_1594725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594725).length < 2 ^ (prefixWord ++ tailWord_1594725).sum := by decide
  have hdescent : baseEnd_1594725 < baseStart_1594725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594735 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_1594735 : Nat := 118140960795 + 1594735 * 2 ^ 59
def prefixEnd_1594735 : Nat := 4983230072969 + 3 ^ 40 * 1594735 * 2
def baseEnd_1594735 : Nat := 818865571547923325678453

theorem tailTrace_1594735 : CollatzResearch.WordTrace tailWord_1594735 prefixEnd_1594735 818865571547923325678453 := by
  unfold tailWord_1594735
  simp only [CollatzResearch.WordTrace]
  refine ⟨58164763877554928899497659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38776509251703285932998439 58164763877554928899497659)
  ·
    refine ⟨87247145816332393349246489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58164763877554928899497659 87247145816332393349246489)
    ·
      refine ⟨65435359362249295011934867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87247145816332393349246489 65435359362249295011934867)
      ·
        refine ⟨98153039043373942517902301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65435359362249295011934867 98153039043373942517902301)
        ·
          refine ⟨36807389641265228444213363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98153039043373942517902301 36807389641265228444213363)
          ·
            refine ⟨55211084461897842666320045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36807389641265228444213363 55211084461897842666320045)
            ·
              refine ⟨20704156673211690999870017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55211084461897842666320045 20704156673211690999870017)
              ·
                refine ⟨15528117504908768249902513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20704156673211690999870017 15528117504908768249902513)
                ·
                  refine ⟨11646088128681576187426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15528117504908768249902513 11646088128681576187426885)
                  ·
                    refine ⟨2183641524127795535142541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11646088128681576187426885 2183641524127795535142541)
                    ·
                      refine ⟨818865571547923325678453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183641524127795535142541 818865571547923325678453)
                      ·
                        rfl

theorem cell23_1594735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_1594735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594735 prefixEnd_1594735 := by exact prefixLift 1594735
  have htrace : WordTrace (prefixWord ++ tailWord_1594735) baseStart_1594735 baseEnd_1594735 := by
    simpa [prefixWord, tailWord_1594735, baseEnd_1594735] using wordTrace_append hprefix tailTrace_1594735
  have hstable : (prefixWord ++ tailWord_1594735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594735).length < 2 ^ (prefixWord ++ tailWord_1594735).sum := by decide
  have hdescent : baseEnd_1594735 < baseStart_1594735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594749 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_1594749 : Nat := 118140960795 + 1594749 * 2 ^ 59
def prefixEnd_1594749 : Nat := 4983230072969 + 3 ^ 40 * 1594749 * 2
def baseEnd_1594749 : Nat := 818872760277086270903389

theorem tailTrace_1594749 : CollatzResearch.WordTrace tailWord_1594749 prefixEnd_1594749 818872760277086270903389 := by
  unfold tailWord_1594749
  simp only [CollatzResearch.WordTrace]
  refine ⟨58165274499504209290507301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38776849666336139527004867 58165274499504209290507301)
  ·
    refine ⟨10905988968657039241970119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58165274499504209290507301 10905988968657039241970119)
    ·
      refine ⟨16358983452985558862955179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905988968657039241970119 16358983452985558862955179)
      ·
        refine ⟨24538475179478338294432769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16358983452985558862955179 24538475179478338294432769)
        ·
          refine ⟨18403856384608753720824577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24538475179478338294432769 18403856384608753720824577)
          ·
            refine ⟨13802892288456565290618433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18403856384608753720824577 13802892288456565290618433)
            ·
              refine ⟨10352169216342423967963825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13802892288456565290618433 10352169216342423967963825)
              ·
                refine ⟨7764126912256817975972869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10352169216342423967963825 7764126912256817975972869)
                ·
                  refine ⟨1455773796048153370494913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7764126912256817975972869 1455773796048153370494913)
                  ·
                    refine ⟨1091830347036115027871185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455773796048153370494913 1091830347036115027871185)
                    ·
                      refine ⟨818872760277086270903389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091830347036115027871185 818872760277086270903389)
                      ·
                        rfl

theorem cell23_1594749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_1594749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594749 prefixEnd_1594749 := by exact prefixLift 1594749
  have htrace : WordTrace (prefixWord ++ tailWord_1594749) baseStart_1594749 baseEnd_1594749 := by
    simpa [prefixWord, tailWord_1594749, baseEnd_1594749] using wordTrace_append hprefix tailTrace_1594749
  have hstable : (prefixWord ++ tailWord_1594749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594749).length < 2 ^ (prefixWord ++ tailWord_1594749).sum := by decide
  have hdescent : baseEnd_1594749 < baseStart_1594749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594772 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 7]
def baseStart_1594772 : Nat := 118140960795 + 1594772 * 2 ^ 59
def prefixEnd_1594772 : Nat := 4983230072969 + 3 ^ 40 * 1594772 * 2
def baseEnd_1594772 : Nat := 90987174481348853435087

theorem tailTrace_1594772 : CollatzResearch.WordTrace tailWord_1594772 prefixEnd_1594772 90987174481348853435087 := by
  unfold tailWord_1594772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29083056689210442109297285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38777408918947256145729713 29083056689210442109297285)
  ·
    refine ⟨5453073129226957895493241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29083056689210442109297285 5453073129226957895493241)
    ·
      refine ⟨4089804846920218421619931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5453073129226957895493241 4089804846920218421619931)
      ·
        refine ⟨6134707270380327632429897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089804846920218421619931 6134707270380327632429897)
        ·
          refine ⟨4601030452785245724322423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6134707270380327632429897 4601030452785245724322423)
          ·
            refine ⟨6901545679177868586483635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601030452785245724322423 6901545679177868586483635)
            ·
              refine ⟨10352318518766802879725453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901545679177868586483635 10352318518766802879725453)
              ·
                refine ⟨3882119444537551079897045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10352318518766802879725453 3882119444537551079897045)
                ·
                  refine ⟨90987174481348853435087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3882119444537551079897045 90987174481348853435087)
                  ·
                    rfl

theorem cell23_1594772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_1594772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594772 prefixEnd_1594772 := by exact prefixLift 1594772
  have htrace : WordTrace (prefixWord ++ tailWord_1594772) baseStart_1594772 baseEnd_1594772 := by
    simpa [prefixWord, tailWord_1594772, baseEnd_1594772] using wordTrace_append hprefix tailTrace_1594772
  have hstable : (prefixWord ++ tailWord_1594772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594772).length < 2 ^ (prefixWord ++ tailWord_1594772).sum := by decide
  have hdescent : baseEnd_1594772 < baseStart_1594772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594783 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1594783 : Nat := 118140960795 + 1594783 * 2 ^ 59
def prefixEnd_1594783 : Nat := 4983230072969 + 3 ^ 40 * 1594783 * 2
def baseEnd_1594783 : Nat := 818890218619339137878233

theorem tailTrace_1594783 : CollatzResearch.WordTrace tailWord_1594783 prefixEnd_1594783 818890218619339137878233 := by
  unfold tailWord_1594783
  simp only [CollatzResearch.WordTrace]
  refine ⟨58166514581381033097245003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38777676387587355398163335 58166514581381033097245003)
  ·
    refine ⟨87249771872071549645867505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58166514581381033097245003 87249771872071549645867505)
    ·
      refine ⟨65437328904053662234400629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87249771872071549645867505 65437328904053662234400629)
      ·
        refine ⟨6134749584755030834475059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65437328904053662234400629 6134749584755030834475059)
        ·
          refine ⟨9202124377132546251712589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134749584755030834475059 9202124377132546251712589)
          ·
            refine ⟨3450796641424704844392221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9202124377132546251712589 3450796641424704844392221)
            ·
              refine ⟨1294048740534264316647083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450796641424704844392221 1294048740534264316647083)
              ·
                refine ⟨1941073110801396474970625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294048740534264316647083 1941073110801396474970625)
                ·
                  refine ⟨1455804833101047356227969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1941073110801396474970625 1455804833101047356227969)
                  ·
                    refine ⟨1091853624825785517170977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455804833101047356227969 1091853624825785517170977)
                    ·
                      refine ⟨818890218619339137878233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091853624825785517170977 818890218619339137878233)
                      ·
                        rfl

theorem cell23_1594783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1594783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594783 prefixEnd_1594783 := by exact prefixLift 1594783
  have htrace : WordTrace (prefixWord ++ tailWord_1594783) baseStart_1594783 baseEnd_1594783 := by
    simpa [prefixWord, tailWord_1594783, baseEnd_1594783] using wordTrace_append hprefix tailTrace_1594783
  have hstable : (prefixWord ++ tailWord_1594783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594783).length < 2 ^ (prefixWord ++ tailWord_1594783).sum := by decide
  have hdescent : baseEnd_1594783 < baseStart_1594783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594889 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 3]
def baseStart_1594889 : Nat := 118140960795 + 1594889 * 2 ^ 59
def prefixEnd_1594889 : Nat := 4983230072969 + 3 ^ 40 * 1594889 * 2
def baseEnd_1594889 : Nat := 818944647568715723152745

theorem tailTrace_1594889 : CollatzResearch.WordTrace tailWord_1594889 prefixEnd_1594889 818944647568715723152745 := by
  unfold tailWord_1594889
  simp only [CollatzResearch.WordTrace]
  refine ⟨58170380718997013200603721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38780253812664675467069147 58170380718997013200603721)
  ·
    refine ⟨43627785539247759900452791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58170380718997013200603721 43627785539247759900452791)
    ·
      refine ⟨65441678308871639850679187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43627785539247759900452791 65441678308871639850679187)
      ·
        refine ⟨98162517463307459776018781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65441678308871639850679187 98162517463307459776018781)
        ·
          refine ⟨36810944048740297416007043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98162517463307459776018781 36810944048740297416007043)
          ·
            refine ⟨55216416073110446124010565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36810944048740297416007043 55216416073110446124010565)
            ·
              refine ⟨10353078013708208648251981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55216416073110446124010565 10353078013708208648251981)
              ·
                refine ⟨3882404255140578243094493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10353078013708208648251981 3882404255140578243094493)
                ·
                  refine ⟨1455901595677716841160435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3882404255140578243094493 1455901595677716841160435)
                  ·
                    refine ⟨2183852393516575261740653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1455901595677716841160435 2183852393516575261740653)
                    ·
                      refine ⟨818944647568715723152745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183852393516575261740653 818944647568715723152745)
                      ·
                        rfl

theorem cell23_1594889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_1594889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594889 prefixEnd_1594889 := by exact prefixLift 1594889
  have htrace : WordTrace (prefixWord ++ tailWord_1594889) baseStart_1594889 baseEnd_1594889 := by
    simpa [prefixWord, tailWord_1594889, baseEnd_1594889] using wordTrace_append hprefix tailTrace_1594889
  have hstable : (prefixWord ++ tailWord_1594889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594889).length < 2 ^ (prefixWord ++ tailWord_1594889).sum := by decide
  have hdescent : baseEnd_1594889 < baseStart_1594889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594909 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1594909 : Nat := 118140960795 + 1594909 * 2 ^ 59
def prefixEnd_1594909 : Nat := 4983230072969 + 3 ^ 40 * 1594909 * 2
def baseEnd_1594909 : Nat := 272984972393935214967551

theorem tailTrace_1594909 : CollatzResearch.WordTrace tailWord_1594909 prefixEnd_1594909 272984972393935214967551 := by
  unfold tailWord_1594909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58171110178924556616331781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38780740119283037744221187 58171110178924556616331781)
  ·
    refine ⟨10907083158548354365562209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58171110178924556616331781 10907083158548354365562209)
    ·
      refine ⟨8180312368911265774171657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10907083158548354365562209 8180312368911265774171657)
      ·
        refine ⟨6135234276683449330628743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8180312368911265774171657 6135234276683449330628743)
        ·
          refine ⟨9202851415025173995943115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135234276683449330628743 9202851415025173995943115)
          ·
            refine ⟨13804277122537760993914673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9202851415025173995943115 13804277122537760993914673)
            ·
              refine ⟨10353207841903320745436005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13804277122537760993914673 10353207841903320745436005)
              ·
                refine ⟨1941226470356872639769251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10353207841903320745436005 1941226470356872639769251)
                ·
                  refine ⟨2911839705535308959653877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941226470356872639769251 2911839705535308959653877)
                  ·
                    refine ⟨272984972393935214967551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2911839705535308959653877 272984972393935214967551)
                    ·
                      rfl

theorem cell23_1594909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1594909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594909 prefixEnd_1594909 := by exact prefixLift 1594909
  have htrace : WordTrace (prefixWord ++ tailWord_1594909) baseStart_1594909 baseEnd_1594909 := by
    simpa [prefixWord, tailWord_1594909, baseEnd_1594909] using wordTrace_append hprefix tailTrace_1594909
  have hstable : (prefixWord ++ tailWord_1594909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594909).length < 2 ^ (prefixWord ++ tailWord_1594909).sum := by decide
  have hdescent : baseEnd_1594909 < baseStart_1594909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594910 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1594910 : Nat := 118140960795 + 1594910 * 2 ^ 59
def prefixEnd_1594910 : Nat := 4983230072969 + 3 ^ 40 * 1594910 * 2
def baseEnd_1594910 : Nat := 818955430662460140990149

theorem tailTrace_1594910 : CollatzResearch.WordTrace tailWord_1594910 prefixEnd_1594910 818955430662460140990149 := by
  unfold tailWord_1594910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271393331490116723389773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38780764434613955858078789 7271393331490116723389773)
  ·
    refine ⟨2726772499308793771271165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7271393331490116723389773 2726772499308793771271165)
    ·
      refine ⟨1022539687240797664226687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2726772499308793771271165 1022539687240797664226687)
      ·
        refine ⟨1533809530861196496340031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022539687240797664226687 1533809530861196496340031)
        ·
          refine ⟨2300714296291794744510047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533809530861196496340031 2300714296291794744510047)
          ·
            refine ⟨3451071444437692116765071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300714296291794744510047 3451071444437692116765071)
            ·
              refine ⟨5176607166656538175147607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451071444437692116765071 5176607166656538175147607)
              ·
                refine ⟨7764910749984807262721411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176607166656538175147607 7764910749984807262721411)
                ·
                  refine ⟨11647366124977210894082117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7764910749984807262721411 11647366124977210894082117)
                  ·
                    refine ⟨2183881148433227042640397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11647366124977210894082117 2183881148433227042640397)
                    ·
                      refine ⟨818955430662460140990149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2183881148433227042640397 818955430662460140990149)
                      ·
                        rfl

theorem cell23_1594910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1594910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594910 prefixEnd_1594910 := by exact prefixLift 1594910
  have htrace : WordTrace (prefixWord ++ tailWord_1594910) baseStart_1594910 baseEnd_1594910 := by
    simpa [prefixWord, tailWord_1594910, baseEnd_1594910] using wordTrace_append hprefix tailTrace_1594910
  have hstable : (prefixWord ++ tailWord_1594910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594910).length < 2 ^ (prefixWord ++ tailWord_1594910).sum := by decide
  have hdescent : baseEnd_1594910 < baseStart_1594910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594926 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1594926 : Nat := 118140960795 + 1594926 * 2 ^ 59
def prefixEnd_1594926 : Nat := 4983230072969 + 3 ^ 40 * 1594926 * 2
def baseEnd_1594926 : Nat := 272987882117644026130025

theorem tailTrace_1594926 : CollatzResearch.WordTrace tailWord_1594926 prefixEnd_1594926 272987882117644026130025 := by
  unfold tailWord_1594926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271466277482871064962579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38781153479908645679800421 7271466277482871064962579)
  ·
    refine ⟨10907199416224306597443869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7271466277482871064962579 10907199416224306597443869)
    ·
      refine ⟨4090199781084114974041451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10907199416224306597443869 4090199781084114974041451)
      ·
        refine ⟨6135299671626172461062177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090199781084114974041451 6135299671626172461062177)
        ·
          refine ⟨4601474753719629345796633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135299671626172461062177 4601474753719629345796633)
          ·
            refine ⟨3451106065289722009347475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601474753719629345796633 3451106065289722009347475)
            ·
              refine ⟨5176659097934583014021213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451106065289722009347475 5176659097934583014021213)
              ·
                refine ⟨1941247161725468630257955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5176659097934583014021213 1941247161725468630257955)
                ·
                  refine ⟨2911870742588202945386933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941247161725468630257955 2911870742588202945386933)
                  ·
                    refine ⟨272987882117644026130025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2911870742588202945386933 272987882117644026130025)
                    ·
                      rfl

theorem cell23_1594926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1594926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594926 prefixEnd_1594926 := by exact prefixLift 1594926
  have htrace : WordTrace (prefixWord ++ tailWord_1594926) baseStart_1594926 baseEnd_1594926 := by
    simpa [prefixWord, tailWord_1594926, baseEnd_1594926] using wordTrace_append hprefix tailTrace_1594926
  have hstable : (prefixWord ++ tailWord_1594926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594926).length < 2 ^ (prefixWord ++ tailWord_1594926).sum := by decide
  have hdescent : baseEnd_1594926 < baseStart_1594926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1594980 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_1594980 : Nat := 118140960795 + 1594980 * 2 ^ 59
def prefixEnd_1594980 : Nat := 4983230072969 + 3 ^ 40 * 1594980 * 2
def baseEnd_1594980 : Nat := 818991374308274867114827

theorem tailTrace_1594980 : CollatzResearch.WordTrace tailWord_1594980 prefixEnd_1594980 818991374308274867114827 := by
  unfold tailWord_1594980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29086849880833667871083197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38782466507778223828110929 29086849880833667871083197)
  ·
    refine ⟨10907568705312625451656199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29086849880833667871083197 10907568705312625451656199)
    ·
      refine ⟨16361353057968938177484299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10907568705312625451656199 16361353057968938177484299)
      ·
        refine ⟨24542029586953407266226449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16361353057968938177484299 24542029586953407266226449)
        ·
          refine ⟨18406522190215055449669837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24542029586953407266226449 18406522190215055449669837)
          ·
            refine ⟨6902445821330645793626189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18406522190215055449669837 6902445821330645793626189)
            ·
              refine ⟨2588417182998992172609821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6902445821330645793626189 2588417182998992172609821)
              ·
                refine ⟨970656443624622064728683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2588417182998992172609821 970656443624622064728683)
                ·
                  refine ⟨1455984665436933097093025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970656443624622064728683 1455984665436933097093025)
                  ·
                    refine ⟨1091988499077699822819769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455984665436933097093025 1091988499077699822819769)
                    ·
                      refine ⟨818991374308274867114827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1091988499077699822819769 818991374308274867114827)
                      ·
                        rfl

theorem cell23_1594980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_1594980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1594980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1594980 prefixEnd_1594980 := by exact prefixLift 1594980
  have htrace : WordTrace (prefixWord ++ tailWord_1594980) baseStart_1594980 baseEnd_1594980 := by
    simpa [prefixWord, tailWord_1594980, baseEnd_1594980] using wordTrace_append hprefix tailTrace_1594980
  have hstable : (prefixWord ++ tailWord_1594980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1594980).length < 2 ^ (prefixWord ++ tailWord_1594980).sum := by decide
  have hdescent : baseEnd_1594980 < baseStart_1594980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1594980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595040 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2]
def baseStart_1595040 : Nat := 118140960795 + 1595040 * 2 ^ 59
def prefixEnd_1595040 : Nat := 4983230072969 + 3 ^ 40 * 1595040 * 2
def baseEnd_1595040 : Nat := 819022183147544632364551

theorem tailTrace_1595040 : CollatzResearch.WordTrace tailWord_1595040 prefixEnd_1595040 819022183147544632364551 := by
  unfold tailWord_1595040
  simp only [CollatzResearch.WordTrace]
  refine ⟨29087944070724982994675287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38783925427633310659567049 29087944070724982994675287)
  ·
    refine ⟨43631916106087474492012931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29087944070724982994675287 43631916106087474492012931)
    ·
      refine ⟨65447874159131211738019397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43631916106087474492012931 65447874159131211738019397)
      ·
        refine ⟨12271476404837102200878637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65447874159131211738019397 12271476404837102200878637)
        ·
          refine ⟨4601803651813913325329489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12271476404837102200878637 4601803651813913325329489)
          ·
            refine ⟨3451352738860434993997117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601803651813913325329489 3451352738860434993997117)
            ·
              refine ⟨1294257277072663122748919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3451352738860434993997117 1294257277072663122748919)
              ·
                refine ⟨1941385915608994684123379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294257277072663122748919 1941385915608994684123379)
                ·
                  refine ⟨2912078873413492026185069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941385915608994684123379 2912078873413492026185069)
                  ·
                    refine ⟨1092029577530059509819401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912078873413492026185069 1092029577530059509819401)
                    ·
                      refine ⟨819022183147544632364551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092029577530059509819401 819022183147544632364551)
                      ·
                        rfl

theorem cell23_1595040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_1595040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595040 prefixEnd_1595040 := by exact prefixLift 1595040
  have htrace : WordTrace (prefixWord ++ tailWord_1595040) baseStart_1595040 baseEnd_1595040 := by
    simpa [prefixWord, tailWord_1595040, baseEnd_1595040] using wordTrace_append hprefix tailTrace_1595040
  have hstable : (prefixWord ++ tailWord_1595040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595040).length < 2 ^ (prefixWord ++ tailWord_1595040).sum := by decide
  have hdescent : baseEnd_1595040 < baseStart_1595040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595048 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1595048 : Nat := 118140960795 + 1595048 * 2 ^ 59
def prefixEnd_1595048 : Nat := 4983230072969 + 3 ^ 40 * 1595048 * 2
def baseEnd_1595048 : Nat := 819026290992780601064515

theorem tailTrace_1595048 : CollatzResearch.WordTrace tailWord_1595048 prefixEnd_1595048 819026290992780601064515 := by
  unfold tailWord_1595048
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088089962710491677820899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38784119950280655570427865 29088089962710491677820899)
  ·
    refine ⟨43632134944065737516731349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29088089962710491677820899 43632134944065737516731349)
    ·
      refine ⟨1022628162751540723048391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43632134944065737516731349 1022628162751540723048391)
      ·
        refine ⟨1533942244127311084572587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022628162751540723048391 1533942244127311084572587)
        ·
          refine ⟨2300913366190966626858881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533942244127311084572587 2300913366190966626858881)
          ·
            refine ⟨1725685024643224970144161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300913366190966626858881 1725685024643224970144161)
            ·
              refine ⟨1294263768482418727608121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725685024643224970144161 1294263768482418727608121)
              ·
                refine ⟨970697826361814045706091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294263768482418727608121 970697826361814045706091)
                ·
                  refine ⟨1456046739542721068559137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970697826361814045706091 1456046739542721068559137)
                  ·
                    refine ⟨1092035054657040801419353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456046739542721068559137 1092035054657040801419353)
                    ·
                      refine ⟨819026290992780601064515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092035054657040801419353 819026290992780601064515)
                      ·
                        rfl

theorem cell23_1595048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1595048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595048 prefixEnd_1595048 := by exact prefixLift 1595048
  have htrace : WordTrace (prefixWord ++ tailWord_1595048) baseStart_1595048 baseEnd_1595048 := by
    simpa [prefixWord, tailWord_1595048, baseEnd_1595048] using wordTrace_append hprefix tailTrace_1595048
  have hstable : (prefixWord ++ tailWord_1595048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595048).length < 2 ^ (prefixWord ++ tailWord_1595048).sum := by decide
  have hdescent : baseEnd_1595048 < baseStart_1595048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595070 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_1595070 : Nat := 118140960795 + 1595070 * 2 ^ 59
def prefixEnd_1595070 : Nat := 4983230072969 + 3 ^ 40 * 1595070 * 2
def baseEnd_1595070 : Nat := 819037587567179514989413

theorem tailTrace_1595070 : CollatzResearch.WordTrace tailWord_1595070 prefixEnd_1595070 819037587567179514989413 := by
  unfold tailWord_1595070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7272122791417660139117833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38784654887560854075295109 7272122791417660139117833)
  ·
    refine ⟨5454092093563245104338375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7272122791417660139117833 5454092093563245104338375)
    ·
      refine ⟨8181138140344867656507563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454092093563245104338375 8181138140344867656507563)
      ·
        refine ⟨12271707210517301484761345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181138140344867656507563 12271707210517301484761345)
        ·
          refine ⟨9203780407887976113571009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12271707210517301484761345 9203780407887976113571009)
          ·
            refine ⟨6902835305915982085178257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9203780407887976113571009 6902835305915982085178257)
            ·
              refine ⟨5177126479436986563883693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6902835305915982085178257 5177126479436986563883693)
              ·
                refine ⟨1941422429788869961456385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177126479436986563883693 1941422429788869961456385)
                ·
                  refine ⟨1456066822341652471092289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1941422429788869961456385 1456066822341652471092289)
                  ·
                    refine ⟨1092050116756239353319217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456066822341652471092289 1092050116756239353319217)
                    ·
                      refine ⟨819037587567179514989413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092050116756239353319217 819037587567179514989413)
                      ·
                        rfl

theorem cell23_1595070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_1595070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595070 prefixEnd_1595070 := by exact prefixLift 1595070
  have htrace : WordTrace (prefixWord ++ tailWord_1595070) baseStart_1595070 baseEnd_1595070 := by
    simpa [prefixWord, tailWord_1595070, baseEnd_1595070] using wordTrace_append hprefix tailTrace_1595070
  have hstable : (prefixWord ++ tailWord_1595070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595070).length < 2 ^ (prefixWord ++ tailWord_1595070).sum := by decide
  have hdescent : baseEnd_1595070 < baseStart_1595070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595089 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1595089 : Nat := 118140960795 + 1595089 * 2 ^ 59
def prefixEnd_1595089 : Nat := 4983230072969 + 3 ^ 40 * 1595089 * 2
def baseEnd_1595089 : Nat := 273015781233204980217275

theorem tailTrace_1595089 : CollatzResearch.WordTrace tailWord_1595089 prefixEnd_1595089 273015781233204980217275 := by
  unfold tailWord_1595089
  simp only [CollatzResearch.WordTrace]
  refine ⟨58177675318272447357884321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38785116878848298238589547 58177675318272447357884321)
  ·
    refine ⟨43633256488704335518413241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58177675318272447357884321 43633256488704335518413241)
    ·
      refine ⟨32724942366528251638809931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43633256488704335518413241 32724942366528251638809931)
      ·
        refine ⟨49087413549792377458214897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32724942366528251638809931 49087413549792377458214897)
        ·
          refine ⟨36815560162344283093661173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49087413549792377458214897 36815560162344283093661173)
          ·
            refine ⟨3451458765219776540030735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36815560162344283093661173 3451458765219776540030735)
            ·
              refine ⟨5177188147829664810046103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451458765219776540030735 5177188147829664810046103)
              ·
                refine ⟨7765782221744497215069155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177188147829664810046103 7765782221744497215069155)
                ·
                  refine ⟨11648673332616745822603733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765782221744497215069155 11648673332616745822603733)
                  ·
                    refine ⟨273015781233204980217275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11648673332616745822603733 273015781233204980217275)
                    ·
                      rfl

theorem cell23_1595089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1595089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595089 prefixEnd_1595089 := by exact prefixLift 1595089
  have htrace : WordTrace (prefixWord ++ tailWord_1595089) baseStart_1595089 baseEnd_1595089 := by
    simpa [prefixWord, tailWord_1595089, baseEnd_1595089] using wordTrace_append hprefix tailTrace_1595089
  have hstable : (prefixWord ++ tailWord_1595089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595089).length < 2 ^ (prefixWord ++ tailWord_1595089).sum := by decide
  have hdescent : baseEnd_1595089 < baseStart_1595089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595126 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1595126 : Nat := 118140960795 + 1595126 * 2 ^ 59
def prefixEnd_1595126 : Nat := 4983230072969 + 3 ^ 40 * 1595126 * 2
def baseEnd_1595126 : Nat := 819066342483831295889155

theorem tailTrace_1595126 : CollatzResearch.WordTrace tailWord_1595126 prefixEnd_1595126 819066342483831295889155 := by
  unfold tailWord_1595126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636189051196150167311327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38786016546092268451320821 3636189051196150167311327)
  ·
    refine ⟨5454283576794225250966991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636189051196150167311327 5454283576794225250966991)
    ·
      refine ⟨8181425365191337876450487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454283576794225250966991 8181425365191337876450487)
      ·
        refine ⟨12272138047787006814675731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181425365191337876450487 12272138047787006814675731)
        ·
          refine ⟨18408207071680510222013597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272138047787006814675731 18408207071680510222013597)
          ·
            refine ⟨6903077651880191333255099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18408207071680510222013597 6903077651880191333255099)
            ·
              refine ⟨10354616477820286999882649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903077651880191333255099 10354616477820286999882649)
              ·
                refine ⟨7765962358365215249911987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10354616477820286999882649 7765962358365215249911987)
                ·
                  refine ⟨11648943537547822874867981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765962358365215249911987 11648943537547822874867981)
                  ·
                    refine ⟨4368353826580433578075493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11648943537547822874867981 4368353826580433578075493)
                    ·
                      refine ⟨819066342483831295889155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4368353826580433578075493 819066342483831295889155)
                      ·
                        rfl

theorem cell23_1595126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1595126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595126 prefixEnd_1595126 := by exact prefixLift 1595126
  have htrace : WordTrace (prefixWord ++ tailWord_1595126) baseStart_1595126 baseEnd_1595126 := by
    simpa [prefixWord, tailWord_1595126, baseEnd_1595126] using wordTrace_append hprefix tailTrace_1595126
  have hstable : (prefixWord ++ tailWord_1595126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595126).length < 2 ^ (prefixWord ++ tailWord_1595126).sum := by decide
  have hdescent : baseEnd_1595126 < baseStart_1595126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595146 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1595146 : Nat := 118140960795 + 1595146 * 2 ^ 59
def prefixEnd_1595146 : Nat := 4983230072969 + 3 ^ 40 * 1595146 * 2
def baseEnd_1595146 : Nat := 819076612096921217639063

theorem tailTrace_1595146 : CollatzResearch.WordTrace tailWord_1595146 prefixEnd_1595146 819076612096921217639063 := by
  unfold tailWord_1595146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14544938569766486523177323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38786502852710630728472861 14544938569766486523177323)
  ·
    refine ⟨21817407854649729784765985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14544938569766486523177323 21817407854649729784765985)
    ·
      refine ⟨16363055890987297338574489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21817407854649729784765985 16363055890987297338574489)
      ·
        refine ⟨12272291918240473003930867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16363055890987297338574489 12272291918240473003930867)
        ·
          refine ⟨18408437877360709505896301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12272291918240473003930867 18408437877360709505896301)
          ·
            refine ⟨6903164204010266064711113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18408437877360709505896301 6903164204010266064711113)
            ·
              refine ⟨5177373153007699548533335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903164204010266064711113 5177373153007699548533335)
              ·
                refine ⟨7766059729511549322800003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177373153007699548533335 7766059729511549322800003)
                ·
                  refine ⟨11649089594267323984200005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766059729511549322800003 11649089594267323984200005)
                  ·
                    refine ⟨2184204298925123247037501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11649089594267323984200005 2184204298925123247037501)
                    ·
                      refine ⟨819076612096921217639063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184204298925123247037501 819076612096921217639063)
                      ·
                        rfl

theorem cell23_1595146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1595146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595146 prefixEnd_1595146 := by exact prefixLift 1595146
  have htrace : WordTrace (prefixWord ++ tailWord_1595146) baseStart_1595146 baseEnd_1595146 := by
    simpa [prefixWord, tailWord_1595146, baseEnd_1595146] using wordTrace_append hprefix tailTrace_1595146
  have hstable : (prefixWord ++ tailWord_1595146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595146).length < 2 ^ (prefixWord ++ tailWord_1595146).sum := by decide
  have hdescent : baseEnd_1595146 < baseStart_1595146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595203 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 2, 3, 2]
def baseStart_1595203 : Nat := 118140960795 + 1595203 * 2 ^ 59
def prefixEnd_1595203 : Nat := 4983230072969 + 3 ^ 40 * 1595203 * 2
def baseEnd_1595203 : Nat := 819105880494227494626301

theorem tailTrace_1595203 : CollatzResearch.WordTrace tailWord_1595203 prefixEnd_1595203 819105880494227494626301 := by
  unfold tailWord_1595203
  simp only [CollatzResearch.WordTrace]
  refine ⟨58181833239859444827534263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38787888826572963218356175 58181833239859444827534263)
  ·
    refine ⟨87272749859789167241301395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58181833239859444827534263 87272749859789167241301395)
    ·
      refine ⟨130909124789683750861952093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87272749859789167241301395 130909124789683750861952093)
      ·
        refine ⟨49090921796131406573232035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130909124789683750861952093 49090921796131406573232035)
        ·
          refine ⟨73636382694197109859848053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49090921796131406573232035 73636382694197109859848053)
          ·
            refine ⟨6903410877580979049360755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73636382694197109859848053 6903410877580979049360755)
            ·
              refine ⟨10355116316371468574041133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903410877580979049360755 10355116316371468574041133)
              ·
                refine ⟨3883168618639300715265425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10355116316371468574041133 3883168618639300715265425)
                ·
                  refine ⟨2912376463979475536449069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883168618639300715265425 2912376463979475536449069)
                  ·
                    refine ⟨1092141173992303326168401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912376463979475536449069 1092141173992303326168401)
                    ·
                      refine ⟨819105880494227494626301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092141173992303326168401 819105880494227494626301)
                      ·
                        rfl

theorem cell23_1595203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_1595203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595203 prefixEnd_1595203 := by exact prefixLift 1595203
  have htrace : WordTrace (prefixWord ++ tailWord_1595203) baseStart_1595203 baseEnd_1595203 := by
    simpa [prefixWord, tailWord_1595203, baseEnd_1595203] using wordTrace_append hprefix tailTrace_1595203
  have hstable : (prefixWord ++ tailWord_1595203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595203).length < 2 ^ (prefixWord ++ tailWord_1595203).sum := by decide
  have hdescent : baseEnd_1595203 < baseStart_1595203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595210 : List Nat := [3, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_1595210 : Nat := 118140960795 + 1595210 * 2 ^ 59
def prefixEnd_1595210 : Nat := 4983230072969 + 3 ^ 40 * 1595210 * 2
def baseEnd_1595210 : Nat := 819109474858808967238769

theorem tailTrace_1595210 : CollatzResearch.WordTrace tailWord_1595210 prefixEnd_1595210 819109474858808967238769 := by
  unfold tailWord_1595210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545522137708521255759771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38788059033889390015359389 14545522137708521255759771)
  ·
    refine ⟨21818283206562781883639657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14545522137708521255759771 21818283206562781883639657)
    ·
      refine ⟨16363712404922086412729743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21818283206562781883639657 16363712404922086412729743)
      ·
        refine ⟨24545568607383129619094615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16363712404922086412729743 24545568607383129619094615)
        ·
          refine ⟨36818352911074694428641923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24545568607383129619094615 36818352911074694428641923)
          ·
            refine ⟨55227529366612041642962885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36818352911074694428641923 55227529366612041642962885)
            ·
              refine ⟨10355161756239757808055541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55227529366612041642962885 10355161756239757808055541)
              ·
                refine ⟨970796414647477294505207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10355161756239757808055541 970796414647477294505207)
                ·
                  refine ⟨1456194621971215941757811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970796414647477294505207 1456194621971215941757811)
                  ·
                    refine ⟨2184291932956823912636717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456194621971215941757811 2184291932956823912636717)
                    ·
                      refine ⟨819109474858808967238769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184291932956823912636717 819109474858808967238769)
                      ·
                        rfl

theorem cell23_1595210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_1595210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595210 prefixEnd_1595210 := by exact prefixLift 1595210
  have htrace : WordTrace (prefixWord ++ tailWord_1595210) baseStart_1595210 baseEnd_1595210 := by
    simpa [prefixWord, tailWord_1595210, baseEnd_1595210] using wordTrace_append hprefix tailTrace_1595210
  have hstable : (prefixWord ++ tailWord_1595210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595210).length < 2 ^ (prefixWord ++ tailWord_1595210).sum := by decide
  have hdescent : baseEnd_1595210 < baseStart_1595210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595220 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_1595220 : Nat := 118140960795 + 1595220 * 2 ^ 59
def prefixEnd_1595220 : Nat := 4983230072969 + 3 ^ 40 * 1595220 * 2
def baseEnd_1595220 : Nat := 819114609665353928113723

theorem tailTrace_1595220 : CollatzResearch.WordTrace tailWord_1595220 prefixEnd_1595220 819114609665353928113723 := by
  unfold tailWord_1595220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29091226640398928365451557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38788302187198571153935409 29091226640398928365451557)
  ·
    refine ⟨5454604995074799068522167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29091226640398928365451557 5454604995074799068522167)
    ·
      refine ⟨8181907492612198602783251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454604995074799068522167 8181907492612198602783251)
      ·
        refine ⟨12272861238918297904174877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8181907492612198602783251 12272861238918297904174877)
        ·
          refine ⟨4602322964594361714065579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12272861238918297904174877 4602322964594361714065579)
          ·
            refine ⟨6903484446891542571098369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602322964594361714065579 6903484446891542571098369)
            ·
              refine ⟨5177613335168656928323777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903484446891542571098369 5177613335168656928323777)
              ·
                refine ⟨3883210001376492696242833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177613335168656928323777 3883210001376492696242833)
                ·
                  refine ⟨2912407501032369522182125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883210001376492696242833 2912407501032369522182125)
                  ·
                    refine ⟨1092152812887138570818297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912407501032369522182125 1092152812887138570818297)
                    ·
                      refine ⟨819114609665353928113723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092152812887138570818297 819114609665353928113723)
                      ·
                        rfl

theorem cell23_1595220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_1595220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595220 prefixEnd_1595220 := by exact prefixLift 1595220
  have htrace : WordTrace (prefixWord ++ tailWord_1595220) baseStart_1595220 baseEnd_1595220 := by
    simpa [prefixWord, tailWord_1595220, baseEnd_1595220] using wordTrace_append hprefix tailTrace_1595220
  have hstable : (prefixWord ++ tailWord_1595220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595220).length < 2 ^ (prefixWord ++ tailWord_1595220).sum := by decide
  have hdescent : baseEnd_1595220 < baseStart_1595220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595253 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1595253 : Nat := 118140960795 + 1595253 * 2 ^ 59
def prefixEnd_1595253 : Nat := 4983230072969 + 3 ^ 40 * 1595253 * 2
def baseEnd_1595253 : Nat := 819131554526952299001071

theorem tailTrace_1595253 : CollatzResearch.WordTrace tailWord_1595253 prefixEnd_1595253 819131554526952299001071 := by
  unfold tailWord_1595253
  simp only [CollatzResearch.WordTrace]
  refine ⟨58183656889678303366854413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38789104593118868911236275 58183656889678303366854413)
  ·
    refine ⟨21818871333629363762570405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58183656889678303366854413 21818871333629363762570405)
    ·
      refine ⟨4091038375055505705481951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21818871333629363762570405 4091038375055505705481951)
      ·
        refine ⟨6136557562583258558222927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091038375055505705481951 6136557562583258558222927)
        ·
          refine ⟨9204836343874887837334391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136557562583258558222927 9204836343874887837334391)
          ·
            refine ⟨13807254515812331756001587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9204836343874887837334391 13807254515812331756001587)
            ·
              refine ⟨20710881773718497634002381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13807254515812331756001587 20710881773718497634002381)
              ·
                refine ⟨7766580665144436612750893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20710881773718497634002381 7766580665144436612750893)
                ·
                  refine ⟨2912467749429163729781585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7766580665144436612750893 2912467749429163729781585)
                  ·
                    refine ⟨2184350812071872797336189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912467749429163729781585 2184350812071872797336189)
                    ·
                      refine ⟨819131554526952299001071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184350812071872797336189 819131554526952299001071)
                      ·
                        rfl

theorem cell23_1595253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1595253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595253 prefixEnd_1595253 := by exact prefixLift 1595253
  have htrace : WordTrace (prefixWord ++ tailWord_1595253) baseStart_1595253 baseEnd_1595253 := by
    simpa [prefixWord, tailWord_1595253, baseEnd_1595253] using wordTrace_append hprefix tailTrace_1595253
  have hstable : (prefixWord ++ tailWord_1595253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595253).length < 2 ^ (prefixWord ++ tailWord_1595253).sum := by decide
  have hdescent : baseEnd_1595253 < baseStart_1595253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595254 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1595254 : Nat := 118140960795 + 1595254 * 2 ^ 59
def prefixEnd_1595254 : Nat := 4983230072969 + 3 ^ 40 * 1595254 * 2
def baseEnd_1595254 : Nat := 819132068007606795088567

theorem tailTrace_1595254 : CollatzResearch.WordTrace tailWord_1595254 prefixEnd_1595254 819132068007606795088567 := by
  unfold tailWord_1595254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636480835167167533602551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38789128908449787025093877 3636480835167167533602551)
  ·
    refine ⟨5454721252750751300403827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636480835167167533602551 5454721252750751300403827)
    ·
      refine ⟨8182081879126126950605741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454721252750751300403827 8182081879126126950605741)
      ·
        refine ⟨3068280704672297606477153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8182081879126126950605741 3068280704672297606477153)
        ·
          refine ⟨2301210528504223204857865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3068280704672297606477153 2301210528504223204857865)
          ·
            refine ⟨1725907896378167403643399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301210528504223204857865 1725907896378167403643399)
            ·
              refine ⟨2588861844567251105465099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725907896378167403643399 2588861844567251105465099)
              ·
                refine ⟨3883292766850876658197649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588861844567251105465099 3883292766850876658197649)
                ·
                  refine ⟨2912469575138157493648237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883292766850876658197649 2912469575138157493648237)
                  ·
                    refine ⟨1092176090676809060118089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912469575138157493648237 1092176090676809060118089)
                    ·
                      refine ⟨819132068007606795088567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092176090676809060118089 819132068007606795088567)
                      ·
                        rfl

theorem cell23_1595254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1595254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595254 prefixEnd_1595254 := by exact prefixLift 1595254
  have htrace : WordTrace (prefixWord ++ tailWord_1595254) baseStart_1595254 baseEnd_1595254 := by
    simpa [prefixWord, tailWord_1595254, baseEnd_1595254] using wordTrace_append hprefix tailTrace_1595254
  have hstable : (prefixWord ++ tailWord_1595254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595254).length < 2 ^ (prefixWord ++ tailWord_1595254).sum := by decide
  have hdescent : baseEnd_1595254 < baseStart_1595254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595267 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 1, 2, 2]
def baseStart_1595267 : Nat := 118140960795 + 1595267 * 2 ^ 59
def prefixEnd_1595267 : Nat := 4983230072969 + 3 ^ 40 * 1595267 * 2
def baseEnd_1595267 : Nat := 819138743256115244226007

theorem tailTrace_1595267 : CollatzResearch.WordTrace tailWord_1595267 prefixEnd_1595267 819138743256115244226007 := by
  unfold tailWord_1595267
  simp only [CollatzResearch.WordTrace]
  refine ⟨58184167511627583757864055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38789445007751722505242703 58184167511627583757864055)
  ·
    refine ⟨87276251267441375636796083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58184167511627583757864055 87276251267441375636796083)
    ·
      refine ⟨130914376901162063455194125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87276251267441375636796083 130914376901162063455194125)
      ·
        refine ⟨49092891337935773795697797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130914376901162063455194125 49092891337935773795697797)
        ·
          refine ⟨9204917125862957586693337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49092891337935773795697797 9204917125862957586693337)
          ·
            refine ⟨6903687844397218190020003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9204917125862957586693337 6903687844397218190020003)
            ·
              refine ⟨10355531766595827285030005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903687844397218190020003 10355531766595827285030005)
              ·
                refine ⟨970831103118358807971563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10355531766595827285030005 970831103118358807971563)
                ·
                  refine ⟨1456246654677538211957345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970831103118358807971563 1456246654677538211957345)
                  ·
                    refine ⟨1092184991008153658968009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456246654677538211957345 1092184991008153658968009)
                    ·
                      refine ⟨819138743256115244226007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092184991008153658968009 819138743256115244226007)
                      ·
                        rfl

theorem cell23_1595267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_1595267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595267 prefixEnd_1595267 := by exact prefixLift 1595267
  have htrace : WordTrace (prefixWord ++ tailWord_1595267) baseStart_1595267 baseEnd_1595267 := by
    simpa [prefixWord, tailWord_1595267, baseEnd_1595267] using wordTrace_append hprefix tailTrace_1595267
  have hstable : (prefixWord ++ tailWord_1595267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595267).length < 2 ^ (prefixWord ++ tailWord_1595267).sum := by decide
  have hdescent : baseEnd_1595267 < baseStart_1595267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595284 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1595284 : Nat := 118140960795 + 1595284 * 2 ^ 59
def prefixEnd_1595284 : Nat := 4983230072969 + 3 ^ 40 * 1595284 * 2
def baseEnd_1595284 : Nat := 819147472427241677713429

theorem tailTrace_1595284 : CollatzResearch.WordTrace tailWord_1595284 prefixEnd_1595284 819147472427241677713429 := by
  unfold tailWord_1595284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092393776282997830616453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38789858368377330440821937 29092393776282997830616453)
  ·
    refine ⟨5454823833053062093240585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29092393776282997830616453 5454823833053062093240585)
    ·
      refine ⟨4091117874789796569930439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454823833053062093240585 4091117874789796569930439)
      ·
        refine ⟨6136676812184694854895659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091117874789796569930439 6136676812184694854895659)
        ·
          refine ⟨9205015218277042282343489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136676812184694854895659 9205015218277042282343489)
          ·
            refine ⟨6903761413707781711757617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9205015218277042282343489 6903761413707781711757617)
            ·
              refine ⟨5177821060280836283818213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6903761413707781711757617 5177821060280836283818213)
              ·
                refine ⟨970841448802656803215915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5177821060280836283818213 970841448802656803215915)
                ·
                  refine ⟨1456262173203985204823873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970841448802656803215915 1456262173203985204823873)
                  ·
                    refine ⟨1092196629902988903617905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456262173203985204823873 1092196629902988903617905)
                    ·
                      refine ⟨819147472427241677713429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092196629902988903617905 819147472427241677713429)
                      ·
                        rfl

theorem cell23_1595284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1595284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595284 prefixEnd_1595284 := by exact prefixLift 1595284
  have htrace : WordTrace (prefixWord ++ tailWord_1595284) baseStart_1595284 baseEnd_1595284 := by
    simpa [prefixWord, tailWord_1595284, baseEnd_1595284] using wordTrace_append hprefix tailTrace_1595284
  have hstable : (prefixWord ++ tailWord_1595284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595284).length < 2 ^ (prefixWord ++ tailWord_1595284).sum := by decide
  have hdescent : baseEnd_1595284 < baseStart_1595284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595294 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1595294 : Nat := 118140960795 + 1595294 * 2 ^ 59
def prefixEnd_1595294 : Nat := 4983230072969 + 3 ^ 40 * 1595294 * 2
def baseEnd_1595294 : Nat := 273050869077928879529461

theorem tailTrace_1595294 : CollatzResearch.WordTrace tailWord_1595294 prefixEnd_1595294 273050869077928879529461 := by
  unfold tailWord_1595294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273144035316220921137117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38790101521686511579397957 7273144035316220921137117)
  ·
    refine ⟨2727429013243582845426419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7273144035316220921137117 2727429013243582845426419)
    ·
      refine ⟨4091143519865374268139629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727429013243582845426419 4091143519865374268139629)
      ·
        refine ⟨1534178819949515350552361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4091143519865374268139629 1534178819949515350552361)
        ·
          refine ⟨1150634114962136512914271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534178819949515350552361 1150634114962136512914271)
          ·
            refine ⟨1725951172443204769371407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150634114962136512914271 1725951172443204769371407)
            ·
              refine ⟨2588926758664807154057111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725951172443204769371407 2588926758664807154057111)
              ·
                refine ⟨3883390137997210731085667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588926758664807154057111 3883390137997210731085667)
                ·
                  refine ⟨5825085206995816096628501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883390137997210731085667 5825085206995816096628501)
                  ·
                    refine ⟨273050869077928879529461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5825085206995816096628501 273050869077928879529461)
                    ·
                      rfl

theorem cell23_1595294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1595294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595294 prefixEnd_1595294 := by exact prefixLift 1595294
  have htrace : WordTrace (prefixWord ++ tailWord_1595294) baseStart_1595294 baseEnd_1595294 := by
    simpa [prefixWord, tailWord_1595294, baseEnd_1595294] using wordTrace_append hprefix tailTrace_1595294
  have hstable : (prefixWord ++ tailWord_1595294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595294).length < 2 ^ (prefixWord ++ tailWord_1595294).sum := by decide
  have hdescent : baseEnd_1595294 < baseStart_1595294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595297 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1595297 : Nat := 118140960795 + 1595297 * 2 ^ 59
def prefixEnd_1595297 : Nat := 4983230072969 + 3 ^ 40 * 1595297 * 2
def baseEnd_1595297 : Nat := 819154147675750126850869

theorem tailTrace_1595297 : CollatzResearch.WordTrace tailWord_1595297 prefixEnd_1595297 819154147675750126850869 := by
  unfold tailWord_1595297
  simp only [CollatzResearch.WordTrace]
  refine ⟨58185261701518898881456145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38790174467679265920970763 58185261701518898881456145)
  ·
    refine ⟨43638946276139174161092109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58185261701518898881456145 43638946276139174161092109)
    ·
      refine ⟨16364604853552190310409541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43638946276139174161092109 16364604853552190310409541)
      ·
        refine ⟨3068363410041035683201789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16364604853552190310409541 3068363410041035683201789)
        ·
          refine ⟨1150636278765388381200671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3068363410041035683201789 1150636278765388381200671)
          ·
            refine ⟨1725954418148082571801007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150636278765388381200671 1725954418148082571801007)
            ·
              refine ⟨2588931627222123857701511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725954418148082571801007 2588931627222123857701511)
              ·
                refine ⟨3883397440833185786552267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588931627222123857701511 3883397440833185786552267)
                ·
                  refine ⟨5825096161249778679828401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883397440833185786552267 5825096161249778679828401)
                  ·
                    refine ⟨4368822120937334009871301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825096161249778679828401 4368822120937334009871301)
                    ·
                      refine ⟨819154147675750126850869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4368822120937334009871301 819154147675750126850869)
                      ·
                        rfl

theorem cell23_1595297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1595297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595297 prefixEnd_1595297 := by exact prefixLift 1595297
  have htrace : WordTrace (prefixWord ++ tailWord_1595297) baseStart_1595297 baseEnd_1595297 := by
    simpa [prefixWord, tailWord_1595297, baseEnd_1595297] using wordTrace_append hprefix tailTrace_1595297
  have hstable : (prefixWord ++ tailWord_1595297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595297).length < 2 ^ (prefixWord ++ tailWord_1595297).sum := by decide
  have hdescent : baseEnd_1595297 < baseStart_1595297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595300 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_1595300 : Nat := 118140960795 + 1595300 * 2 ^ 59
def prefixEnd_1595300 : Nat := 4983230072969 + 3 ^ 40 * 1595300 * 2
def baseEnd_1595300 : Nat := 819155688117713615113355

theorem tailTrace_1595300 : CollatzResearch.WordTrace tailWord_1595300 prefixEnd_1595300 819155688117713615113355 := by
  unfold tailWord_1595300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092685560254015196907677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38790247413672020262543569 29092685560254015196907677)
  ·
    refine ⟨10909757085095255698840379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29092685560254015196907677 10909757085095255698840379)
    ·
      refine ⟨16364635627642883548260569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909757085095255698840379 16364635627642883548260569)
      ·
        refine ⟨12273476720732162661195427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16364635627642883548260569 12273476720732162661195427)
        ·
          refine ⟨18410215081098243991793141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12273476720732162661195427 18410215081098243991793141)
          ·
            refine ⟨1725957663852960374230607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18410215081098243991793141 1725957663852960374230607)
            ·
              refine ⟨2588936495779440561345911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725957663852960374230607 2588936495779440561345911)
              ·
                refine ⟨3883404743669160842018867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588936495779440561345911 3883404743669160842018867)
                ·
                  refine ⟨5825107115503741263028301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883404743669160842018867 5825107115503741263028301)
                  ·
                    refine ⟨2184415168313902973635613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5825107115503741263028301 2184415168313902973635613)
                    ·
                      refine ⟨819155688117713615113355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184415168313902973635613 819155688117713615113355)
                      ·
                        rfl

theorem cell23_1595300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_1595300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595300 prefixEnd_1595300 := by exact prefixLift 1595300
  have htrace : WordTrace (prefixWord ++ tailWord_1595300) baseStart_1595300 baseEnd_1595300 := by
    simpa [prefixWord, tailWord_1595300, baseEnd_1595300] using wordTrace_append hprefix tailTrace_1595300
  have hstable : (prefixWord ++ tailWord_1595300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595300).length < 2 ^ (prefixWord ++ tailWord_1595300).sum := by decide
  have hdescent : baseEnd_1595300 < baseStart_1595300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595304 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1595304 : Nat := 118140960795 + 1595304 * 2 ^ 59
def prefixEnd_1595304 : Nat := 4983230072969 + 3 ^ 40 * 1595304 * 2
def baseEnd_1595304 : Nat := 819157742040331599463337

theorem tailTrace_1595304 : CollatzResearch.WordTrace tailWord_1595304 prefixEnd_1595304 819157742040331599463337 := by
  unfold tailWord_1595304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092758506246769538480483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38790344674995692717973977 29092758506246769538480483)
  ·
    refine ⟨43639137759370154307720725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29092758506246769538480483 43639137759370154307720725)
    ·
      refine ⟨2045584582470475983174409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43639137759370154307720725 2045584582470475983174409)
      ·
        refine ⟨1534188436852856987380807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2045584582470475983174409 1534188436852856987380807)
        ·
          refine ⟨2301282655279285481071211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534188436852856987380807 2301282655279285481071211)
          ·
            refine ⟨3451923982918928221606817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301282655279285481071211 3451923982918928221606817)
            ·
              refine ⟨2588942987189196166205113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451923982918928221606817 2588942987189196166205113)
              ·
                refine ⟨1941707240391897124653835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588942987189196166205113 1941707240391897124653835)
                ·
                  refine ⟨2912560860587845686980753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941707240391897124653835 2912560860587845686980753)
                  ·
                    refine ⟨2184420645440884265235565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912560860587845686980753 2184420645440884265235565)
                    ·
                      refine ⟨819157742040331599463337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184420645440884265235565 819157742040331599463337)
                      ·
                        rfl

theorem cell23_1595304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1595304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595304 prefixEnd_1595304 := by exact prefixLift 1595304
  have htrace : WordTrace (prefixWord ++ tailWord_1595304) baseStart_1595304 baseEnd_1595304 := by
    simpa [prefixWord, tailWord_1595304, baseEnd_1595304] using wordTrace_append hprefix tailTrace_1595304
  have hstable : (prefixWord ++ tailWord_1595304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595304).length < 2 ^ (prefixWord ++ tailWord_1595304).sum := by decide
  have hdescent : baseEnd_1595304 < baseStart_1595304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595376 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_1595376 : Nat := 118140960795 + 1595376 * 2 ^ 59
def prefixEnd_1595376 : Nat := 4983230072969 + 3 ^ 40 * 1595376 * 2
def baseEnd_1595376 : Nat := 273064904215818439254335

theorem tailTrace_1595376 : CollatzResearch.WordTrace tailWord_1595376 prefixEnd_1595376 273064904215818439254335 := by
  unfold tailWord_1595376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29094071534116347686790991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38792095378821796915721321 29094071534116347686790991)
  ·
    refine ⟨43641107301174521530186487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29094071534116347686790991 43641107301174521530186487)
    ·
      refine ⟨65461660951761782295279731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43641107301174521530186487 65461660951761782295279731)
      ·
        refine ⟨98192491427642673442919597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65461660951761782295279731 98192491427642673442919597)
        ·
          refine ⟨36822184285366002541094849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98192491427642673442919597 36822184285366002541094849)
          ·
            refine ⟨27616638214024501905821137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36822184285366002541094849 27616638214024501905821137)
            ·
              refine ⟨20712478660518376429365853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27616638214024501905821137 20712478660518376429365853)
              ·
                refine ⟨7767179497694391161012195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20712478660518376429365853 7767179497694391161012195)
                ·
                  refine ⟨11650769246541586741518293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7767179497694391161012195 11650769246541586741518293)
                  ·
                    refine ⟨273064904215818439254335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11650769246541586741518293 273064904215818439254335)
                    ·
                      rfl

theorem cell23_1595376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_1595376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595376 prefixEnd_1595376 := by exact prefixLift 1595376
  have htrace : WordTrace (prefixWord ++ tailWord_1595376) baseStart_1595376 baseEnd_1595376 := by
    simpa [prefixWord, tailWord_1595376, baseEnd_1595376] using wordTrace_append hprefix tailTrace_1595376
  have hstable : (prefixWord ++ tailWord_1595376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595376).length < 2 ^ (prefixWord ++ tailWord_1595376).sum := by decide
  have hdescent : baseEnd_1595376 < baseStart_1595376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595383 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 5, 2]
def baseStart_1595383 : Nat := 118140960795 + 1595383 * 2 ^ 59
def prefixEnd_1595383 : Nat := 4983230072969 + 3 ^ 40 * 1595383 * 2
def baseEnd_1595383 : Nat := 819198307012036790375473

theorem tailTrace_1595383 : CollatzResearch.WordTrace tailWord_1595383 prefixEnd_1595383 819198307012036790375473 := by
  unfold tailWord_1595383
  simp only [CollatzResearch.WordTrace]
  refine ⟨58188398379207335569086803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38792265586138223712724535 58188398379207335569086803)
  ·
    refine ⟨87282597568811003353630205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58188398379207335569086803 87282597568811003353630205)
    ·
      refine ⟨32730974088304126257611327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87282597568811003353630205 32730974088304126257611327)
      ·
        refine ⟨49096461132456189386416991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32730974088304126257611327 49096461132456189386416991)
        ·
          refine ⟨73644691698684284079625487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49096461132456189386416991 73644691698684284079625487)
          ·
            refine ⟨110467037548026426119438231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73644691698684284079625487 110467037548026426119438231)
            ·
              refine ⟨165700556322039639179157347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110467037548026426119438231 165700556322039639179157347)
              ·
                refine ⟨248550834483059458768736021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165700556322039639179157347 248550834483059458768736021)
                ·
                  refine ⟨11650820366393412129784501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248550834483059458768736021 11650820366393412129784501)
                  ·
                    refine ⟨1092264409349382387167297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11650820366393412129784501 1092264409349382387167297)
                    ·
                      refine ⟨819198307012036790375473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092264409349382387167297 819198307012036790375473)
                      ·
                        rfl

theorem cell23_1595383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_1595383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595383 prefixEnd_1595383 := by exact prefixLift 1595383
  have htrace : WordTrace (prefixWord ++ tailWord_1595383) baseStart_1595383 baseEnd_1595383 := by
    simpa [prefixWord, tailWord_1595383, baseEnd_1595383] using wordTrace_append hprefix tailTrace_1595383
  have hstable : (prefixWord ++ tailWord_1595383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595383).length < 2 ^ (prefixWord ++ tailWord_1595383).sum := by decide
  have hdescent : baseEnd_1595383 < baseStart_1595383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595393 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1595393 : Nat := 118140960795 + 1595393 * 2 ^ 59
def prefixEnd_1595393 : Nat := 4983230072969 + 3 ^ 40 * 1595393 * 2
def baseEnd_1595393 : Nat := 273067813939527250416809

theorem tailTrace_1595393 : CollatzResearch.WordTrace tailWord_1595393 prefixEnd_1595393 273067813939527250416809 := by
  unfold tailWord_1595393
  simp only [CollatzResearch.WordTrace]
  refine ⟨58188763109171107276950833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38792508739447404851300555 58188763109171107276950833)
  ·
    refine ⟨43641572331878330457713125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58188763109171107276950833 43641572331878330457713125)
    ·
      refine ⟨8182794812227186960821211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43641572331878330457713125 8182794812227186960821211)
      ·
        refine ⟨12274192218340780441231817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182794812227186960821211 12274192218340780441231817)
        ·
          refine ⟨9205644163755585330923863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12274192218340780441231817 9205644163755585330923863)
          ·
            refine ⟨13808466245633377996385795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205644163755585330923863 13808466245633377996385795)
            ·
              refine ⟨20712699368450066994578693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13808466245633377996385795 20712699368450066994578693)
              ·
                refine ⟨3883631131584387561483505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20712699368450066994578693 3883631131584387561483505)
                ·
                  refine ⟨2912723348688290671112629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883631131584387561483505 2912723348688290671112629)
                  ·
                    refine ⟨273067813939527250416809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2912723348688290671112629 273067813939527250416809)
                    ·
                      rfl

theorem cell23_1595393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1595393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595393 prefixEnd_1595393 := by exact prefixLift 1595393
  have htrace : WordTrace (prefixWord ++ tailWord_1595393) baseStart_1595393 baseEnd_1595393 := by
    simpa [prefixWord, tailWord_1595393, baseEnd_1595393] using wordTrace_append hprefix tailTrace_1595393
  have hstable : (prefixWord ++ tailWord_1595393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595393).length < 2 ^ (prefixWord ++ tailWord_1595393).sum := by decide
  have hdescent : baseEnd_1595393 < baseStart_1595393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595397 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 5]
def baseStart_1595397 : Nat := 118140960795 + 1595397 * 2 ^ 59
def prefixEnd_1595397 : Nat := 4983230072969 + 3 ^ 40 * 1595397 * 2
def baseEnd_1595397 : Nat := 91022832860133303955601

theorem tailTrace_1595397 : CollatzResearch.WordTrace tailWord_1595397 prefixEnd_1595397 91022832860133303955601 := by
  unfold tailWord_1595397
  simp only [CollatzResearch.WordTrace]
  refine ⟨58188909001156615960096445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38792606000771077306730963 58188909001156615960096445)
  ·
    refine ⟨21820840875433730985036167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58188909001156615960096445 21820840875433730985036167)
    ·
      refine ⟨32731261313150596477554251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21820840875433730985036167 32731261313150596477554251)
      ·
        refine ⟨49096891969725894716331377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32731261313150596477554251 49096891969725894716331377)
        ·
          refine ⟨36822668977294421037248533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49096891969725894716331377 36822668977294421037248533)
          ·
            refine ⟨1726062608310675986121025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36822668977294421037248533 1726062608310675986121025)
            ·
              refine ⟨1294546956233006989590769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726062608310675986121025 1294546956233006989590769)
              ·
                refine ⟨970910217174755242193077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294546956233006989590769 970910217174755242193077)
                ·
                  refine ⟨91022832860133303955601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970910217174755242193077 91022832860133303955601)
                  ·
                    rfl

theorem cell23_1595397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_1595397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595397 prefixEnd_1595397 := by exact prefixLift 1595397
  have htrace : WordTrace (prefixWord ++ tailWord_1595397) baseStart_1595397 baseEnd_1595397 := by
    simpa [prefixWord, tailWord_1595397, baseEnd_1595397] using wordTrace_append hprefix tailTrace_1595397
  have hstable : (prefixWord ++ tailWord_1595397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595397).length < 2 ^ (prefixWord ++ tailWord_1595397).sum := by decide
  have hdescent : baseEnd_1595397 < baseStart_1595397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595453 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 8]
def baseStart_1595453 : Nat := 118140960795 + 1595453 * 2 ^ 59
def prefixEnd_1595453 : Nat := 4983230072969 + 3 ^ 40 * 1595453 * 2
def baseEnd_1595453 : Nat := 91026027850872390722239

theorem tailTrace_1595453 : CollatzResearch.WordTrace tailWord_1595453 prefixEnd_1595453 91026027850872390722239 := by
  unfold tailWord_1595453
  simp only [CollatzResearch.WordTrace]
  refine ⟨58190951488953737524135013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38793967659302491682756675 58190951488953737524135013)
  ·
    refine ⟨10910803404178825785775315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58190951488953737524135013 10910803404178825785775315)
    ·
      refine ⟨16366205106268238678662973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10910803404178825785775315 16366205106268238678662973)
      ·
        refine ⟨6137326914850589504498615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16366205106268238678662973 6137326914850589504498615)
        ·
          refine ⟨9205990372275884256747923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137326914850589504498615 9205990372275884256747923)
          ·
            refine ⟨13808985558413826385121885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205990372275884256747923 13808985558413826385121885)
            ·
              refine ⟨5178369584405184894420707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13808985558413826385121885 5178369584405184894420707)
              ·
                refine ⟨7767554376607777341631061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178369584405184894420707 7767554376607777341631061)
                ·
                  refine ⟨91026027850872390722239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7767554376607777341631061 91026027850872390722239)
                  ·
                    rfl

theorem cell23_1595453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_1595453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595453 prefixEnd_1595453 := by exact prefixLift 1595453
  have htrace : WordTrace (prefixWord ++ tailWord_1595453) baseStart_1595453 baseEnd_1595453 := by
    simpa [prefixWord, tailWord_1595453, baseEnd_1595453] using wordTrace_append hprefix tailTrace_1595453
  have hstable : (prefixWord ++ tailWord_1595453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595453).length < 2 ^ (prefixWord ++ tailWord_1595453).sum := by decide
  have hdescent : baseEnd_1595453 < baseStart_1595453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595457 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1595457 : Nat := 118140960795 + 1595457 * 2 ^ 59
def prefixEnd_1595457 : Nat := 4983230072969 + 3 ^ 40 * 1595457 * 2
def baseEnd_1595457 : Nat := 273078768193489833616711

theorem tailTrace_1595457 : CollatzResearch.WordTrace tailWord_1595457 prefixEnd_1595457 273078768193489833616711 := by
  unfold tailWord_1595457
  simp only [CollatzResearch.WordTrace]
  refine ⟨58191097380939246207280625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38794064920626164138187083 58191097380939246207280625)
  ·
    refine ⟨43643323035704434655460469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58191097380939246207280625 43643323035704434655460469)
    ·
      refine ⟨4091561534597290748949419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43643323035704434655460469 4091561534597290748949419)
      ·
        refine ⟨6137342301895936123424129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091561534597290748949419 6137342301895936123424129)
        ·
          refine ⟨4603006726421952092568097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6137342301895936123424129 4603006726421952092568097)
          ·
            refine ⟨3452255044816464069426073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4603006726421952092568097 3452255044816464069426073)
            ·
              refine ⟨2589191283612348052069555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452255044816464069426073 2589191283612348052069555)
              ·
                refine ⟨3883786925418522078104333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589191283612348052069555 3883786925418522078104333)
                ·
                  refine ⟨1456420097031945779289125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3883786925418522078104333 1456420097031945779289125)
                  ·
                    refine ⟨273078768193489833616711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1456420097031945779289125 273078768193489833616711)
                    ·
                      rfl

theorem cell23_1595457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1595457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595457 prefixEnd_1595457 := by exact prefixLift 1595457
  have htrace : WordTrace (prefixWord ++ tailWord_1595457) baseStart_1595457 baseEnd_1595457 := by
    simpa [prefixWord, tailWord_1595457, baseEnd_1595457] using wordTrace_append hprefix tailTrace_1595457
  have hstable : (prefixWord ++ tailWord_1595457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595457).length < 2 ^ (prefixWord ++ tailWord_1595457).sum := by decide
  have hdescent : baseEnd_1595457 < baseStart_1595457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595500 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_1595500 : Nat := 118140960795 + 1595500 * 2 ^ 59
def prefixEnd_1595500 : Nat := 4983230072969 + 3 ^ 40 * 1595500 * 2
def baseEnd_1595500 : Nat := 273086128082870944204145

theorem tailTrace_1595500 : CollatzResearch.WordTrace tailWord_1595500 prefixEnd_1595500 273086128082870944204145 := by
  unfold tailWord_1595500
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096332859891732275547977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38795110479855643034063969 29096332859891732275547977)
  ·
    refine ⟨21822249644918799206660983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29096332859891732275547977 21822249644918799206660983)
    ·
      refine ⟨32733374467378198809991475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21822249644918799206660983 32733374467378198809991475)
      ·
        refine ⟨49100061701067298214987213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32733374467378198809991475 49100061701067298214987213)
        ·
          refine ⟨18412523137900236830620205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49100061701067298214987213 18412523137900236830620205)
          ·
            refine ⟨6904696176712588811482577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18412523137900236830620205 6904696176712588811482577)
            ·
              refine ⟨5178522132534441608611933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904696176712588811482577 5178522132534441608611933)
              ·
                refine ⟨1941945799700415603229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5178522132534441608611933 1941945799700415603229475)
                ·
                  refine ⟨2912918699550623404844213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941945799700415603229475 2912918699550623404844213)
                  ·
                    refine ⟨273086128082870944204145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2912918699550623404844213 273086128082870944204145)
                    ·
                      rfl

theorem cell23_1595500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_1595500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595500 prefixEnd_1595500 := by exact prefixLift 1595500
  have htrace : WordTrace (prefixWord ++ tailWord_1595500) baseStart_1595500 baseEnd_1595500 := by
    simpa [prefixWord, tailWord_1595500, baseEnd_1595500] using wordTrace_append hprefix tailTrace_1595500
  have hstable : (prefixWord ++ tailWord_1595500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595500).length < 2 ^ (prefixWord ++ tailWord_1595500).sum := by decide
  have hdescent : baseEnd_1595500 < baseStart_1595500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595534 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_1595534 : Nat := 118140960795 + 1595534 * 2 ^ 59
def prefixEnd_1595534 : Nat := 4983230072969 + 3 ^ 40 * 1595534 * 2
def baseEnd_1595534 : Nat := 273091947530288566529093

theorem tailTrace_1595534 : CollatzResearch.WordTrace tailWord_1595534 prefixEnd_1595534 273091947530288566529093 := by
  unfold tailWord_1595534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274238225207536044729207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38795937201106858905222437 7274238225207536044729207)
  ·
    refine ⟨10911357337811304067093811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7274238225207536044729207 10911357337811304067093811)
    ·
      refine ⟨16367036006716956100640717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10911357337811304067093811 16367036006716956100640717)
      ·
        refine ⟨6137638502518858537740269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16367036006716956100640717 6137638502518858537740269)
        ·
          refine ⟨2301614438444571951652601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6137638502518858537740269 2301614438444571951652601)
          ·
            refine ⟨1726210828833428963739451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301614438444571951652601 1726210828833428963739451)
            ·
              refine ⟨2589316243250143445609177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726210828833428963739451 2589316243250143445609177)
              ·
                refine ⟨1941987182437607584206883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589316243250143445609177 1941987182437607584206883)
                ·
                  refine ⟨2912980773656411376310325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941987182437607584206883 2912980773656411376310325)
                  ·
                    refine ⟨273091947530288566529093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2912980773656411376310325 273091947530288566529093)
                    ·
                      rfl

theorem cell23_1595534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_1595534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595534 prefixEnd_1595534 := by exact prefixLift 1595534
  have htrace : WordTrace (prefixWord ++ tailWord_1595534) baseStart_1595534 baseEnd_1595534 := by
    simpa [prefixWord, tailWord_1595534, baseEnd_1595534] using wordTrace_append hprefix tailTrace_1595534
  have hstable : (prefixWord ++ tailWord_1595534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595534).length < 2 ^ (prefixWord ++ tailWord_1595534).sum := by decide
  have hdescent : baseEnd_1595534 < baseStart_1595534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595570 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1595570 : Nat := 118140960795 + 1595570 * 2 ^ 59
def prefixEnd_1595570 : Nat := 4983230072969 + 3 ^ 40 * 1595570 * 2
def baseEnd_1595570 : Nat := 819294327894427558737113

theorem tailTrace_1595570 : CollatzResearch.WordTrace tailWord_1595570 prefixEnd_1595570 819294327894427558737113 := by
  unfold tailWord_1595570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548804707382466626536041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38796812553019911004096109 14548804707382466626536041)
  ·
    refine ⟨10911603530536849969902031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14548804707382466626536041 10911603530536849969902031)
    ·
      refine ⟨16367405295805274954853047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10911603530536849969902031 16367405295805274954853047)
      ·
        refine ⟨24551107943707912432279571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16367405295805274954853047 24551107943707912432279571)
        ·
          refine ⟨36826661915561868648419357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24551107943707912432279571 36826661915561868648419357)
          ·
            refine ⟨13809998218335700743157259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36826661915561868648419357 13809998218335700743157259)
            ·
              refine ⟨20714997327503551114735889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13809998218335700743157259 20714997327503551114735889)
              ·
                refine ⟨15536247995627663336051917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20714997327503551114735889 15536247995627663336051917)
                ·
                  refine ⟨5826092998360373751019469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15536247995627663336051917 5826092998360373751019469)
                  ·
                    refine ⟨2184784874385140156632301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5826092998360373751019469 2184784874385140156632301)
                    ·
                      refine ⟨819294327894427558737113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184784874385140156632301 819294327894427558737113)
                      ·
                        rfl

theorem cell23_1595570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1595570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595570 prefixEnd_1595570 := by exact prefixLift 1595570
  have htrace : WordTrace (prefixWord ++ tailWord_1595570) baseStart_1595570 baseEnd_1595570 := by
    simpa [prefixWord, tailWord_1595570, baseEnd_1595570] using wordTrace_append hprefix tailTrace_1595570
  have hstable : (prefixWord ++ tailWord_1595570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595570).length < 2 ^ (prefixWord ++ tailWord_1595570).sum := by decide
  have hdescent : baseEnd_1595570 < baseStart_1595570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595583 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1595583 : Nat := 118140960795 + 1595583 * 2 ^ 59
def prefixEnd_1595583 : Nat := 4983230072969 + 3 ^ 40 * 1595583 * 2
def baseEnd_1595583 : Nat := 819301003142936007874553

theorem tailTrace_1595583 : CollatzResearch.WordTrace tailWord_1595583 prefixEnd_1595583 819301003142936007874553 := by
  unfold tailWord_1595583
  simp only [CollatzResearch.WordTrace]
  refine ⟨58195692978482769726367403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38797128652321846484244935 58195692978482769726367403)
  ·
    refine ⟨87293539467724154589551105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58195692978482769726367403 87293539467724154589551105)
    ·
      refine ⟨65470154600793115942163329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87293539467724154589551105 65470154600793115942163329)
      ·
        refine ⟨49102615950594836956622497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65470154600793115942163329 49102615950594836956622497)
        ·
          refine ⟨36826961962946127717466873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49102615950594836956622497 36826961962946127717466873)
          ·
            refine ⟨27620221472209595788100155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36826961962946127717466873 27620221472209595788100155)
            ·
              refine ⟨41430332208314393682150233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27620221472209595788100155 41430332208314393682150233)
              ·
                refine ⟨31072749156235795261612675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41430332208314393682150233 31072749156235795261612675)
                ·
                  refine ⟨46609123734353692892419013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31072749156235795261612675 46609123734353692892419013)
                  ·
                    refine ⟨8739210700191317417328565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46609123734353692892419013 8739210700191317417328565)
                    ·
                      refine ⟨819301003142936007874553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8739210700191317417328565 819301003142936007874553)
                      ·
                        rfl

theorem cell23_1595583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1595583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595583 prefixEnd_1595583 := by exact prefixLift 1595583
  have htrace : WordTrace (prefixWord ++ tailWord_1595583) baseStart_1595583 baseEnd_1595583 := by
    simpa [prefixWord, tailWord_1595583, baseEnd_1595583] using wordTrace_append hprefix tailTrace_1595583
  have hstable : (prefixWord ++ tailWord_1595583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595583).length < 2 ^ (prefixWord ++ tailWord_1595583).sum := by decide
  have hdescent : baseEnd_1595583 < baseStart_1595583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595603 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 6, 6]
def baseStart_1595603 : Nat := 118140960795 + 1595603 * 2 ^ 59
def prefixEnd_1595603 : Nat := 4983230072969 + 3 ^ 40 * 1595603 * 2
def baseEnd_1595603 : Nat := 273103757585341976541487

theorem tailTrace_1595603 : CollatzResearch.WordTrace tailWord_1595603 prefixEnd_1595603 273103757585341976541487 := by
  unfold tailWord_1595603
  simp only [CollatzResearch.WordTrace]
  refine ⟨58196422438410313142095463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38797614958940208761396975 58196422438410313142095463)
  ·
    refine ⟨87294633657615469713143195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58196422438410313142095463 87294633657615469713143195)
    ·
      refine ⟨130941950486423204569714793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87294633657615469713143195 130941950486423204569714793)
      ·
        refine ⟨98206462864817403427286095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130941950486423204569714793 98206462864817403427286095)
        ·
          refine ⟨147309694297226105140929143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98206462864817403427286095 147309694297226105140929143)
          ·
            refine ⟨220964541445839157711393715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147309694297226105140929143 220964541445839157711393715)
            ·
              refine ⟨331446812168758736567090573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220964541445839157711393715 331446812168758736567090573)
              ·
                refine ⟨124292554563284526212658965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331446812168758736567090573 124292554563284526212658965)
                ·
                  refine ⟨5826213495153962166218389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124292554563284526212658965 5826213495153962166218389)
                  ·
                    refine ⟨273103757585341976541487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5826213495153962166218389 273103757585341976541487)
                    ·
                      rfl

theorem cell23_1595603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_1595603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595603 prefixEnd_1595603 := by exact prefixLift 1595603
  have htrace : WordTrace (prefixWord ++ tailWord_1595603) baseStart_1595603 baseEnd_1595603 := by
    simpa [prefixWord, tailWord_1595603, baseEnd_1595603] using wordTrace_append hprefix tailTrace_1595603
  have hstable : (prefixWord ++ tailWord_1595603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595603).length < 2 ^ (prefixWord ++ tailWord_1595603).sum := by decide
  have hdescent : baseEnd_1595603 < baseStart_1595603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595621 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1595621 : Nat := 118140960795 + 1595621 * 2 ^ 59
def prefixEnd_1595621 : Nat := 4983230072969 + 3 ^ 40 * 1595621 * 2
def baseEnd_1595621 : Nat := 819320515407806859199379

theorem tailTrace_1595621 : CollatzResearch.WordTrace tailWord_1595621 prefixEnd_1595621 819320515407806859199379 := by
  unfold tailWord_1595621
  simp only [CollatzResearch.WordTrace]
  refine ⟨58197078952345102216250717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38798052634896734810833811 58197078952345102216250717)
  ·
    refine ⟨21823904607129413331094019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58197078952345102216250717 21823904607129413331094019)
    ·
      refine ⟨32735856910694119996641029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21823904607129413331094019 32735856910694119996641029)
      ·
        refine ⟨6137973170755147499370193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32735856910694119996641029 6137973170755147499370193)
        ·
          refine ⟨4603479878066360624527645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6137973170755147499370193 4603479878066360624527645)
          ·
            refine ⟨1726304954274885234197867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4603479878066360624527645 1726304954274885234197867)
            ·
              refine ⟨2589457431412327851296801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726304954274885234197867 2589457431412327851296801)
              ·
                refine ⟨1942093073559245888472601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589457431412327851296801 1942093073559245888472601)
                ·
                  refine ⟨1456569805169434416354451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1942093073559245888472601 1456569805169434416354451)
                  ·
                    refine ⟨2184854707754151624531677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456569805169434416354451 2184854707754151624531677)
                    ·
                      refine ⟨819320515407806859199379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2184854707754151624531677 819320515407806859199379)
                      ·
                        rfl

theorem cell23_1595621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1595621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595621 prefixEnd_1595621 := by exact prefixLift 1595621
  have htrace : WordTrace (prefixWord ++ tailWord_1595621) baseStart_1595621 baseEnd_1595621 := by
    simpa [prefixWord, tailWord_1595621, baseEnd_1595621] using wordTrace_append hprefix tailTrace_1595621
  have hstable : (prefixWord ++ tailWord_1595621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595621).length < 2 ^ (prefixWord ++ tailWord_1595621).sum := by decide
  have hdescent : baseEnd_1595621 < baseStart_1595621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595630 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1595630 : Nat := 118140960795 + 1595630 * 2 ^ 59
def prefixEnd_1595630 : Nat := 4983230072969 + 3 ^ 40 * 1595630 * 2
def baseEnd_1595630 : Nat := 819325136733697323986837

theorem tailTrace_1595630 : CollatzResearch.WordTrace tailWord_1595630 prefixEnd_1595630 819325136733697323986837 := by
  unfold tailWord_1595630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274675901164062094166043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38798271472874997835552229 7274675901164062094166043)
  ·
    refine ⟨10912013851746093141249065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7274675901164062094166043 10912013851746093141249065)
    ·
      refine ⟨8184010388809569855936799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10912013851746093141249065 8184010388809569855936799)
      ·
        refine ⟨12276015583214354783905199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184010388809569855936799 12276015583214354783905199)
        ·
          refine ⟨18414023374821532175857799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12276015583214354783905199 18414023374821532175857799)
          ·
            refine ⟨27621035062232298263786699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18414023374821532175857799 27621035062232298263786699)
            ·
              refine ⟨41431552593348447395680049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27621035062232298263786699 41431552593348447395680049)
              ·
                refine ⟨31073664445011335546760037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41431552593348447395680049 31073664445011335546760037)
                ·
                  refine ⟨5826312083439625415017507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31073664445011335546760037 5826312083439625415017507)
                  ·
                    refine ⟨8739468125159438122526261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826312083439625415017507 8739468125159438122526261)
                    ·
                      refine ⟨819325136733697323986837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8739468125159438122526261 819325136733697323986837)
                      ·
                        rfl

theorem cell23_1595630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1595630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595630 prefixEnd_1595630 := by exact prefixLift 1595630
  have htrace : WordTrace (prefixWord ++ tailWord_1595630) baseStart_1595630 baseEnd_1595630 := by
    simpa [prefixWord, tailWord_1595630, baseEnd_1595630] using wordTrace_append hprefix tailTrace_1595630
  have hstable : (prefixWord ++ tailWord_1595630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595630).length < 2 ^ (prefixWord ++ tailWord_1595630).sum := by decide
  have hdescent : baseEnd_1595630 < baseStart_1595630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595643 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_1595643 : Nat := 118140960795 + 1595643 * 2 ^ 59
def prefixEnd_1595643 : Nat := 4983230072969 + 3 ^ 40 * 1595643 * 2
def baseEnd_1595643 : Nat := 819331811982205773124277

theorem tailTrace_1595643 : CollatzResearch.WordTrace tailWord_1595643 prefixEnd_1595643 819331811982205773124277 := by
  unfold tailWord_1595643
  simp only [CollatzResearch.WordTrace]
  refine ⟨58197881358265399973551583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38798587572176933315701055 58197881358265399973551583)
  ·
    refine ⟨87296822037398099960327375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58197881358265399973551583 87296822037398099960327375)
    ·
      refine ⟨130945233056097149940491063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87296822037398099960327375 130945233056097149940491063)
      ·
        refine ⟨196417849584145724910736595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130945233056097149940491063 196417849584145724910736595)
        ·
          refine ⟨294626774376218587366104893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196417849584145724910736595 294626774376218587366104893)
          ·
            refine ⟨110485040391081970262289335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294626774376218587366104893 110485040391081970262289335)
            ·
              refine ⟨165727560586622955393434003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110485040391081970262289335 165727560586622955393434003)
              ·
                refine ⟨248591340879934433090151005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165727560586622955393434003 248591340879934433090151005)
                ·
                  refine ⟨93221752829975412408806627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248591340879934433090151005 93221752829975412408806627)
                  ·
                    refine ⟨139832629244963118613209941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93221752829975412408806627 139832629244963118613209941)
                    ·
                      refine ⟨819331811982205773124277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 139832629244963118613209941 819331811982205773124277)
                      ·
                        rfl

theorem cell23_1595643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_1595643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595643 prefixEnd_1595643 := by exact prefixLift 1595643
  have htrace : WordTrace (prefixWord ++ tailWord_1595643) baseStart_1595643 baseEnd_1595643 := by
    simpa [prefixWord, tailWord_1595643, baseEnd_1595643] using wordTrace_append hprefix tailTrace_1595643
  have hstable : (prefixWord ++ tailWord_1595643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595643).length < 2 ^ (prefixWord ++ tailWord_1595643).sum := by decide
  have hdescent : baseEnd_1595643 < baseStart_1595643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595644 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_1595644 : Nat := 118140960795 + 1595644 * 2 ^ 59
def prefixEnd_1595644 : Nat := 4983230072969 + 3 ^ 40 * 1595644 * 2
def baseEnd_1595644 : Nat := 819332325462860269211773

theorem tailTrace_1595644 : CollatzResearch.WordTrace tailWord_1595644 prefixEnd_1595644 819332325462860269211773 := by
  unfold tailWord_1595644
  simp only [CollatzResearch.WordTrace]
  refine ⟨29098958915630888572168993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38798611887507851429558657 29098958915630888572168993)
  ·
    refine ⟨21824219186723166429126745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29098958915630888572168993 21824219186723166429126745)
    ·
      refine ⟨16368164390042374821845059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21824219186723166429126745 16368164390042374821845059)
      ·
        refine ⟨24552246585063562232767589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16368164390042374821845059 24552246585063562232767589)
        ·
          refine ⟨4603546234699417918643923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24552246585063562232767589 4603546234699417918643923)
          ·
            refine ⟨6905319352049126877965885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603546234699417918643923 6905319352049126877965885)
            ·
              refine ⟨2589494757018422579237207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6905319352049126877965885 2589494757018422579237207)
              ·
                refine ⟨3884242135527633868855811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589494757018422579237207 3884242135527633868855811)
                ·
                  refine ⟨5826363203291450803283717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884242135527633868855811 5826363203291450803283717)
                  ·
                    refine ⟨1092443100617147025615697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826363203291450803283717 1092443100617147025615697)
                    ·
                      refine ⟨819332325462860269211773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092443100617147025615697 819332325462860269211773)
                      ·
                        rfl

theorem cell23_1595644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_1595644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595644 prefixEnd_1595644 := by exact prefixLift 1595644
  have htrace : WordTrace (prefixWord ++ tailWord_1595644) baseStart_1595644 baseEnd_1595644 := by
    simpa [prefixWord, tailWord_1595644, baseEnd_1595644] using wordTrace_append hprefix tailTrace_1595644
  have hstable : (prefixWord ++ tailWord_1595644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595644).length < 2 ^ (prefixWord ++ tailWord_1595644).sum := by decide
  have hdescent : baseEnd_1595644 < baseStart_1595644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595678 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1595678 : Nat := 118140960795 + 1595678 * 2 ^ 59
def prefixEnd_1595678 : Nat := 4983230072969 + 3 ^ 40 * 1595678 * 2
def baseEnd_1595678 : Nat := 819349783805113136186617

theorem tailTrace_1595678 : CollatzResearch.WordTrace tailWord_1595678 prefixEnd_1595678 819349783805113136186617 := by
  unfold tailWord_1595678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274894739142325118884461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38799438608759067300717125 7274894739142325118884461)
  ·
    refine ⟨2728085527178371919581673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7274894739142325118884461 2728085527178371919581673)
    ·
      refine ⟨2046064145383778939686255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2728085527178371919581673 2046064145383778939686255)
      ·
        refine ⟨3069096218075668409529383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046064145383778939686255 3069096218075668409529383)
        ·
          refine ⟨4603644327113502614294075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069096218075668409529383 4603644327113502614294075)
          ·
            refine ⟨6905466490670253921441113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603644327113502614294075 6905466490670253921441113)
            ·
              refine ⟨5179099868002690441080835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6905466490670253921441113 5179099868002690441080835)
              ·
                refine ⟨7768649802004035661621253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5179099868002690441080835 7768649802004035661621253)
                ·
                  refine ⟨1456621837875756686553985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7768649802004035661621253 1456621837875756686553985)
                  ·
                    refine ⟨1092466378406817514915489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456621837875756686553985 1092466378406817514915489)
                    ·
                      refine ⟨819349783805113136186617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092466378406817514915489 819349783805113136186617)
                      ·
                        rfl

theorem cell23_1595678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1595678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595678 prefixEnd_1595678 := by exact prefixLift 1595678
  have htrace : WordTrace (prefixWord ++ tailWord_1595678) baseStart_1595678 baseEnd_1595678 := by
    simpa [prefixWord, tailWord_1595678, baseEnd_1595678] using wordTrace_append hprefix tailTrace_1595678
  have hstable : (prefixWord ++ tailWord_1595678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595678).length < 2 ^ (prefixWord ++ tailWord_1595678).sum := by decide
  have hdescent : baseEnd_1595678 < baseStart_1595678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595717 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_1595717 : Nat := 118140960795 + 1595717 * 2 ^ 59
def prefixEnd_1595717 : Nat := 4983230072969 + 3 ^ 40 * 1595717 * 2
def baseEnd_1595717 : Nat := 819369809550638483598937

theorem tailTrace_1595717 : CollatzResearch.WordTrace tailWord_1595717 prefixEnd_1595717 819369809550638483598937 := by
  unfold tailWord_1595717
  simp only [CollatzResearch.WordTrace]
  refine ⟨58200580359997310611745405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38800386906664873741163603 58200580359997310611745405)
  ·
    refine ⟨21825217634998991479404527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58200580359997310611745405 21825217634998991479404527)
    ·
      refine ⟨32737826452498487219106791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21825217634998991479404527 32737826452498487219106791)
      ·
        refine ⟨49106739678747730828660187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32737826452498487219106791 49106739678747730828660187)
        ·
          refine ⟨73660109518121596242990281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49106739678747730828660187 73660109518121596242990281)
          ·
            refine ⟨55245082138591197182242711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73660109518121596242990281 55245082138591197182242711)
            ·
              refine ⟨82867623207886795773364067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55245082138591197182242711 82867623207886795773364067)
              ·
                refine ⟨124301434811830193660046101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82867623207886795773364067 124301434811830193660046101)
                ·
                  refine ⟨5826629756804540327814661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124301434811830193660046101 5826629756804540327814661)
                  ·
                    refine ⟨1092493079400851311465249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5826629756804540327814661 1092493079400851311465249)
                    ·
                      refine ⟨819369809550638483598937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092493079400851311465249 819369809550638483598937)
                      ·
                        rfl

theorem cell23_1595717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_1595717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595717 prefixEnd_1595717 := by exact prefixLift 1595717
  have htrace : WordTrace (prefixWord ++ tailWord_1595717) baseStart_1595717 baseEnd_1595717 := by
    simpa [prefixWord, tailWord_1595717, baseEnd_1595717] using wordTrace_append hprefix tailTrace_1595717
  have hstable : (prefixWord ++ tailWord_1595717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595717).length < 2 ^ (prefixWord ++ tailWord_1595717).sum := by decide
  have hdescent : baseEnd_1595717 < baseStart_1595717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595757 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1595757 : Nat := 118140960795 + 1595757 * 2 ^ 59
def prefixEnd_1595757 : Nat := 4983230072969 + 3 ^ 40 * 1595757 * 2
def baseEnd_1595757 : Nat := 91043372086313147455417

theorem tailTrace_1595757 : CollatzResearch.WordTrace tailWord_1595757 prefixEnd_1595757 91043372086313147455417 := by
  unfold tailWord_1595757
  simp only [CollatzResearch.WordTrace]
  refine ⟨58202039279852397443201525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38801359519901598295467683 58202039279852397443201525)
  ·
    refine ⟨5456441182486162260300143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58202039279852397443201525 5456441182486162260300143)
    ·
      refine ⟨8184661773729243390450215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5456441182486162260300143 8184661773729243390450215)
      ·
        refine ⟨12276992660593865085675323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184661773729243390450215 12276992660593865085675323)
        ·
          refine ⟨18415488990890797628512985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12276992660593865085675323 18415488990890797628512985)
          ·
            refine ⟨13811616743168098221384739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18415488990890797628512985 13811616743168098221384739)
            ·
              refine ⟨20717425114752147332077109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811616743168098221384739 20717425114752147332077109)
              ·
                refine ⟨1942258604508013812382229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20717425114752147332077109 1942258604508013812382229)
                ·
                  refine ⟨91043372086313147455417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1942258604508013812382229 91043372086313147455417)
                  ·
                    rfl

theorem cell23_1595757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1595757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595757 prefixEnd_1595757 := by exact prefixLift 1595757
  have htrace : WordTrace (prefixWord ++ tailWord_1595757) baseStart_1595757 baseEnd_1595757 := by
    simpa [prefixWord, tailWord_1595757, baseEnd_1595757] using wordTrace_append hprefix tailTrace_1595757
  have hstable : (prefixWord ++ tailWord_1595757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595757).length < 2 ^ (prefixWord ++ tailWord_1595757).sum := by decide
  have hdescent : baseEnd_1595757 < baseStart_1595757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595784 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1595784 : Nat := 118140960795 + 1595784 * 2 ^ 59
def prefixEnd_1595784 : Nat := 4983230072969 + 3 ^ 40 * 1595784 * 2
def baseEnd_1595784 : Nat := 819404212754489721461129

theorem tailTrace_1595784 : CollatzResearch.WordTrace tailWord_1595784 prefixEnd_1595784 819404212754489721461129 := by
  unfold tailWord_1595784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29101512025377290527217203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38802016033836387369622937 29101512025377290527217203)
  ·
    refine ⟨43652268038065935790825805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29101512025377290527217203 43652268038065935790825805)
    ·
      refine ⟨16369600514274725921559677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43652268038065935790825805 16369600514274725921559677)
      ·
        refine ⟨6138600192853022220584879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16369600514274725921559677 6138600192853022220584879)
        ·
          refine ⟨9207900289279533330877319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138600192853022220584879 9207900289279533330877319)
          ·
            refine ⟨13811850433919299996315979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207900289279533330877319 13811850433919299996315979)
            ·
              refine ⟨20717775650878949994473969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811850433919299996315979 20717775650878949994473969)
              ·
                refine ⟨15538331738159212495855477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20717775650878949994473969 15538331738159212495855477)
                ·
                  refine ⟨1456718600452426171486451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15538331738159212495855477 1456718600452426171486451)
                  ·
                    refine ⟨2185077900678639257229677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456718600452426171486451 2185077900678639257229677)
                    ·
                      refine ⟨819404212754489721461129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185077900678639257229677 819404212754489721461129)
                      ·
                        rfl

theorem cell23_1595784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1595784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595784 prefixEnd_1595784 := by exact prefixLift 1595784
  have htrace : WordTrace (prefixWord ++ tailWord_1595784) baseStart_1595784 baseEnd_1595784 := by
    simpa [prefixWord, tailWord_1595784, baseEnd_1595784] using wordTrace_append hprefix tailTrace_1595784
  have hstable : (prefixWord ++ tailWord_1595784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595784).length < 2 ^ (prefixWord ++ tailWord_1595784).sum := by decide
  have hdescent : baseEnd_1595784 < baseStart_1595784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595801 : List Nat := [1, 2, 1, 2, 1, 4, 1, 6, 1, 1, 3]
def baseStart_1595801 : Nat := 118140960795 + 1595801 * 2 ^ 59
def prefixEnd_1595801 : Nat := 4983230072969 + 3 ^ 40 * 1595801 * 2
def baseEnd_1595801 : Nat := 819412941925616154948551

theorem tailTrace_1595801 : CollatzResearch.WordTrace tailWord_1595801 prefixEnd_1595801 819412941925616154948551 := by
  unfold tailWord_1595801
  simp only [CollatzResearch.WordTrace]
  refine ⟨58203644091692992957803257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38802429394461995305202171 58203644091692992957803257)
  ·
    refine ⟨43652733068769744718352443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58203644091692992957803257 43652733068769744718352443)
    ·
      refine ⟨65479099603154617077528665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43652733068769744718352443 65479099603154617077528665)
      ·
        refine ⟨49109324702365962808146499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65479099603154617077528665 49109324702365962808146499)
        ·
          refine ⟨73663987053548944212219749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49109324702365962808146499 73663987053548944212219749)
          ·
            refine ⟨13811997572540427039791203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73663987053548944212219749 13811997572540427039791203)
            ·
              refine ⟨20717996358810640559686805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811997572540427039791203 20717996358810640559686805)
              ·
                refine ⟨971156079319248776235319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20717996358810640559686805 971156079319248776235319)
                ·
                  refine ⟨1456734118978873164352979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971156079319248776235319 1456734118978873164352979)
                  ·
                    refine ⟨2185101178468309746529469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456734118978873164352979 2185101178468309746529469)
                    ·
                      refine ⟨819412941925616154948551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185101178468309746529469 819412941925616154948551)
                      ·
                        rfl

theorem cell23_1595801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_1595801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595801 prefixEnd_1595801 := by exact prefixLift 1595801
  have htrace : WordTrace (prefixWord ++ tailWord_1595801) baseStart_1595801 baseEnd_1595801 := by
    simpa [prefixWord, tailWord_1595801, baseEnd_1595801] using wordTrace_append hprefix tailTrace_1595801
  have hstable : (prefixWord ++ tailWord_1595801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595801).length < 2 ^ (prefixWord ++ tailWord_1595801).sum := by decide
  have hdescent : baseEnd_1595801 < baseStart_1595801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595847 : List Nat := [1, 1, 4, 1, 1, 6, 9]
def baseStart_1595847 : Nat := 118140960795 + 1595847 * 2 ^ 59
def prefixEnd_1595847 : Nat := 4983230072969 + 3 ^ 40 * 1595847 * 2
def baseEnd_1595847 : Nat := 10116500765873123147819

theorem tailTrace_1595847 : CollatzResearch.WordTrace tailWord_1595847 prefixEnd_1595847 10116500765873123147819 := by
  unfold tailWord_1595847
  simp only [CollatzResearch.WordTrace]
  refine ⟨58205321849526342813977795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38803547899684228542651863 58205321849526342813977795)
  ·
    refine ⟨87307982774289514220966693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58205321849526342813977795 87307982774289514220966693)
    ·
      refine ⟨16370246770179283916431255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87307982774289514220966693 16370246770179283916431255)
      ·
        refine ⟨24555370155268925874646883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16370246770179283916431255 24555370155268925874646883)
        ·
          refine ⟨36833055232903388811970325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24555370155268925874646883 36833055232903388811970325)
          ·
            refine ⟨1726549464042346350561109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36833055232903388811970325 1726549464042346350561109)
            ·
              refine ⟨10116500765873123147819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1726549464042346350561109 10116500765873123147819)
              ·
                rfl

theorem cell23_1595847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 9].length) (baseStart_1595847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595847 prefixEnd_1595847 := by exact prefixLift 1595847
  have htrace : WordTrace (prefixWord ++ tailWord_1595847) baseStart_1595847 baseEnd_1595847 := by
    simpa [prefixWord, tailWord_1595847, baseEnd_1595847] using wordTrace_append hprefix tailTrace_1595847
  have hstable : (prefixWord ++ tailWord_1595847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595847).length < 2 ^ (prefixWord ++ tailWord_1595847).sum := by decide
  have hdescent : baseEnd_1595847 < baseStart_1595847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595907 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 2, 6]
def baseStart_1595907 : Nat := 118140960795 + 1595907 * 2 ^ 59
def prefixEnd_1595907 : Nat := 4983230072969 + 3 ^ 40 * 1595907 * 2
def baseEnd_1595907 : Nat := 273155790291664246741021

theorem tailTrace_1595907 : CollatzResearch.WordTrace tailWord_1595907 prefixEnd_1595907 273155790291664246741021 := by
  unfold tailWord_1595907
  simp only [CollatzResearch.WordTrace]
  refine ⟨58207510229308973061161975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38805006819539315374107983 58207510229308973061161975)
  ·
    refine ⟨87311265343963459591742963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58207510229308973061161975 87311265343963459591742963)
    ·
      refine ⟨130966898015945189387614445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87311265343963459591742963 130966898015945189387614445)
      ·
        refine ⟨49112586755979446020355417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130966898015945189387614445 49112586755979446020355417)
        ·
          refine ⟨36834440066984584515266563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49112586755979446020355417 36834440066984584515266563)
          ·
            refine ⟨55251660100476876772899845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36834440066984584515266563 55251660100476876772899845)
            ·
              refine ⟨10359686268839414394918721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55251660100476876772899845 10359686268839414394918721)
              ·
                refine ⟨7769764701629560796189041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10359686268839414394918721 7769764701629560796189041)
                ·
                  refine ⟨5827323526222170597141781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7769764701629560796189041 5827323526222170597141781)
                  ·
                    refine ⟨273155790291664246741021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5827323526222170597141781 273155790291664246741021)
                    ·
                      rfl

theorem cell23_1595907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_1595907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595907 prefixEnd_1595907 := by exact prefixLift 1595907
  have htrace : WordTrace (prefixWord ++ tailWord_1595907) baseStart_1595907 baseEnd_1595907 := by
    simpa [prefixWord, tailWord_1595907, baseEnd_1595907] using wordTrace_append hprefix tailTrace_1595907
  have hstable : (prefixWord ++ tailWord_1595907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595907).length < 2 ^ (prefixWord ++ tailWord_1595907).sum := by decide
  have hdescent : baseEnd_1595907 < baseStart_1595907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595908 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1595908 : Nat := 118140960795 + 1595908 * 2 ^ 59
def prefixEnd_1595908 : Nat := 4983230072969 + 3 ^ 40 * 1595908 * 2
def baseEnd_1595908 : Nat := 819467884355647236310559

theorem tailTrace_1595908 : CollatzResearch.WordTrace tailWord_1595908 prefixEnd_1595908 819467884355647236310559 := by
  unfold tailWord_1595908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103773351152675115974189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38805031134870233487965585 29103773351152675115974189)
  ·
    refine ⟨10913915006682253168490321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29103773351152675115974189 10913915006682253168490321)
    ·
      refine ⟨8185436255011689876367741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10913915006682253168490321 8185436255011689876367741)
      ·
        refine ⟨3069538595629383703637903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8185436255011689876367741 3069538595629383703637903)
        ·
          refine ⟨4604307893444075555456855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069538595629383703637903 4604307893444075555456855)
          ·
            refine ⟨6906461840166113333185283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604307893444075555456855 6906461840166113333185283)
            ·
              refine ⟨10359692760249169999777925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6906461840166113333185283 10359692760249169999777925)
              ·
                refine ⟨1942442392546719374958361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10359692760249169999777925 1942442392546719374958361)
                ·
                  refine ⟨1456831794410039531218771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1942442392546719374958361 1456831794410039531218771)
                  ·
                    refine ⟨2185247691615059296828157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456831794410039531218771 2185247691615059296828157)
                    ·
                      refine ⟨819467884355647236310559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185247691615059296828157 819467884355647236310559)
                      ·
                        rfl

theorem cell23_1595908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1595908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595908 prefixEnd_1595908 := by exact prefixLift 1595908
  have htrace : WordTrace (prefixWord ++ tailWord_1595908) baseStart_1595908 baseEnd_1595908 := by
    simpa [prefixWord, tailWord_1595908, baseEnd_1595908] using wordTrace_append hprefix tailTrace_1595908
  have hstable : (prefixWord ++ tailWord_1595908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595908).length < 2 ^ (prefixWord ++ tailWord_1595908).sum := by decide
  have hdescent : baseEnd_1595908 < baseStart_1595908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1595965 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1595965 : Nat := 118140960795 + 1595965 * 2 ^ 59
def prefixEnd_1595965 : Nat := 4983230072969 + 3 ^ 40 * 1595965 * 2
def baseEnd_1595965 : Nat := 819497152752953513297797

theorem tailTrace_1595965 : CollatzResearch.WordTrace tailWord_1595965 prefixEnd_1595965 819497152752953513297797 := by
  unfold tailWord_1595965
  simp only [CollatzResearch.WordTrace]
  refine ⟨58209625663098848966773349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38806417108732565977848899 58209625663098848966773349)
  ·
    refine ⟨10914304811831034181270003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58209625663098848966773349 10914304811831034181270003)
    ·
      refine ⟨16371457217746551271905005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10914304811831034181270003 16371457217746551271905005)
      ·
        refine ⟨6139296456654956726964377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16371457217746551271905005 6139296456654956726964377)
        ·
          refine ⟨4604472342491217545223283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6139296456654956726964377 4604472342491217545223283)
          ·
            refine ⟨6906708513736826317834925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604472342491217545223283 6906708513736826317834925)
            ·
              refine ⟨2590015692651309869188097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6906708513736826317834925 2590015692651309869188097)
              ·
                refine ⟨1942511769488482401891073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590015692651309869188097 1942511769488482401891073)
                ·
                  refine ⟨1456883827116361801418305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1942511769488482401891073 1456883827116361801418305)
                  ·
                    refine ⟨1092662870337271351063729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456883827116361801418305 1092662870337271351063729)
                    ·
                      refine ⟨819497152752953513297797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092662870337271351063729 819497152752953513297797)
                      ·
                        rfl

theorem cell23_1595965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1595965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1595965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1595965 prefixEnd_1595965 := by exact prefixLift 1595965
  have htrace : WordTrace (prefixWord ++ tailWord_1595965) baseStart_1595965 baseEnd_1595965 := by
    simpa [prefixWord, tailWord_1595965, baseEnd_1595965] using wordTrace_append hprefix tailTrace_1595965
  have hstable : (prefixWord ++ tailWord_1595965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1595965).length < 2 ^ (prefixWord ++ tailWord_1595965).sum := by decide
  have hdescent : baseEnd_1595965 < baseStart_1595965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1595965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596004 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_1596004 : Nat := 118140960795 + 1596004 * 2 ^ 59
def prefixEnd_1596004 : Nat := 4983230072969 + 3 ^ 40 * 1596004 * 2
def baseEnd_1596004 : Nat := 819517178498478860710117

theorem tailTrace_1596004 : CollatzResearch.WordTrace tailWord_1596004 prefixEnd_1596004 819517178498478860710117 := by
  unfold tailWord_1596004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105524054978779313721533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38807365406638372418295377 29105524054978779313721533)
  ·
    refine ⟨10914571520617042242645575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29105524054978779313721533 10914571520617042242645575)
    ·
      refine ⟨16371857280925563363968363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10914571520617042242645575 16371857280925563363968363)
      ·
        refine ⟨24557785921388345045952545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16371857280925563363968363 24557785921388345045952545)
        ·
          refine ⟨18418339441041258784464409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24557785921388345045952545 18418339441041258784464409)
          ·
            refine ⟨13813754580780944088348307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18418339441041258784464409 13813754580780944088348307)
            ·
              refine ⟨20720631871171416132522461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813754580780944088348307 20720631871171416132522461)
              ·
                refine ⟨7770236951689281049695923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20720631871171416132522461 7770236951689281049695923)
                ·
                  refine ⟨11655355427533921574543885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770236951689281049695923 11655355427533921574543885)
                  ·
                    refine ⟨4370758285325220590453957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11655355427533921574543885 4370758285325220590453957)
                    ·
                      refine ⟨819517178498478860710117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4370758285325220590453957 819517178498478860710117)
                      ·
                        rfl

theorem cell23_1596004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_1596004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596004 prefixEnd_1596004 := by exact prefixLift 1596004
  have htrace : WordTrace (prefixWord ++ tailWord_1596004) baseStart_1596004 baseEnd_1596004 := by
    simpa [prefixWord, tailWord_1596004, baseEnd_1596004] using wordTrace_append hprefix tailTrace_1596004
  have hstable : (prefixWord ++ tailWord_1596004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596004).length < 2 ^ (prefixWord ++ tailWord_1596004).sum := by decide
  have hdescent : baseEnd_1596004 < baseStart_1596004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596005 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 5]
def baseStart_1596005 : Nat := 118140960795 + 1596005 * 2 ^ 59
def prefixEnd_1596005 : Nat := 4983230072969 + 3 ^ 40 * 1596005 * 2
def baseEnd_1596005 : Nat := 91057521331014817421957

theorem tailTrace_1596005 : CollatzResearch.WordTrace tailWord_1596005 prefixEnd_1596005 91057521331014817421957 := by
  unfold tailWord_1596005
  simp only [CollatzResearch.WordTrace]
  refine ⟨58211084582953935798229469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38807389721969290532152979 58211084582953935798229469)
  ·
    refine ⟨21829156718607725924336051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58211084582953935798229469 21829156718607725924336051)
    ·
      refine ⟨32743735077911588886504077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829156718607725924336051 32743735077911588886504077)
      ·
        refine ⟨12278900654216845832439029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32743735077911588886504077 12278900654216845832439029)
        ·
          refine ⟨1151146936332829296791159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12278900654216845832439029 1151146936332829296791159)
          ·
            refine ⟨1726720404499243945186739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151146936332829296791159 1726720404499243945186739)
            ·
              refine ⟨2590080606748865917780109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726720404499243945186739 2590080606748865917780109)
              ·
                refine ⟨971280227530824719167541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2590080606748865917780109 971280227530824719167541)
                ·
                  refine ⟨91057521331014817421957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 971280227530824719167541 91057521331014817421957)
                  ·
                    rfl

theorem cell23_1596005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_1596005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596005 prefixEnd_1596005 := by exact prefixLift 1596005
  have htrace : WordTrace (prefixWord ++ tailWord_1596005) baseStart_1596005 baseEnd_1596005 := by
    simpa [prefixWord, tailWord_1596005, baseEnd_1596005] using wordTrace_append hprefix tailTrace_1596005
  have hstable : (prefixWord ++ tailWord_1596005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596005).length < 2 ^ (prefixWord ++ tailWord_1596005).sum := by decide
  have hdescent : baseEnd_1596005 < baseStart_1596005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596078 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_1596078 : Nat := 118140960795 + 1596078 * 2 ^ 59
def prefixEnd_1596078 : Nat := 4983230072969 + 3 ^ 40 * 1596078 * 2
def baseEnd_1596078 : Nat := 91061686229656841242753

theorem tailTrace_1596078 : CollatzResearch.WordTrace tailWord_1596078 prefixEnd_1596078 91061686229656841242753 := by
  unfold tailWord_1596078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276718388961183658204611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38809164741126312843757925 7276718388961183658204611)
  ·
    refine ⟨10915077583441775487306917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7276718388961183658204611 10915077583441775487306917)
    ·
      refine ⟨2046577046895332903870047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10915077583441775487306917 2046577046895332903870047)
      ·
        refine ⟨3069865570342999355805071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046577046895332903870047 3069865570342999355805071)
        ·
          refine ⟨4604798355514499033707607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069865570342999355805071 4604798355514499033707607)
          ·
            refine ⟨6907197533271748550561411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4604798355514499033707607 6907197533271748550561411)
            ·
              refine ⟨10360796299907622825842117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907197533271748550561411 10360796299907622825842117)
              ·
                refine ⟨1942649306232679279845397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10360796299907622825842117 1942649306232679279845397)
                ·
                  refine ⟨91061686229656841242753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1942649306232679279845397 91061686229656841242753)
                  ·
                    rfl

theorem cell23_1596078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_1596078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596078 prefixEnd_1596078 := by exact prefixLift 1596078
  have htrace : WordTrace (prefixWord ++ tailWord_1596078) baseStart_1596078 baseEnd_1596078 := by
    simpa [prefixWord, tailWord_1596078, baseEnd_1596078] using wordTrace_append hprefix tailTrace_1596078
  have hstable : (prefixWord ++ tailWord_1596078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596078).length < 2 ^ (prefixWord ++ tailWord_1596078).sum := by decide
  have hdescent : baseEnd_1596078 < baseStart_1596078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596109 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1596109 : Nat := 118140960795 + 1596109 * 2 ^ 59
def prefixEnd_1596109 : Nat := 4983230072969 + 3 ^ 40 * 1596109 * 2
def baseEnd_1596109 : Nat := 819571093967200949897135

theorem tailTrace_1596109 : CollatzResearch.WordTrace tailWord_1596109 prefixEnd_1596109 819571093967200949897135 := by
  unfold tailWord_1596109
  simp only [CollatzResearch.WordTrace]
  refine ⟨58214877774577161560015381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38809918516384774373343587 58214877774577161560015381)
  ·
    refine ⟨2728822395683304448125721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58214877774577161560015381 2728822395683304448125721)
    ·
      refine ⟨2046616796762478336094291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2728822395683304448125721 2046616796762478336094291)
      ·
        refine ⟨3069925195143717504141437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046616796762478336094291 3069925195143717504141437)
        ·
          refine ⟨1151221948178894064053039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3069925195143717504141437 1151221948178894064053039)
          ·
            refine ⟨1726832922268341096079559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151221948178894064053039 1726832922268341096079559)
            ·
              refine ⟨2590249383402511644119339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726832922268341096079559 2590249383402511644119339)
              ·
                refine ⟨3885374075103767466179009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590249383402511644119339 3885374075103767466179009)
                ·
                  refine ⟨2914030556327825599634257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885374075103767466179009 2914030556327825599634257)
                  ·
                    refine ⟨2185522917245869199725693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914030556327825599634257 2185522917245869199725693)
                    ·
                      refine ⟨819571093967200949897135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185522917245869199725693 819571093967200949897135)
                      ·
                        rfl

theorem cell23_1596109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1596109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596109 prefixEnd_1596109 := by exact prefixLift 1596109
  have htrace : WordTrace (prefixWord ++ tailWord_1596109) baseStart_1596109 baseEnd_1596109 := by
    simpa [prefixWord, tailWord_1596109, baseEnd_1596109] using wordTrace_append hprefix tailTrace_1596109
  have hstable : (prefixWord ++ tailWord_1596109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596109).length < 2 ^ (prefixWord ++ tailWord_1596109).sum := by decide
  have hdescent : baseEnd_1596109 < baseStart_1596109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596121 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_1596121 : Nat := 118140960795 + 1596121 * 2 ^ 59
def prefixEnd_1596121 : Nat := 4983230072969 + 3 ^ 40 * 1596121 * 2
def baseEnd_1596121 : Nat := 273192418578351634315693

theorem tailTrace_1596121 : CollatzResearch.WordTrace tailWord_1596121 prefixEnd_1596121 273192418578351634315693 := by
  unfold tailWord_1596121
  simp only [CollatzResearch.WordTrace]
  refine ⟨58215315450533687609452217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38810210300355791739634811 58215315450533687609452217)
  ·
    refine ⟨43661486587900265707089163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58215315450533687609452217 43661486587900265707089163)
    ·
      refine ⟨65492229881850398560633745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43661486587900265707089163 65492229881850398560633745)
      ·
        refine ⟨49119172411387798920475309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65492229881850398560633745 49119172411387798920475309)
        ·
          refine ⟨18419689654270424595178241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49119172411387798920475309 18419689654270424595178241)
          ·
            refine ⟨13814767240702818446383681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18419689654270424595178241 13814767240702818446383681)
            ·
              refine ⟨10361075430527113834787761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814767240702818446383681 10361075430527113834787761)
              ·
                refine ⟨7770806572895335376090821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10361075430527113834787761 7770806572895335376090821)
                ·
                  refine ⟨1457026232417875383017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7770806572895335376090821 1457026232417875383017029)
                  ·
                    refine ⟨273192418578351634315693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1457026232417875383017029 273192418578351634315693)
                    ·
                      rfl

theorem cell23_1596121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_1596121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596121 prefixEnd_1596121 := by exact prefixLift 1596121
  have htrace : WordTrace (prefixWord ++ tailWord_1596121) baseStart_1596121 baseEnd_1596121 := by
    simpa [prefixWord, tailWord_1596121, baseEnd_1596121] using wordTrace_append hprefix tailTrace_1596121
  have hstable : (prefixWord ++ tailWord_1596121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596121).length < 2 ^ (prefixWord ++ tailWord_1596121).sum := by decide
  have hdescent : baseEnd_1596121 < baseStart_1596121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596128 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2]
def baseStart_1596128 : Nat := 118140960795 + 1596128 * 2 ^ 59
def prefixEnd_1596128 : Nat := 4983230072969 + 3 ^ 40 * 1596128 * 2
def baseEnd_1596128 : Nat := 819580850099636375559547

theorem tailTrace_1596128 : CollatzResearch.WordTrace tailWord_1596128 prefixEnd_1596128 819580850099636375559547 := by
  unfold tailWord_1596128
  simp only [CollatzResearch.WordTrace]
  refine ⟨29107785380754163902478519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38810380507672218536638025 29107785380754163902478519)
  ·
    refine ⟨43661678071131245853717779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29107785380754163902478519 43661678071131245853717779)
    ·
      refine ⟨65492517106696868780576669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43661678071131245853717779 65492517106696868780576669)
      ·
        refine ⟨24559693915011325792716251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65492517106696868780576669 24559693915011325792716251)
        ·
          refine ⟨36839540872516988689074377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24559693915011325792716251 36839540872516988689074377)
          ·
            refine ⟨27629655654387741516805783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36839540872516988689074377 27629655654387741516805783)
            ·
              refine ⟨41444483481581612275208675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27629655654387741516805783 41444483481581612275208675)
              ·
                refine ⟨62166725222372418412813013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41444483481581612275208675 62166725222372418412813013)
                ·
                  refine ⟨1457032622399353556550305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62166725222372418412813013 1457032622399353556550305)
                  ·
                    refine ⟨1092774466799515167412729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457032622399353556550305 1092774466799515167412729)
                    ·
                      refine ⟨819580850099636375559547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092774466799515167412729 819580850099636375559547)
                      ·
                        rfl

theorem cell23_1596128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_1596128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596128 prefixEnd_1596128 := by exact prefixLift 1596128
  have htrace : WordTrace (prefixWord ++ tailWord_1596128) baseStart_1596128 baseEnd_1596128 := by
    simpa [prefixWord, tailWord_1596128, baseEnd_1596128] using wordTrace_append hprefix tailTrace_1596128
  have hstable : (prefixWord ++ tailWord_1596128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596128).length < 2 ^ (prefixWord ++ tailWord_1596128).sum := by decide
  have hdescent : baseEnd_1596128 < baseStart_1596128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596141 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1596141 : Nat := 118140960795 + 1596141 * 2 ^ 59
def prefixEnd_1596141 : Nat := 4983230072969 + 3 ^ 40 * 1596141 * 2
def baseEnd_1596141 : Nat := 819587525348144824696987

theorem tailTrace_1596141 : CollatzResearch.WordTrace tailWord_1596141 prefixEnd_1596141 819587525348144824696987 := by
  unfold tailWord_1596141
  simp only [CollatzResearch.WordTrace]
  refine ⟨58216044910461231025180277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38810696606974154016786851 58216044910461231025180277)
  ·
    refine ⟨5457754210355740408610651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58216044910461231025180277 5457754210355740408610651)
    ·
      refine ⟨8186631315533610612915977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457754210355740408610651 8186631315533610612915977)
      ·
        refine ⟨6139973486650207959686983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8186631315533610612915977 6139973486650207959686983)
        ·
          refine ⟨9209960229975311939530475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139973486650207959686983 9209960229975311939530475)
          ·
            refine ⟨13814940344962967909295713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9209960229975311939530475 13814940344962967909295713)
            ·
              refine ⟨10361205258722225931971785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814940344962967909295713 10361205258722225931971785)
              ·
                refine ⟨7770903944041669448978839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10361205258722225931971785 7770903944041669448978839)
                ·
                  refine ⟨11656355916062504173468259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770903944041669448978839 11656355916062504173468259)
                  ·
                    refine ⟨17484533874093756260202389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11656355916062504173468259 17484533874093756260202389)
                    ·
                      refine ⟨819587525348144824696987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17484533874093756260202389 819587525348144824696987)
                      ·
                        rfl

theorem cell23_1596141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1596141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596141 prefixEnd_1596141 := by exact prefixLift 1596141
  have htrace : WordTrace (prefixWord ++ tailWord_1596141) baseStart_1596141 baseEnd_1596141 := by
    simpa [prefixWord, tailWord_1596141, baseEnd_1596141] using wordTrace_append hprefix tailTrace_1596141
  have hstable : (prefixWord ++ tailWord_1596141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596141).length < 2 ^ (prefixWord ++ tailWord_1596141).sum := by decide
  have hdescent : baseEnd_1596141 < baseStart_1596141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596145 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_1596145 : Nat := 118140960795 + 1596145 * 2 ^ 59
def prefixEnd_1596145 : Nat := 4983230072969 + 3 ^ 40 * 1596145 * 2
def baseEnd_1596145 : Nat := 819589579270762809046969

theorem tailTrace_1596145 : CollatzResearch.WordTrace tailWord_1596145 prefixEnd_1596145 819589579270762809046969 := by
  unfold tailWord_1596145
  simp only [CollatzResearch.WordTrace]
  refine ⟨58216190802446739708325889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38810793868297826472217259 58216190802446739708325889)
  ·
    refine ⟨43662143101835054781244417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58216190802446739708325889 43662143101835054781244417)
    ·
      refine ⟨32746607326376291085933313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43662143101835054781244417 32746607326376291085933313)
      ·
        refine ⟨24559955494782218314449985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32746607326376291085933313 24559955494782218314449985)
        ·
          refine ⟨18419966621086663735837489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24559955494782218314449985 18419966621086663735837489)
          ·
            refine ⟨13814974965814997801878117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18419966621086663735837489 13814974965814997801878117)
            ·
              refine ⟨2590307806090312087852147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13814974965814997801878117 2590307806090312087852147)
              ·
                refine ⟨3885461709135468131778221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590307806090312087852147 3885461709135468131778221)
                ·
                  refine ⟨1457048140925800549416833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3885461709135468131778221 1457048140925800549416833)
                  ·
                    refine ⟨1092786105694350412062625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457048140925800549416833 1092786105694350412062625)
                    ·
                      refine ⟨819589579270762809046969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092786105694350412062625 819589579270762809046969)
                      ·
                        rfl

theorem cell23_1596145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_1596145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596145 prefixEnd_1596145 := by exact prefixLift 1596145
  have htrace : WordTrace (prefixWord ++ tailWord_1596145) baseStart_1596145 baseEnd_1596145 := by
    simpa [prefixWord, tailWord_1596145, baseEnd_1596145] using wordTrace_append hprefix tailTrace_1596145
  have hstable : (prefixWord ++ tailWord_1596145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596145).length < 2 ^ (prefixWord ++ tailWord_1596145).sum := by decide
  have hdescent : baseEnd_1596145 < baseStart_1596145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596158 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1596158 : Nat := 118140960795 + 1596158 * 2 ^ 59
def prefixEnd_1596158 : Nat := 4983230072969 + 3 ^ 40 * 1596158 * 2
def baseEnd_1596158 : Nat := 819596254519271258184409

theorem tailTrace_1596158 : CollatzResearch.WordTrace tailWord_1596158 prefixEnd_1596158 819596254519271258184409 := by
  unfold tailWord_1596158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277083118924955366068641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38811109967599761952366085 7277083118924955366068641)
  ·
    refine ⟨5457812339193716524551481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7277083118924955366068641 5457812339193716524551481)
    ·
      refine ⟨4093359254395287393413611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5457812339193716524551481 4093359254395287393413611)
      ·
        refine ⟨6140038881592931090120417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093359254395287393413611 6140038881592931090120417)
        ·
          refine ⟨4605029161194698317590313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6140038881592931090120417 4605029161194698317590313)
          ·
            refine ⟨3453771870896023738192735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4605029161194698317590313 3453771870896023738192735)
            ·
              refine ⟨5180657806344035607289103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453771870896023738192735 5180657806344035607289103)
              ·
                refine ⟨7770986709516053410933655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180657806344035607289103 7770986709516053410933655)
                ·
                  refine ⟨11656480064274080116400483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770986709516053410933655 11656480064274080116400483)
                  ·
                    refine ⟨17484720096411120174600725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11656480064274080116400483 17484720096411120174600725)
                    ·
                      refine ⟨819596254519271258184409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17484720096411120174600725 819596254519271258184409)
                      ·
                        rfl

theorem cell23_1596158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1596158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596158 prefixEnd_1596158 := by exact prefixLift 1596158
  have htrace : WordTrace (prefixWord ++ tailWord_1596158) baseStart_1596158 baseEnd_1596158 := by
    simpa [prefixWord, tailWord_1596158, baseEnd_1596158] using wordTrace_append hprefix tailTrace_1596158
  have hstable : (prefixWord ++ tailWord_1596158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596158).length < 2 ^ (prefixWord ++ tailWord_1596158).sum := by decide
  have hdescent : baseEnd_1596158 < baseStart_1596158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596162 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_1596162 : Nat := 118140960795 + 1596162 * 2 ^ 59
def prefixEnd_1596162 : Nat := 4983230072969 + 3 ^ 40 * 1596162 * 2
def baseEnd_1596162 : Nat := 819598308441889242534391

theorem tailTrace_1596162 : CollatzResearch.WordTrace tailWord_1596162 prefixEnd_1596162 819598308441889242534391 := by
  unfold tailWord_1596162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554202710846287902923685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38811207228923434407796493 14554202710846287902923685)
  ·
    refine ⟨2728913008283678981798191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14554202710846287902923685 2728913008283678981798191)
    ·
      refine ⟨4093369512425518472697287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728913008283678981798191 4093369512425518472697287)
      ·
        refine ⟨6140054268638277709045931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4093369512425518472697287 6140054268638277709045931)
        ·
          refine ⟨9210081402957416563568897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6140054268638277709045931 9210081402957416563568897)
          ·
            refine ⟨6907561052218062422676673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9210081402957416563568897 6907561052218062422676673)
            ·
              refine ⟨5180670789163546817007505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6907561052218062422676673 5180670789163546817007505)
              ·
                refine ⟨3885503091872660112755629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180670789163546817007505 3885503091872660112755629)
                ·
                  refine ⟨1457063659452247542283361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3885503091872660112755629 1457063659452247542283361)
                  ·
                    refine ⟨1092797744589185656712521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457063659452247542283361 1092797744589185656712521)
                    ·
                      refine ⟨819598308441889242534391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092797744589185656712521 819598308441889242534391)
                      ·
                        rfl

theorem cell23_1596162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_1596162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596162 prefixEnd_1596162 := by exact prefixLift 1596162
  have htrace : WordTrace (prefixWord ++ tailWord_1596162) baseStart_1596162 baseEnd_1596162 := by
    simpa [prefixWord, tailWord_1596162, baseEnd_1596162] using wordTrace_append hprefix tailTrace_1596162
  have hstable : (prefixWord ++ tailWord_1596162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596162).length < 2 ^ (prefixWord ++ tailWord_1596162).sum := by decide
  have hdescent : baseEnd_1596162 < baseStart_1596162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596168 : List Nat := [2, 1, 3, 2, 2, 4, 2, 7]
def baseStart_1596168 : Nat := 118140960795 + 1596168 * 2 ^ 59
def prefixEnd_1596168 : Nat := 4983230072969 + 3 ^ 40 * 1596168 * 2
def baseEnd_1596168 : Nat := 30355607012067267372569

theorem tailTrace_1596168 : CollatzResearch.WordTrace tailWord_1596168 prefixEnd_1596168 30355607012067267372569 := by
  unfold tailWord_1596168
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108514840681707318206579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38811353120908943090942105 29108514840681707318206579)
  ·
    refine ⟨43662772261022560977309869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29108514840681707318206579 43662772261022560977309869)
    ·
      refine ⟨16373539597883460366491201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43662772261022560977309869 16373539597883460366491201)
      ·
        refine ⟨12280154698412595274868401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16373539597883460366491201 12280154698412595274868401)
        ·
          refine ⟨9210116023809446456151301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12280154698412595274868401 9210116023809446456151301)
          ·
            refine ⟨1726896754464271210528369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9210116023809446456151301 1726896754464271210528369)
            ·
              refine ⟨1295172565848203407896277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726896754464271210528369 1295172565848203407896277)
              ·
                refine ⟨30355607012067267372569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1295172565848203407896277 30355607012067267372569)
                ·
                  rfl

theorem cell23_1596168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 7].length) (baseStart_1596168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596168 prefixEnd_1596168 := by exact prefixLift 1596168
  have htrace : WordTrace (prefixWord ++ tailWord_1596168) baseStart_1596168 baseEnd_1596168 := by
    simpa [prefixWord, tailWord_1596168, baseEnd_1596168] using wordTrace_append hprefix tailTrace_1596168
  have hstable : (prefixWord ++ tailWord_1596168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596168).length < 2 ^ (prefixWord ++ tailWord_1596168).sum := by decide
  have hdescent : baseEnd_1596168 < baseStart_1596168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596196 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_1596196 : Nat := 118140960795 + 1596196 * 2 ^ 59
def prefixEnd_1596196 : Nat := 4983230072969 + 3 ^ 40 * 1596196 * 2
def baseEnd_1596196 : Nat := 819615766784142109509235

theorem tailTrace_1596196 : CollatzResearch.WordTrace tailWord_1596196 prefixEnd_1596196 819615766784142109509235 := by
  unfold tailWord_1596196
  simp only [CollatzResearch.WordTrace]
  refine ⟨29109025462630987709216221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38812033950174650278954961 29109025462630987709216221)
  ·
    refine ⟨10915884548486620390956083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29109025462630987709216221 10915884548486620390956083)
    ·
      refine ⟨16373826822729930586434125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10915884548486620390956083 16373826822729930586434125)
      ·
        refine ⟨6140185058523723969912797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16373826822729930586434125 6140185058523723969912797)
        ·
          refine ⟨2302569396946396488717299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6140185058523723969912797 2302569396946396488717299)
          ·
            refine ⟨3453854095419594733075949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302569396946396488717299 3453854095419594733075949)
            ·
              refine ⟨1295195285782348024903481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3453854095419594733075949 1295195285782348024903481)
              ·
                refine ⟨971396464336761018677611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295195285782348024903481 971396464336761018677611)
                ·
                  refine ⟨1457094696505141528016417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971396464336761018677611 1457094696505141528016417)
                  ·
                    refine ⟨1092821022378856146012313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457094696505141528016417 1092821022378856146012313)
                    ·
                      refine ⟨819615766784142109509235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092821022378856146012313 819615766784142109509235)
                      ·
                        rfl

theorem cell23_1596196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_1596196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596196 prefixEnd_1596196 := by exact prefixLift 1596196
  have htrace : WordTrace (prefixWord ++ tailWord_1596196) baseStart_1596196 baseEnd_1596196 := by
    simpa [prefixWord, tailWord_1596196, baseEnd_1596196] using wordTrace_append hprefix tailTrace_1596196
  have hstable : (prefixWord ++ tailWord_1596196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596196).length < 2 ^ (prefixWord ++ tailWord_1596196).sum := by decide
  have hdescent : baseEnd_1596196 < baseStart_1596196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596222 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_1596222 : Nat := 118140960795 + 1596222 * 2 ^ 59
def prefixEnd_1596222 : Nat := 4983230072969 + 3 ^ 40 * 1596222 * 2
def baseEnd_1596222 : Nat := 819629117281159007784115

theorem tailTrace_1596222 : CollatzResearch.WordTrace tailWord_1596222 prefixEnd_1596222 819629117281159007784115 := by
  unfold tailWord_1596222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277374902895972732359865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38812666148778521239252613 7277374902895972732359865)
  ·
    refine ⟨5458031177171979549269899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7277374902895972732359865 5458031177171979549269899)
    ·
      refine ⟨8187046765757969323904849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5458031177171979549269899 8187046765757969323904849)
      ·
        refine ⟨6140285074318476992928637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8187046765757969323904849 6140285074318476992928637)
        ·
          refine ⟨2302606902869428872348239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6140285074318476992928637 2302606902869428872348239)
          ·
            refine ⟨3453910354304143308522359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302606902869428872348239 3453910354304143308522359)
            ·
              refine ⟨5180865531456214962783539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453910354304143308522359 5180865531456214962783539)
              ·
                refine ⟨7771298297184322444175309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180865531456214962783539 7771298297184322444175309)
                ·
                  refine ⟨2914236861444120916565741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7771298297184322444175309 2914236861444120916565741)
                  ·
                    refine ⟨1092838823041545343712153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914236861444120916565741 1092838823041545343712153)
                    ·
                      refine ⟨819629117281159007784115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092838823041545343712153 819629117281159007784115)
                      ·
                        rfl

theorem cell23_1596222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_1596222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596222 prefixEnd_1596222 := by exact prefixLift 1596222
  have htrace : WordTrace (prefixWord ++ tailWord_1596222) baseStart_1596222 baseEnd_1596222 := by
    simpa [prefixWord, tailWord_1596222, baseEnd_1596222] using wordTrace_append hprefix tailTrace_1596222
  have hstable : (prefixWord ++ tailWord_1596222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596222).length < 2 ^ (prefixWord ++ tailWord_1596222).sum := by decide
  have hdescent : baseEnd_1596222 < baseStart_1596222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596231 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1596231 : Nat := 118140960795 + 1596231 * 2 ^ 59
def prefixEnd_1596231 : Nat := 4983230072969 + 3 ^ 40 * 1596231 * 2
def baseEnd_1596231 : Nat := 819633738607049472571573

theorem tailTrace_1596231 : CollatzResearch.WordTrace tailWord_1596231 prefixEnd_1596231 819633738607049472571573 := by
  unfold tailWord_1596231
  simp only [CollatzResearch.WordTrace]
  refine ⟨58219327480135176395956547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38812884986756784263971031 58219327480135176395956547)
  ·
    refine ⟨87328991220202764593934821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58219327480135176395956547 87328991220202764593934821)
    ·
      refine ⟨16374185853788018361362779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87328991220202764593934821 16374185853788018361362779)
      ·
        refine ⟨24561278780682027542044169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16374185853788018361362779 24561278780682027542044169)
        ·
          refine ⟨18420959085511520656533127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24561278780682027542044169 18420959085511520656533127)
          ·
            refine ⟨27631438628267280984799691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420959085511520656533127 27631438628267280984799691)
            ·
              refine ⟨41447157942400921477199537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27631438628267280984799691 41447157942400921477199537)
              ·
                refine ⟨31085368456800691107899653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41447157942400921477199537 31085368456800691107899653)
                ·
                  refine ⟨5828506585650129582731185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31085368456800691107899653 5828506585650129582731185)
                  ·
                    refine ⟨4371379939237597187048389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828506585650129582731185 4371379939237597187048389)
                    ·
                      refine ⟨819633738607049472571573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4371379939237597187048389 819633738607049472571573)
                      ·
                        rfl

theorem cell23_1596231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1596231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596231 prefixEnd_1596231 := by exact prefixLift 1596231
  have htrace : WordTrace (prefixWord ++ tailWord_1596231) baseStart_1596231 baseEnd_1596231 := by
    simpa [prefixWord, tailWord_1596231, baseEnd_1596231] using wordTrace_append hprefix tailTrace_1596231
  have hstable : (prefixWord ++ tailWord_1596231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596231).length < 2 ^ (prefixWord ++ tailWord_1596231).sum := by decide
  have hdescent : baseEnd_1596231 < baseStart_1596231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596268 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_1596268 : Nat := 118140960795 + 1596268 * 2 ^ 59
def prefixEnd_1596268 : Nat := 4983230072969 + 3 ^ 40 * 1596268 * 2
def baseEnd_1596268 : Nat := 819652737391265827808903

theorem tailTrace_1596268 : CollatzResearch.WordTrace tailWord_1596268 prefixEnd_1596268 819652737391265827808903 := by
  unfold tailWord_1596268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29110338490500565857526729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38813784654000754476702305 29110338490500565857526729)
  ·
    refine ⟨21832753867875424393145047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29110338490500565857526729 21832753867875424393145047)
    ·
      refine ⟨32749130801813136589717571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21832753867875424393145047 32749130801813136589717571)
      ·
        refine ⟨49123696202719704884576357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32749130801813136589717571 49123696202719704884576357)
        ·
          refine ⟨9210693038009944665858067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49123696202719704884576357 9210693038009944665858067)
          ·
            refine ⟨13816039557014916998787101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9210693038009944665858067 13816039557014916998787101)
            ·
              refine ⟨5181014833880593874545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13816039557014916998787101 5181014833880593874545163)
              ·
                refine ⟨7771522250820890811817745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181014833880593874545163 7771522250820890811817745)
                ·
                  refine ⟨5828641688115668108863309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7771522250820890811817745 5828641688115668108863309)
                  ·
                    refine ⟨2185740633043375540823741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5828641688115668108863309 2185740633043375540823741)
                    ·
                      refine ⟨819652737391265827808903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185740633043375540823741 819652737391265827808903)
                      ·
                        rfl

theorem cell23_1596268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_1596268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596268 prefixEnd_1596268 := by exact prefixLift 1596268
  have htrace : WordTrace (prefixWord ++ tailWord_1596268) baseStart_1596268 baseEnd_1596268 := by
    simpa [prefixWord, tailWord_1596268, baseEnd_1596268] using wordTrace_append hprefix tailTrace_1596268
  have hstable : (prefixWord ++ tailWord_1596268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596268).length < 2 ^ (prefixWord ++ tailWord_1596268).sum := by decide
  have hdescent : baseEnd_1596268 < baseStart_1596268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596271 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 4, 5]
def baseStart_1596271 : Nat := 118140960795 + 1596271 * 2 ^ 59
def prefixEnd_1596271 : Nat := 4983230072969 + 3 ^ 40 * 1596271 * 2
def baseEnd_1596271 : Nat := 273218092611076438690463

theorem tailTrace_1596271 : CollatzResearch.WordTrace tailWord_1596271 prefixEnd_1596271 273218092611076438690463 := by
  unfold tailWord_1596271
  simp only [CollatzResearch.WordTrace]
  refine ⟨58220786399990263227412667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38813857599993508818275111 58220786399990263227412667)
  ·
    refine ⟨87331179599985394841119001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58220786399990263227412667 87331179599985394841119001)
    ·
      refine ⟨65498384699989046130839251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87331179599985394841119001 65498384699989046130839251)
      ·
        refine ⟨98247577049983569196258877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65498384699989046130839251 98247577049983569196258877)
        ·
          refine ⟨36842841393743838448597079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98247577049983569196258877 36842841393743838448597079)
          ·
            refine ⟨55264262090615757672895619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36842841393743838448597079 55264262090615757672895619)
            ·
              refine ⟨82896393135923636509343429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55264262090615757672895619 82896393135923636509343429)
              ·
                refine ⟨15543073712985681845501893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82896393135923636509343429 15543073712985681845501893)
                ·
                  refine ⟨2914326321184815346031605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15543073712985681845501893 2914326321184815346031605)
                  ·
                    refine ⟨273218092611076438690463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2914326321184815346031605 273218092611076438690463)
                    ·
                      rfl

theorem cell23_1596271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_1596271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596271 prefixEnd_1596271 := by exact prefixLift 1596271
  have htrace : WordTrace (prefixWord ++ tailWord_1596271) baseStart_1596271 baseEnd_1596271 := by
    simpa [prefixWord, tailWord_1596271, baseEnd_1596271] using wordTrace_append hprefix tailTrace_1596271
  have hstable : (prefixWord ++ tailWord_1596271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596271).length < 2 ^ (prefixWord ++ tailWord_1596271).sum := by decide
  have hdescent : baseEnd_1596271 < baseStart_1596271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596290 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1596290 : Nat := 118140960795 + 1596290 * 2 ^ 59
def prefixEnd_1596290 : Nat := 4983230072969 + 3 ^ 40 * 1596290 * 2
def baseEnd_1596290 : Nat := 819664033965664741733803

theorem tailTrace_1596290 : CollatzResearch.WordTrace tailWord_1596290 prefixEnd_1596290 819664033965664741733803 := by
  unfold tailWord_1596290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555369846730357368088581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38814319591280952981569549 14555369846730357368088581)
  ·
    refine ⟨2729131846261942006516609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14555369846730357368088581 2729131846261942006516609)
    ·
      refine ⟨2046848884696456504887457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2729131846261942006516609 2046848884696456504887457)
      ·
        refine ⟨1535136663522342378665593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2046848884696456504887457 1535136663522342378665593)
        ·
          refine ⟨1151352497641756783999195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535136663522342378665593 1151352497641756783999195)
          ·
            refine ⟨1727028746462635175998793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151352497641756783999195 1727028746462635175998793)
            ·
              refine ⟨1295271559846976381999095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1727028746462635175998793 1295271559846976381999095)
              ·
                refine ⟨1942907339770464572998643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295271559846976381999095 1942907339770464572998643)
                ·
                  refine ⟨2914361009655696859497965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942907339770464572998643 2914361009655696859497965)
                  ·
                    refine ⟨1092885378620886322311737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914361009655696859497965 1092885378620886322311737)
                    ·
                      refine ⟨819664033965664741733803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092885378620886322311737 819664033965664741733803)
                      ·
                        rfl

theorem cell23_1596290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1596290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596290 prefixEnd_1596290 := by exact prefixLift 1596290
  have htrace : WordTrace (prefixWord ++ tailWord_1596290) baseStart_1596290 baseEnd_1596290 := by
    simpa [prefixWord, tailWord_1596290, baseEnd_1596290] using wordTrace_append hprefix tailTrace_1596290
  have hstable : (prefixWord ++ tailWord_1596290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596290).length < 2 ^ (prefixWord ++ tailWord_1596290).sum := by decide
  have hdescent : baseEnd_1596290 < baseStart_1596290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596351 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1596351 : Nat := 118140960795 + 1596351 * 2 ^ 59
def prefixEnd_1596351 : Nat := 4983230072969 + 3 ^ 40 * 1596351 * 2
def baseEnd_1596351 : Nat := 819695356285589003071021

theorem tailTrace_1596351 : CollatzResearch.WordTrace tailWord_1596351 prefixEnd_1596351 819695356285589003071021 := by
  unfold tailWord_1596351
  simp only [CollatzResearch.WordTrace]
  refine ⟨58223704239700436890324907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38815802826466957926883271 58223704239700436890324907)
  ·
    refine ⟨87335556359550655335487361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58223704239700436890324907 87335556359550655335487361)
    ·
      refine ⟨65501667269662991501615521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87335556359550655335487361 65501667269662991501615521)
      ·
        refine ⟨49126250452247243626211641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65501667269662991501615521 49126250452247243626211641)
        ·
          refine ⟨36844687839185432719658731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49126250452247243626211641 36844687839185432719658731)
          ·
            refine ⟨55267031758778149079488097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36844687839185432719658731 55267031758778149079488097)
            ·
              refine ⟨41450273819083611809616073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55267031758778149079488097 41450273819083611809616073)
              ·
                refine ⟨31087705364312708857212055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41450273819083611809616073 31087705364312708857212055)
                ·
                  refine ⟨46631558046469063285818083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31087705364312708857212055 46631558046469063285818083)
                  ·
                    refine ⟨69947337069703594928727125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46631558046469063285818083 69947337069703594928727125)
                    ·
                      refine ⟨819695356285589003071021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 69947337069703594928727125 819695356285589003071021)
                      ·
                        rfl

theorem cell23_1596351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1596351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596351 prefixEnd_1596351 := by exact prefixLift 1596351
  have htrace : WordTrace (prefixWord ++ tailWord_1596351) baseStart_1596351 baseEnd_1596351 := by
    simpa [prefixWord, tailWord_1596351, baseEnd_1596351] using wordTrace_append hprefix tailTrace_1596351
  have hstable : (prefixWord ++ tailWord_1596351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596351).length < 2 ^ (prefixWord ++ tailWord_1596351).sum := by decide
  have hdescent : baseEnd_1596351 < baseStart_1596351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596352 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 1, 4]
def baseStart_1596352 : Nat := 118140960795 + 1596352 * 2 ^ 59
def prefixEnd_1596352 : Nat := 4983230072969 + 3 ^ 40 * 1596352 * 2
def baseEnd_1596352 : Nat := 273231956588747833052839

theorem tailTrace_1596352 : CollatzResearch.WordTrace tailWord_1596352 prefixEnd_1596352 273231956588747833052839 := by
  unfold tailWord_1596352
  simp only [CollatzResearch.WordTrace]
  refine ⟨29111870356348407030555655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38815827141797876040740873 29111870356348407030555655)
  ·
    refine ⟨43667805534522610545833483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29111870356348407030555655 43667805534522610545833483)
    ·
      refine ⟨65501708301783915818750225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43667805534522610545833483 65501708301783915818750225)
      ·
        refine ⟨49126281226337936864062669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65501708301783915818750225 49126281226337936864062669)
        ·
          refine ⟨18422355459876726324023501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49126281226337936864062669 18422355459876726324023501)
          ·
            refine ⟨6908383297453772371508813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18422355459876726324023501 6908383297453772371508813)
            ·
              refine ⟨2590643736545164639315805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6908383297453772371508813 2590643736545164639315805)
              ·
                refine ⟨971491401204436739743427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2590643736545164639315805 971491401204436739743427)
                ·
                  refine ⟨1457237101806655109615141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971491401204436739743427 1457237101806655109615141)
                  ·
                    refine ⟨273231956588747833052839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1457237101806655109615141 273231956588747833052839)
                    ·
                      rfl

theorem cell23_1596352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 4].length) (baseStart_1596352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596352 prefixEnd_1596352 := by exact prefixLift 1596352
  have htrace : WordTrace (prefixWord ++ tailWord_1596352) baseStart_1596352 baseEnd_1596352 := by
    simpa [prefixWord, tailWord_1596352, baseEnd_1596352] using wordTrace_append hprefix tailTrace_1596352
  have hstable : (prefixWord ++ tailWord_1596352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596352).length < 2 ^ (prefixWord ++ tailWord_1596352).sum := by decide
  have hdescent : baseEnd_1596352 < baseStart_1596352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596375 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1596375 : Nat := 118140960795 + 1596375 * 2 ^ 59
def prefixEnd_1596375 : Nat := 4983230072969 + 3 ^ 40 * 1596375 * 2
def baseEnd_1596375 : Nat := 819707679821296909170911

theorem tailTrace_1596375 : CollatzResearch.WordTrace tailWord_1596375 prefixEnd_1596375 819707679821296909170911 := by
  unfold tailWord_1596375
  simp only [CollatzResearch.WordTrace]
  refine ⟨58224579591613488989198579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38816386394408992659465719 58224579591613488989198579)
  ·
    refine ⟨87336869387420233483797869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58224579591613488989198579 87336869387420233483797869)
    ·
      refine ⟨32751326020282587556424201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87336869387420233483797869 32751326020282587556424201)
      ·
        refine ⟨24563494515211940667318151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32751326020282587556424201 24563494515211940667318151)
        ·
          refine ⟨36845241772817911000977227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24563494515211940667318151 36845241772817911000977227)
          ·
            refine ⟨55267862659226866501465841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36845241772817911000977227 55267862659226866501465841)
            ·
              refine ⟨41450896994420149876099381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55267862659226866501465841 41450896994420149876099381)
              ·
                refine ⟨3886021593226889050884317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41450896994420149876099381 3886021593226889050884317)
                ·
                  refine ⟨1457258097460083394081619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3886021593226889050884317 1457258097460083394081619)
                  ·
                    refine ⟨2185887146190125091122429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457258097460083394081619 2185887146190125091122429)
                    ·
                      refine ⟨819707679821296909170911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185887146190125091122429 819707679821296909170911)
                      ·
                        rfl

theorem cell23_1596375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1596375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596375 prefixEnd_1596375 := by exact prefixLift 1596375
  have htrace : WordTrace (prefixWord ++ tailWord_1596375) baseStart_1596375 baseEnd_1596375 := by
    simpa [prefixWord, tailWord_1596375, baseEnd_1596375] using wordTrace_append hprefix tailTrace_1596375
  have hstable : (prefixWord ++ tailWord_1596375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596375).length < 2 ^ (prefixWord ++ tailWord_1596375).sum := by decide
  have hdescent : baseEnd_1596375 < baseStart_1596375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596385 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_1596385 : Nat := 118140960795 + 1596385 * 2 ^ 59
def prefixEnd_1596385 : Nat := 4983230072969 + 3 ^ 40 * 1596385 * 2
def baseEnd_1596385 : Nat := 819712814627841870045865

theorem tailTrace_1596385 : CollatzResearch.WordTrace tailWord_1596385 prefixEnd_1596385 819712814627841870045865 := by
  unfold tailWord_1596385
  simp only [CollatzResearch.WordTrace]
  refine ⟨58224944321577260697062609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38816629547718173798041739 58224944321577260697062609)
  ·
    refine ⟨43668708241182945522796957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58224944321577260697062609 43668708241182945522796957)
    ·
      refine ⟨16375765590443604571048859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43668708241182945522796957 16375765590443604571048859)
      ·
        refine ⟨24563648385665406856573289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16375765590443604571048859 24563648385665406856573289)
        ·
          refine ⟨18422736289249055142429967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24563648385665406856573289 18422736289249055142429967)
          ·
            refine ⟨27634104433873582713644951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18422736289249055142429967 27634104433873582713644951)
            ·
              refine ⟨41451156650810374070467427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27634104433873582713644951 41451156650810374070467427)
              ·
                refine ⟨62176734976215561105701141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41451156650810374070467427 62176734976215561105701141)
                ·
                  refine ⟨2914534452010104426829741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62176734976215561105701141 2914534452010104426829741)
                  ·
                    refine ⟨1092950419503789160061153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2914534452010104426829741 1092950419503789160061153)
                    ·
                      refine ⟨819712814627841870045865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092950419503789160061153 819712814627841870045865)
                      ·
                        rfl

theorem cell23_1596385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_1596385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596385 prefixEnd_1596385 := by exact prefixLift 1596385
  have htrace : WordTrace (prefixWord ++ tailWord_1596385) baseStart_1596385 baseEnd_1596385 := by
    simpa [prefixWord, tailWord_1596385, baseEnd_1596385] using wordTrace_append hprefix tailTrace_1596385
  have hstable : (prefixWord ++ tailWord_1596385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596385).length < 2 ^ (prefixWord ++ tailWord_1596385).sum := by decide
  have hdescent : baseEnd_1596385 < baseStart_1596385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596412 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_1596412 : Nat := 118140960795 + 1596412 * 2 ^ 59
def prefixEnd_1596412 : Nat := 4983230072969 + 3 ^ 40 * 1596412 * 2
def baseEnd_1596412 : Nat := 273242226201837754802747

theorem tailTrace_1596412 : CollatzResearch.WordTrace tailWord_1596412 prefixEnd_1596412 273242226201837754802747 := by
  unfold tailWord_1596412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29112964546239722154147745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38817286061652962872196993 29112964546239722154147745)
  ·
    refine ⟨21834723409679791615610809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29112964546239722154147745 21834723409679791615610809)
    ·
      refine ⟨16376042557259843711708107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21834723409679791615610809 16376042557259843711708107)
      ·
        refine ⟨24564063835889765567562161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376042557259843711708107 24564063835889765567562161)
        ·
          refine ⟨18423047876917324175671621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24564063835889765567562161 18423047876917324175671621)
          ·
            refine ⟨3454321476921998282938429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18423047876917324175671621 3454321476921998282938429)
            ·
              refine ⟨1295370553845749356101911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3454321476921998282938429 1295370553845749356101911)
              ·
                refine ⟨1943055830768624034152867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295370553845749356101911 1943055830768624034152867)
                ·
                  refine ⟨2914583746152936051229301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943055830768624034152867 2914583746152936051229301)
                  ·
                    refine ⟨273242226201837754802747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2914583746152936051229301 273242226201837754802747)
                    ·
                      rfl

theorem cell23_1596412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_1596412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596412 prefixEnd_1596412 := by exact prefixLift 1596412
  have htrace : WordTrace (prefixWord ++ tailWord_1596412) baseStart_1596412 baseEnd_1596412 := by
    simpa [prefixWord, tailWord_1596412, baseEnd_1596412] using wordTrace_append hprefix tailTrace_1596412
  have hstable : (prefixWord ++ tailWord_1596412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596412).length < 2 ^ (prefixWord ++ tailWord_1596412).sum := by decide
  have hdescent : baseEnd_1596412 < baseStart_1596412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596426 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_1596426 : Nat := 118140960795 + 1596426 * 2 ^ 59
def prefixEnd_1596426 : Nat := 4983230072969 + 3 ^ 40 * 1596426 * 2
def baseEnd_1596426 : Nat := 819733867334676209633177

theorem tailTrace_1596426 : CollatzResearch.WordTrace tailWord_1596426 prefixEnd_1596426 819733867334676209633177 := by
  unfold tailWord_1596426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14556609928607181174826283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38817626476285816466203421 14556609928607181174826283)
  ·
    refine ⟨21834914892910771762239425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14556609928607181174826283 21834914892910771762239425)
    ·
      refine ⟨16376186169683078821679569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21834914892910771762239425 16376186169683078821679569)
      ·
        refine ⟨12282139627262309116259677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16376186169683078821679569 12282139627262309116259677)
        ·
          refine ⟨4605802360223365918597379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12282139627262309116259677 4605802360223365918597379)
          ·
            refine ⟨6908703540335048877896069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605802360223365918597379 6908703540335048877896069)
            ·
              refine ⟨1295381913812821664605513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6908703540335048877896069 1295381913812821664605513)
              ·
                refine ⟨971536435359616248454135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295381913812821664605513 971536435359616248454135)
                ·
                  refine ⟨1457304653039424372681203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971536435359616248454135 1457304653039424372681203)
                  ·
                    refine ⟨2185956979559136559021805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457304653039424372681203 2185956979559136559021805)
                    ·
                      refine ⟨819733867334676209633177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185956979559136559021805 819733867334676209633177)
                      ·
                        rfl

theorem cell23_1596426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_1596426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596426 prefixEnd_1596426 := by exact prefixLift 1596426
  have htrace : WordTrace (prefixWord ++ tailWord_1596426) baseStart_1596426 baseEnd_1596426 := by
    simpa [prefixWord, tailWord_1596426, baseEnd_1596426] using wordTrace_append hprefix tailTrace_1596426
  have hstable : (prefixWord ++ tailWord_1596426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596426).length < 2 ^ (prefixWord ++ tailWord_1596426).sum := by decide
  have hdescent : baseEnd_1596426 < baseStart_1596426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596449 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1596449 : Nat := 118140960795 + 1596449 * 2 ^ 59
def prefixEnd_1596449 : Nat := 4983230072969 + 3 ^ 40 * 1596449 * 2
def baseEnd_1596449 : Nat := 819745677389729619645571

theorem tailTrace_1596449 : CollatzResearch.WordTrace tailWord_1596449 prefixEnd_1596449 819745677389729619645571 := by
  unfold tailWord_1596449
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227278593345399627392401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38818185728896933084928267 58227278593345399627392401)
  ·
    refine ⟨43670458945009049720544301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58227278593345399627392401 43670458945009049720544301)
    ·
      refine ⟨16376422104378393645204113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43670458945009049720544301 16376422104378393645204113)
      ·
        refine ⟨12282316578283795233903085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16376422104378393645204113 12282316578283795233903085)
        ·
          refine ⟨4605868716856423212713657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12282316578283795233903085 4605868716856423212713657)
          ·
            refine ⟨3454401537642317409535243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4605868716856423212713657 3454401537642317409535243)
            ·
              refine ⟨5181602306463476114302865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454401537642317409535243 5181602306463476114302865)
              ·
                refine ⟨3886201729847607085727149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181602306463476114302865 3886201729847607085727149)
                ·
                  refine ⟨1457325648692852657147681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3886201729847607085727149 1457325648692852657147681)
                  ·
                    refine ⟨1092994236519639492860761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457325648692852657147681 1092994236519639492860761)
                    ·
                      refine ⟨819745677389729619645571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1092994236519639492860761 819745677389729619645571)
                      ·
                        rfl

theorem cell23_1596449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1596449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596449 prefixEnd_1596449 := by exact prefixLift 1596449
  have htrace : WordTrace (prefixWord ++ tailWord_1596449) baseStart_1596449 baseEnd_1596449 := by
    simpa [prefixWord, tailWord_1596449, baseEnd_1596449] using wordTrace_append hprefix tailTrace_1596449
  have hstable : (prefixWord ++ tailWord_1596449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596449).length < 2 ^ (prefixWord ++ tailWord_1596449).sum := by decide
  have hdescent : baseEnd_1596449 < baseStart_1596449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596452 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1596452 : Nat := 118140960795 + 1596452 * 2 ^ 59
def prefixEnd_1596452 : Nat := 4983230072969 + 3 ^ 40 * 1596452 * 2
def baseEnd_1596452 : Nat := 819747217831693107908057

theorem tailTrace_1596452 : CollatzResearch.WordTrace tailWord_1596452 prefixEnd_1596452 819747217831693107908057 := by
  unfold tailWord_1596452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113694006167265569875805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38818258674889687426501073 29113694006167265569875805)
  ·
    refine ⟨10917635252312724588703427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29113694006167265569875805 10917635252312724588703427)
    ·
      refine ⟨16376452878469086883055141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10917635252312724588703427 16376452878469086883055141)
      ·
        refine ⟨3070584914712953790572839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16376452878469086883055141 3070584914712953790572839)
        ·
          refine ⟨4605877372069430685859259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070584914712953790572839 4605877372069430685859259)
          ·
            refine ⟨6908816058104146028788889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605877372069430685859259 6908816058104146028788889)
            ·
              refine ⟨5181612043578109521591667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908816058104146028788889 5181612043578109521591667)
              ·
                refine ⟨7772418065367164282387501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181612043578109521591667 7772418065367164282387501)
                ·
                  refine ⟨2914656774512686605895313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7772418065367164282387501 2914656774512686605895313)
                  ·
                    refine ⟨2185992580884514954421485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914656774512686605895313 2185992580884514954421485)
                    ·
                      refine ⟨819747217831693107908057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2185992580884514954421485 819747217831693107908057)
                      ·
                        rfl

theorem cell23_1596452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1596452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596452 prefixEnd_1596452 := by exact prefixLift 1596452
  have htrace : WordTrace (prefixWord ++ tailWord_1596452) baseStart_1596452 baseEnd_1596452 := by
    simpa [prefixWord, tailWord_1596452, baseEnd_1596452] using wordTrace_append hprefix tailTrace_1596452
  have hstable : (prefixWord ++ tailWord_1596452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596452).length < 2 ^ (prefixWord ++ tailWord_1596452).sum := by decide
  have hdescent : baseEnd_1596452 < baseStart_1596452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596465 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1596465 : Nat := 118140960795 + 1596465 * 2 ^ 59
def prefixEnd_1596465 : Nat := 4983230072969 + 3 ^ 40 * 1596465 * 2
def baseEnd_1596465 : Nat := 819753893080201557045497

theorem tailTrace_1596465 : CollatzResearch.WordTrace tailWord_1596465 prefixEnd_1596465 819753893080201557045497 := by
  unfold tailWord_1596465
  simp only [CollatzResearch.WordTrace]
  refine ⟨58227862161287434359974849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38818574774191622906649899 58227862161287434359974849)
  ·
    refine ⟨43670896620965575769981137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58227862161287434359974849 43670896620965575769981137)
    ·
      refine ⟨32753172465724181827485853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43670896620965575769981137 32753172465724181827485853)
      ·
        refine ⟨12282439674646568185307195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32753172465724181827485853 12282439674646568185307195)
        ·
          refine ⟨18423659511969852277960793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12282439674646568185307195 18423659511969852277960793)
          ·
            refine ⟨13817744633977389208470595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18423659511969852277960793 13817744633977389208470595)
            ·
              refine ⟨20726616950966083812705893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13817744633977389208470595 20726616950966083812705893)
              ·
                refine ⟨3886240678306140714882355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20726616950966083812705893 3886240678306140714882355)
                ·
                  refine ⟨5829361017459211072323533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3886240678306140714882355 5829361017459211072323533)
                  ·
                    refine ⟨2186010381547204152121325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5829361017459211072323533 2186010381547204152121325)
                    ·
                      refine ⟨819753893080201557045497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2186010381547204152121325 819753893080201557045497)
                      ·
                        rfl

theorem cell23_1596465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1596465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596465 prefixEnd_1596465 := by exact prefixLift 1596465
  have htrace : WordTrace (prefixWord ++ tailWord_1596465) baseStart_1596465 baseEnd_1596465 := by
    simpa [prefixWord, tailWord_1596465, baseEnd_1596465] using wordTrace_append hprefix tailTrace_1596465
  have hstable : (prefixWord ++ tailWord_1596465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596465).length < 2 ^ (prefixWord ++ tailWord_1596465).sum := by decide
  have hdescent : baseEnd_1596465 < baseStart_1596465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596466 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_1596466 : Nat := 118140960795 + 1596466 * 2 ^ 59
def prefixEnd_1596466 : Nat := 4983230072969 + 3 ^ 40 * 1596466 * 2
def baseEnd_1596466 : Nat := 819754406560856053132993

theorem tailTrace_1596466 : CollatzResearch.WordTrace tailWord_1596466 prefixEnd_1596466 819754406560856053132993 := by
  unfold tailWord_1596466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14556974658570952882690313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38818599089522541020507501 14556974658570952882690313)
  ·
    refine ⟨10917730993928214662017735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14556974658570952882690313 10917730993928214662017735)
    ·
      refine ⟨16376596490892321993026603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10917730993928214662017735 16376596490892321993026603)
      ·
        refine ⟨24564894736338482989539905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16376596490892321993026603 24564894736338482989539905)
        ·
          refine ⟨18423671052253862242154929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24564894736338482989539905 18423671052253862242154929)
          ·
            refine ⟨13817753289190396681616197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18423671052253862242154929 13817753289190396681616197)
            ·
              refine ⟨2590828741723199377803037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13817753289190396681616197 2590828741723199377803037)
              ·
                refine ⟨971560778146199766676139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2590828741723199377803037 971560778146199766676139)
                ·
                  refine ⟨1457341167219299650014209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971560778146199766676139 1457341167219299650014209)
                  ·
                    refine ⟨1093005875414474737510657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457341167219299650014209 1093005875414474737510657)
                    ·
                      refine ⟨819754406560856053132993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093005875414474737510657 819754406560856053132993)
                      ·
                        rfl

theorem cell23_1596466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_1596466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596466 prefixEnd_1596466 := by exact prefixLift 1596466
  have htrace : WordTrace (prefixWord ++ tailWord_1596466) baseStart_1596466 baseEnd_1596466 := by
    simpa [prefixWord, tailWord_1596466, baseEnd_1596466] using wordTrace_append hprefix tailTrace_1596466
  have hstable : (prefixWord ++ tailWord_1596466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596466).length < 2 ^ (prefixWord ++ tailWord_1596466).sum := by decide
  have hdescent : baseEnd_1596466 < baseStart_1596466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596525 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1596525 : Nat := 118140960795 + 1596525 * 2 ^ 59
def prefixEnd_1596525 : Nat := 4983230072969 + 3 ^ 40 * 1596525 * 2
def baseEnd_1596525 : Nat := 819784701919471322295221

theorem tailTrace_1596525 : CollatzResearch.WordTrace tailWord_1596525 prefixEnd_1596525 819784701919471322295221 := by
  unfold tailWord_1596525
  simp only [CollatzResearch.WordTrace]
  refine ⟨58230050541070064607159029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38820033694046709738106019 58230050541070064607159029)
  ·
    refine ⟨5459067238225318556921159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58230050541070064607159029 5459067238225318556921159)
    ·
      refine ⟨8188600857337977835381739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459067238225318556921159 8188600857337977835381739)
      ·
        refine ⟨12282901286006966753072609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8188600857337977835381739 12282901286006966753072609)
        ·
          refine ⟨9212175964505225064804457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12282901286006966753072609 9212175964505225064804457)
          ·
            refine ⟨6909131973378918798603343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9212175964505225064804457 6909131973378918798603343)
            ·
              refine ⟨10363697960068378197905015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6909131973378918798603343 10363697960068378197905015)
              ·
                refine ⟨15545546940102567296857523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363697960068378197905015 15545546940102567296857523)
                ·
                  refine ⟨23318320410153850945286285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15545546940102567296857523 23318320410153850945286285)
                  ·
                    refine ⟨8744370153807694104482357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23318320410153850945286285 8744370153807694104482357)
                    ·
                      refine ⟨819784701919471322295221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8744370153807694104482357 819784701919471322295221)
                      ·
                        rfl

theorem cell23_1596525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1596525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596525 prefixEnd_1596525 := by exact prefixLift 1596525
  have htrace : WordTrace (prefixWord ++ tailWord_1596525) baseStart_1596525 baseEnd_1596525 := by
    simpa [prefixWord, tailWord_1596525, baseEnd_1596525] using wordTrace_append hprefix tailTrace_1596525
  have hstable : (prefixWord ++ tailWord_1596525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596525).length < 2 ^ (prefixWord ++ tailWord_1596525).sum := by decide
  have hdescent : baseEnd_1596525 < baseStart_1596525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596555 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3]
def baseStart_1596555 : Nat := 118140960795 + 1596555 * 2 ^ 59
def prefixEnd_1596555 : Nat := 4983230072969 + 3 ^ 40 * 1596555 * 2
def baseEnd_1596555 : Nat := 819800106339106204920083

theorem tailTrace_1596555 : CollatzResearch.WordTrace tailWord_1596555 prefixEnd_1596555 819800106339106204920083 := by
  unfold tailWord_1596555
  simp only [CollatzResearch.WordTrace]
  refine ⟨58231144730961379730751119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38820763153974253153834079 58231144730961379730751119)
  ·
    refine ⟨87346717096442069596126679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58231144730961379730751119 87346717096442069596126679)
    ·
      refine ⟨131020075644663104394190019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87346717096442069596126679 131020075644663104394190019)
      ·
        refine ⟨196530113466994656591285029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131020075644663104394190019 196530113466994656591285029)
        ·
          refine ⟨36849396275061498110865943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196530113466994656591285029 36849396275061498110865943)
          ·
            refine ⟨55274094412592247166298915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36849396275061498110865943 55274094412592247166298915)
            ·
              refine ⟨82911141618888370749448373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55274094412592247166298915 82911141618888370749448373)
              ·
                refine ⟨7772919526770784757760785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82911141618888370749448373 7772919526770784757760785)
                ·
                  refine ⟨5829689645078088568320589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7772919526770784757760785 5829689645078088568320589)
                  ·
                    refine ⟨2186133616904283213120221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5829689645078088568320589 2186133616904283213120221)
                    ·
                      refine ⟨819800106339106204920083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2186133616904283213120221 819800106339106204920083)
                      ·
                        rfl

theorem cell23_1596555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 3].length) (baseStart_1596555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596555 prefixEnd_1596555 := by exact prefixLift 1596555
  have htrace : WordTrace (prefixWord ++ tailWord_1596555) baseStart_1596555 baseEnd_1596555 := by
    simpa [prefixWord, tailWord_1596555, baseEnd_1596555] using wordTrace_append hprefix tailTrace_1596555
  have hstable : (prefixWord ++ tailWord_1596555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596555).length < 2 ^ (prefixWord ++ tailWord_1596555).sum := by decide
  have hdescent : baseEnd_1596555 < baseStart_1596555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596629 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1596629 : Nat := 118140960795 + 1596629 * 2 ^ 59
def prefixEnd_1596629 : Nat := 4983230072969 + 3 ^ 40 * 1596629 * 2
def baseEnd_1596629 : Nat := 819838103907538915394743

theorem tailTrace_1596629 : CollatzResearch.WordTrace tailWord_1596629 prefixEnd_1596629 819838103907538915394743 := by
  unfold tailWord_1596629
  simp only [CollatzResearch.WordTrace]
  refine ⟨58233843732693290368944941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38822562488462193579296627 58233843732693290368944941)
  ·
    refine ⟨21837691399759983888354353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58233843732693290368944941 21837691399759983888354353)
    ·
      refine ⟨16378268549819987916265765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21837691399759983888354353 16378268549819987916265765)
      ·
        refine ⟨3070925353091247734299831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16378268549819987916265765 3070925353091247734299831)
        ·
          refine ⟨4606388029636871601449747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070925353091247734299831 4606388029636871601449747)
          ·
            refine ⟨6909582044455307402174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606388029636871601449747 6909582044455307402174621)
            ·
              refine ⟨2591093266670740275815483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6909582044455307402174621 2591093266670740275815483)
              ·
                refine ⟨3886639900006110413723225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2591093266670740275815483 3886639900006110413723225)
                ·
                  refine ⟨2914979925004582810292419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886639900006110413723225 2914979925004582810292419)
                  ·
                    refine ⟨4372469887506874215438629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914979925004582810292419 4372469887506874215438629)
                    ·
                      refine ⟨819838103907538915394743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4372469887506874215438629 819838103907538915394743)
                      ·
                        rfl

theorem cell23_1596629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1596629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596629 prefixEnd_1596629 := by exact prefixLift 1596629
  have htrace : WordTrace (prefixWord ++ tailWord_1596629) baseStart_1596629 baseEnd_1596629 := by
    simpa [prefixWord, tailWord_1596629, baseEnd_1596629] using wordTrace_append hprefix tailTrace_1596629
  have hstable : (prefixWord ++ tailWord_1596629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596629).length < 2 ^ (prefixWord ++ tailWord_1596629).sum := by decide
  have hdescent : baseEnd_1596629 < baseStart_1596629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596639 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 1, 4]
def baseStart_1596639 : Nat := 118140960795 + 1596639 * 2 ^ 59
def prefixEnd_1596639 : Nat := 4983230072969 + 3 ^ 40 * 1596639 * 2
def baseEnd_1596639 : Nat := 273281079571361292089899

theorem tailTrace_1596639 : CollatzResearch.WordTrace tailWord_1596639 prefixEnd_1596639 273281079571361292089899 := by
  unfold tailWord_1596639
  simp only [CollatzResearch.WordTrace]
  refine ⟨58234208462657062076808971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38822805641771374717872647 58234208462657062076808971)
  ·
    refine ⟨87351312693985593115213457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58234208462657062076808971 87351312693985593115213457)
    ·
      refine ⟨65513484520489194836410093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87351312693985593115213457 65513484520489194836410093)
      ·
        refine ⟨24567556695183448063653785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65513484520489194836410093 24567556695183448063653785)
        ·
          refine ⟨18425667521387586047740339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24567556695183448063653785 18425667521387586047740339)
          ·
            refine ⟨27638501282081379071610509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18425667521387586047740339 27638501282081379071610509)
            ·
              refine ⟨10364437980780517151853941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27638501282081379071610509 10364437980780517151853941)
              ·
                refine ⟨971666060698173482986307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10364437980780517151853941 971666060698173482986307)
                ·
                  refine ⟨1457499091047260224479461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971666060698173482986307 1457499091047260224479461)
                  ·
                    refine ⟨273281079571361292089899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1457499091047260224479461 273281079571361292089899)
                    ·
                      rfl

theorem cell23_1596639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 4].length) (baseStart_1596639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596639 prefixEnd_1596639 := by exact prefixLift 1596639
  have htrace : WordTrace (prefixWord ++ tailWord_1596639) baseStart_1596639 baseEnd_1596639 := by
    simpa [prefixWord, tailWord_1596639, baseEnd_1596639] using wordTrace_append hprefix tailTrace_1596639
  have hstable : (prefixWord ++ tailWord_1596639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596639).length < 2 ^ (prefixWord ++ tailWord_1596639).sum := by decide
  have hdescent : baseEnd_1596639 < baseStart_1596639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596652 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 6]
def baseStart_1596652 : Nat := 118140960795 + 1596652 * 2 ^ 59
def prefixEnd_1596652 : Nat := 4983230072969 + 3 ^ 40 * 1596652 * 2
def baseEnd_1596652 : Nat := 91094434884732480600793

theorem tailTrace_1596652 : CollatzResearch.WordTrace tailWord_1596652 prefixEnd_1596652 91094434884732480600793 := by
  unfold tailWord_1596652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29117341305804982648516105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38823121741073310198021473 29117341305804982648516105)
  ·
    refine ⟨21838005979353736986387079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29117341305804982648516105 21838005979353736986387079)
    ·
      refine ⟨32757008969030605479580619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21838005979353736986387079 32757008969030605479580619)
      ·
        refine ⟨49135513453545908219370929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32757008969030605479580619 49135513453545908219370929)
        ·
          refine ⟨36851635090159431164528197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49135513453545908219370929 36851635090159431164528197)
          ·
            refine ⟨6909681579404893343349037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36851635090159431164528197 6909681579404893343349037)
            ·
              refine ⟨2591130592276835003755889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6909681579404893343349037 2591130592276835003755889)
              ·
                refine ⟨1943347944207626252816917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591130592276835003755889 1943347944207626252816917)
                ·
                  refine ⟨91094434884732480600793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1943347944207626252816917 91094434884732480600793)
                  ·
                    rfl

theorem cell23_1596652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_1596652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596652 prefixEnd_1596652 := by exact prefixLift 1596652
  have htrace : WordTrace (prefixWord ++ tailWord_1596652) baseStart_1596652 baseEnd_1596652 := by
    simpa [prefixWord, tailWord_1596652, baseEnd_1596652] using wordTrace_append hprefix tailTrace_1596652
  have hstable : (prefixWord ++ tailWord_1596652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596652).length < 2 ^ (prefixWord ++ tailWord_1596652).sum := by decide
  have hdescent : baseEnd_1596652 < baseStart_1596652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596689 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_1596689 : Nat := 118140960795 + 1596689 * 2 ^ 59
def prefixEnd_1596689 : Nat := 4983230072969 + 3 ^ 40 * 1596689 * 2
def baseEnd_1596689 : Nat := 819868912746808680644467

theorem tailTrace_1596689 : CollatzResearch.WordTrace tailWord_1596689 prefixEnd_1596689 819868912746808680644467 := by
  unfold tailWord_1596689
  simp only [CollatzResearch.WordTrace]
  refine ⟨58236032112475920616129121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38824021408317280410752747 58236032112475920616129121)
  ·
    refine ⟨43677024084356940462096841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58236032112475920616129121 43677024084356940462096841)
    ·
      refine ⟨32757768063267705346572631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43677024084356940462096841 32757768063267705346572631)
      ·
        refine ⟨49136652094901558019858947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32757768063267705346572631 49136652094901558019858947)
        ·
          refine ⟨73704978142352337029788421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49136652094901558019858947 73704978142352337029788421)
          ·
            refine ⟨13819683401691063193085329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73704978142352337029788421 13819683401691063193085329)
            ·
              refine ⟨10364762551268297394813997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13819683401691063193085329 10364762551268297394813997)
              ·
                refine ⟨3886785956725611523055249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10364762551268297394813997 3886785956725611523055249)
                ·
                  refine ⟨2915089467544208642291437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3886785956725611523055249 2915089467544208642291437)
                  ·
                    refine ⟨1093158550329078240859289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915089467544208642291437 1093158550329078240859289)
                    ·
                      refine ⟨819868912746808680644467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093158550329078240859289 819868912746808680644467)
                      ·
                        rfl

theorem cell23_1596689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_1596689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596689 prefixEnd_1596689 := by exact prefixLift 1596689
  have htrace : WordTrace (prefixWord ++ tailWord_1596689) baseStart_1596689 baseEnd_1596689 := by
    simpa [prefixWord, tailWord_1596689, baseEnd_1596689] using wordTrace_append hprefix tailTrace_1596689
  have hstable : (prefixWord ++ tailWord_1596689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596689).length < 2 ^ (prefixWord ++ tailWord_1596689).sum := by decide
  have hdescent : baseEnd_1596689 < baseStart_1596689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596732 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1596732 : Nat := 118140960795 + 1596732 * 2 ^ 59
def prefixEnd_1596732 : Nat := 4983230072969 + 3 ^ 40 * 1596732 * 2
def baseEnd_1596732 : Nat := 819890992414952012406769

theorem tailTrace_1596732 : CollatzResearch.WordTrace tailWord_1596732 prefixEnd_1596732 819890992414952012406769 := by
  unfold tailWord_1596732
  simp only [CollatzResearch.WordTrace]
  refine ⟨29118800225660069479972225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38825066967546759306629633 29118800225660069479972225)
  ·
    refine ⟨21839100169245052109979169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29118800225660069479972225 21839100169245052109979169)
    ·
      refine ⟨16379325126933789082484377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21839100169245052109979169 16379325126933789082484377)
      ·
        refine ⟨12284493845200341811863283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16379325126933789082484377 12284493845200341811863283)
        ·
          refine ⟨18426740767800512717794925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284493845200341811863283 18426740767800512717794925)
          ·
            refine ⟨6910027787925192269173097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18426740767800512717794925 6910027787925192269173097)
            ·
              refine ⟨5182520840943894201879823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910027787925192269173097 5182520840943894201879823)
              ·
                refine ⟨7773781261415841302819735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5182520840943894201879823 7773781261415841302819735)
                ·
                  refine ⟨11660671892123761954229603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7773781261415841302819735 11660671892123761954229603)
                  ·
                    refine ⟨17491007838185642931344405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11660671892123761954229603 17491007838185642931344405)
                    ·
                      refine ⟨819890992414952012406769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17491007838185642931344405 819890992414952012406769)
                      ·
                        rfl

theorem cell23_1596732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1596732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596732 prefixEnd_1596732 := by exact prefixLift 1596732
  have htrace : WordTrace (prefixWord ++ tailWord_1596732) baseStart_1596732 baseEnd_1596732 := by
    simpa [prefixWord, tailWord_1596732, baseEnd_1596732] using wordTrace_append hprefix tailTrace_1596732
  have hstable : (prefixWord ++ tailWord_1596732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596732).length < 2 ^ (prefixWord ++ tailWord_1596732).sum := by decide
  have hdescent : baseEnd_1596732 < baseStart_1596732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596733 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1596733 : Nat := 118140960795 + 1596733 * 2 ^ 59
def prefixEnd_1596733 : Nat := 4983230072969 + 3 ^ 40 * 1596733 * 2
def baseEnd_1596733 : Nat := 273297168631868836164755

theorem tailTrace_1596733 : CollatzResearch.WordTrace tailWord_1596733 prefixEnd_1596733 273297168631868836164755 := by
  unfold tailWord_1596733
  simp only [CollatzResearch.WordTrace]
  refine ⟨58237636924316516130730853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38825091282877677420487235 58237636924316516130730853)
  ·
    refine ⟨10919556923309346774512035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58237636924316516130730853 10919556923309346774512035)
    ·
      refine ⟨16379335384964020161768053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919556923309346774512035 16379335384964020161768053)
      ·
        refine ⟨1535562692340376890165755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16379335384964020161768053 1535562692340376890165755)
        ·
          refine ⟨2303344038510565335248633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535562692340376890165755 2303344038510565335248633)
          ·
            refine ⟨1727508028882924001436475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303344038510565335248633 1727508028882924001436475)
            ·
              refine ⟨2591262043324386002154713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727508028882924001436475 2591262043324386002154713)
              ·
                refine ⟨1943446532493289501616035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591262043324386002154713 1943446532493289501616035)
                ·
                  refine ⟨2915169798739934252424053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943446532493289501616035 2915169798739934252424053)
                  ·
                    refine ⟨273297168631868836164755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2915169798739934252424053 273297168631868836164755)
                    ·
                      rfl

theorem cell23_1596733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1596733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596733 prefixEnd_1596733 := by exact prefixLift 1596733
  have htrace : WordTrace (prefixWord ++ tailWord_1596733) baseStart_1596733 baseEnd_1596733 := by
    simpa [prefixWord, tailWord_1596733, baseEnd_1596733] using wordTrace_append hprefix tailTrace_1596733
  have hstable : (prefixWord ++ tailWord_1596733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596733).length < 2 ^ (prefixWord ++ tailWord_1596733).sum := by decide
  have hdescent : baseEnd_1596733 < baseStart_1596733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596753 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 1, 2, 2]
def baseStart_1596753 : Nat := 118140960795 + 1596753 * 2 ^ 59
def prefixEnd_1596753 : Nat := 4983230072969 + 3 ^ 40 * 1596753 * 2
def baseEnd_1596753 : Nat := 819901775508696430244173

theorem tailTrace_1596753 : CollatzResearch.WordTrace tailWord_1596753 prefixEnd_1596753 819901775508696430244173 := by
  unfold tailWord_1596753
  simp only [CollatzResearch.WordTrace]
  refine ⟨58238366384244059546458913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38825577589496039697639275 58238366384244059546458913)
  ·
    refine ⟨43678774788183044659844185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58238366384244059546458913 43678774788183044659844185)
    ·
      refine ⟨32759081091137283494883139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43678774788183044659844185 32759081091137283494883139)
      ·
        refine ⟨49138621636705925242324709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32759081091137283494883139 49138621636705925242324709)
        ·
          refine ⟨9213491556882360982935883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49138621636705925242324709 9213491556882360982935883)
          ·
            refine ⟨13820237335323541474403825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9213491556882360982935883 13820237335323541474403825)
            ·
              refine ⟨10365178001492656105802869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13820237335323541474403825 10365178001492656105802869)
              ·
                refine ⟨971735437639936509919019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10365178001492656105802869 971735437639936509919019)
                ·
                  refine ⟨1457603156459904764878529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971735437639936509919019 1457603156459904764878529)
                  ·
                    refine ⟨1093202367344928573658897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457603156459904764878529 1093202367344928573658897)
                    ·
                      refine ⟨819901775508696430244173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093202367344928573658897 819901775508696430244173)
                      ·
                        rfl

theorem cell23_1596753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_1596753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596753 prefixEnd_1596753 := by exact prefixLift 1596753
  have htrace : WordTrace (prefixWord ++ tailWord_1596753) baseStart_1596753 baseEnd_1596753 := by
    simpa [prefixWord, tailWord_1596753, baseEnd_1596753] using wordTrace_append hprefix tailTrace_1596753
  have hstable : (prefixWord ++ tailWord_1596753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596753).length < 2 ^ (prefixWord ++ tailWord_1596753).sum := by decide
  have hdescent : baseEnd_1596753 < baseStart_1596753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596769 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_1596769 : Nat := 118140960795 + 1596769 * 2 ^ 59
def prefixEnd_1596769 : Nat := 4983230072969 + 3 ^ 40 * 1596769 * 2
def baseEnd_1596769 : Nat := 819909991199168367644099

theorem tailTrace_1596769 : CollatzResearch.WordTrace tailWord_1596769 prefixEnd_1596769 819909991199168367644099 := by
  unfold tailWord_1596769
  simp only [CollatzResearch.WordTrace]
  refine ⟨58238949952186094279041361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38825966634790729519360907 58238949952186094279041361)
  ·
    refine ⟨43679212464139570709281021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58238949952186094279041361 43679212464139570709281021)
    ·
      refine ⟨16379704674052339015980383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43679212464139570709281021 16379704674052339015980383)
      ·
        refine ⟨24569557011078508523970575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379704674052339015980383 24569557011078508523970575)
        ·
          refine ⟨36854335516617762785955863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24569557011078508523970575 36854335516617762785955863)
          ·
            refine ⟨55281503274926644178933795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36854335516617762785955863 55281503274926644178933795)
            ·
              refine ⟨82922254912389966268400693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55281503274926644178933795 82922254912389966268400693)
              ·
                refine ⟨7773961398036559337662565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82922254912389966268400693 7773961398036559337662565)
                ·
                  refine ⟨1457617762131854875811731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7773961398036559337662565 1457617762131854875811731)
                  ·
                    refine ⟨2186426643197782313717597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457617762131854875811731 2186426643197782313717597)
                    ·
                      refine ⟨819909991199168367644099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2186426643197782313717597 819909991199168367644099)
                      ·
                        rfl

theorem cell23_1596769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_1596769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596769 prefixEnd_1596769 := by exact prefixLift 1596769
  have htrace : WordTrace (prefixWord ++ tailWord_1596769) baseStart_1596769 baseEnd_1596769 := by
    simpa [prefixWord, tailWord_1596769, baseEnd_1596769] using wordTrace_append hprefix tailTrace_1596769
  have hstable : (prefixWord ++ tailWord_1596769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596769).length < 2 ^ (prefixWord ++ tailWord_1596769).sum := by decide
  have hdescent : baseEnd_1596769 < baseStart_1596769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596770 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1596770 : Nat := 118140960795 + 1596770 * 2 ^ 59
def prefixEnd_1596770 : Nat := 4983230072969 + 3 ^ 40 * 1596770 * 2
def baseEnd_1596770 : Nat := 819910504679822863731595

theorem tailTrace_1596770 : CollatzResearch.WordTrace tailWord_1596770 prefixEnd_1596770 819910504679822863731595 := by
  unfold tailWord_1596770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14559746606295617862456941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38825990950121647633218509 14559746606295617862456941)
  ·
    refine ⟨5459904977360856698421353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14559746606295617862456941 5459904977360856698421353)
    ·
      refine ⟨4094928733020642523816015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5459904977360856698421353 4094928733020642523816015)
      ·
        refine ⟨6142393099530963785724023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094928733020642523816015 6142393099530963785724023)
        ·
          refine ⟨9213589649296445678586035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6142393099530963785724023 9213589649296445678586035)
          ·
            refine ⟨13820384473944668517879053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9213589649296445678586035 13820384473944668517879053)
            ·
              refine ⟨5182644177729250694204645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13820384473944668517879053 5182644177729250694204645)
              ·
                refine ⟨971745783324234505163371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5182644177729250694204645 971745783324234505163371)
                ·
                  refine ⟨1457618674986351757745057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971745783324234505163371 1457618674986351757745057)
                  ·
                    refine ⟨1093214006239763818308793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1457618674986351757745057 1093214006239763818308793)
                    ·
                      refine ⟨819910504679822863731595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093214006239763818308793 819910504679822863731595)
                      ·
                        rfl

theorem cell23_1596770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1596770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596770 prefixEnd_1596770 := by exact prefixLift 1596770
  have htrace : WordTrace (prefixWord ++ tailWord_1596770) baseStart_1596770 baseEnd_1596770 := by
    simpa [prefixWord, tailWord_1596770, baseEnd_1596770] using wordTrace_append hprefix tailTrace_1596770
  have hstable : (prefixWord ++ tailWord_1596770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596770).length < 2 ^ (prefixWord ++ tailWord_1596770).sum := by decide
  have hdescent : baseEnd_1596770 < baseStart_1596770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596772 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1596772 : Nat := 118140960795 + 1596772 * 2 ^ 59
def prefixEnd_1596772 : Nat := 4983230072969 + 3 ^ 40 * 1596772 * 2
def baseEnd_1596772 : Nat := 273303843880377285302195

theorem tailTrace_1596772 : CollatzResearch.WordTrace tailWord_1596772 prefixEnd_1596772 273303843880377285302195 := by
  unfold tailWord_1596772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119529685587612895700285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38826039580783483860933713 29119529685587612895700285)
  ·
    refine ⟨10919823632095354835887607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29119529685587612895700285 10919823632095354835887607)
    ·
      refine ⟨16379735448143032253831411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919823632095354835887607 16379735448143032253831411)
      ·
        refine ⟨24569603172214548380747117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379735448143032253831411 24569603172214548380747117)
        ·
          refine ⟨9213601189580455642780169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24569603172214548380747117 9213601189580455642780169)
          ·
            refine ⟨6910200892185341732085127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9213601189580455642780169 6910200892185341732085127)
            ·
              refine ⟨10365301338278012598127691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6910200892185341732085127 10365301338278012598127691)
              ·
                refine ⟨15547952007417018897191537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10365301338278012598127691 15547952007417018897191537)
                ·
                  refine ⟨11660964005562764172893653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15547952007417018897191537 11660964005562764172893653)
                  ·
                    refine ⟨273303843880377285302195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11660964005562764172893653 273303843880377285302195)
                    ·
                      rfl

theorem cell23_1596772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1596772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596772 prefixEnd_1596772 := by exact prefixLift 1596772
  have htrace : WordTrace (prefixWord ++ tailWord_1596772) baseStart_1596772 baseEnd_1596772 := by
    simpa [prefixWord, tailWord_1596772, baseEnd_1596772] using wordTrace_append hprefix tailTrace_1596772
  have hstable : (prefixWord ++ tailWord_1596772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596772).length < 2 ^ (prefixWord ++ tailWord_1596772).sum := by decide
  have hdescent : baseEnd_1596772 < baseStart_1596772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596776 : List Nat := [2, 1, 4, 2, 4, 1, 1, 8]
def baseStart_1596776 : Nat := 118140960795 + 1596776 * 2 ^ 59
def prefixEnd_1596776 : Nat := 4983230072969 + 3 ^ 40 * 1596776 * 2
def baseEnd_1596776 : Nat := 30367169835694438528021

theorem tailTrace_1596776 : CollatzResearch.WordTrace tailWord_1596776 prefixEnd_1596776 30367169835694438528021 := by
  unfold tailWord_1596776
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119602631580367237273091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38826136842107156316364121 29119602631580367237273091)
  ·
    refine ⟨43679403947370550855909637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29119602631580367237273091 43679403947370550855909637)
    ·
      refine ⟨8189888240131978285483057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43679403947370550855909637 8189888240131978285483057)
      ·
        refine ⟨6142416180098983714112293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8189888240131978285483057 6142416180098983714112293)
        ·
          refine ⟨1151703033768559446396055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6142416180098983714112293 1151703033768559446396055)
          ·
            refine ⟨1727554550652839169594083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151703033768559446396055 1727554550652839169594083)
            ·
              refine ⟨2591331825979258754391125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727554550652839169594083 2591331825979258754391125)
              ·
                refine ⟨30367169835694438528021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2591331825979258754391125 30367169835694438528021)
                ·
                  rfl

theorem cell23_1596776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 8].length) (baseStart_1596776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596776 prefixEnd_1596776 := by exact prefixLift 1596776
  have htrace : WordTrace (prefixWord ++ tailWord_1596776) baseStart_1596776 baseEnd_1596776 := by
    simpa [prefixWord, tailWord_1596776, baseEnd_1596776] using wordTrace_append hprefix tailTrace_1596776
  have hstable : (prefixWord ++ tailWord_1596776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596776).length < 2 ^ (prefixWord ++ tailWord_1596776).sum := by decide
  have hdescent : baseEnd_1596776 < baseStart_1596776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596786 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1596786 : Nat := 118140960795 + 1596786 * 2 ^ 59
def prefixEnd_1596786 : Nat := 4983230072969 + 3 ^ 40 * 1596786 * 2
def baseEnd_1596786 : Nat := 819918720370294801131521

theorem tailTrace_1596786 : CollatzResearch.WordTrace tailWord_1596786 prefixEnd_1596786 819918720370294801131521 := by
  unfold tailWord_1596786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14559892498281126545602553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38826379995416337454940141 14559892498281126545602553)
  ·
    refine ⟨10919919373710844909201915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14559892498281126545602553 10919919373710844909201915)
    ·
      refine ⟨16379879060566267363802873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919919373710844909201915 16379879060566267363802873)
      ·
        refine ⟨12284909295424700522852155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16379879060566267363802873 12284909295424700522852155)
        ·
          refine ⟨18427363943137050784278233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12284909295424700522852155 18427363943137050784278233)
          ·
            refine ⟨13820522957352788088208675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18427363943137050784278233 13820522957352788088208675)
            ·
              refine ⟨20730784436029182132313013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13820522957352788088208675 20730784436029182132313013)
              ·
                refine ⟨1943511040877735824904345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20730784436029182132313013 1943511040877735824904345)
                ·
                  refine ⟨1457633280658301868678259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943511040877735824904345 1457633280658301868678259)
                  ·
                    refine ⟨2186449920987452803017389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457633280658301868678259 2186449920987452803017389)
                    ·
                      refine ⟨819918720370294801131521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2186449920987452803017389 819918720370294801131521)
                      ·
                        rfl

theorem cell23_1596786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1596786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596786 prefixEnd_1596786 := by exact prefixLift 1596786
  have htrace : WordTrace (prefixWord ++ tailWord_1596786) baseStart_1596786 baseEnd_1596786 := by
    simpa [prefixWord, tailWord_1596786, baseEnd_1596786] using wordTrace_append hprefix tailTrace_1596786
  have hstable : (prefixWord ++ tailWord_1596786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596786).length < 2 ^ (prefixWord ++ tailWord_1596786).sum := by decide
  have hdescent : baseEnd_1596786 < baseStart_1596786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596796 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_1596796 : Nat := 118140960795 + 1596796 * 2 ^ 59
def prefixEnd_1596796 : Nat := 4983230072969 + 3 ^ 40 * 1596796 * 2
def baseEnd_1596796 : Nat := 819923855176839762006475

theorem tailTrace_1596796 : CollatzResearch.WordTrace tailWord_1596796 prefixEnd_1596796 819923855176839762006475 := by
  unfold tailWord_1596796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29119967361544138945137121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38826623148725518593516161 29119967361544138945137121)
  ·
    refine ⟨21839975521158104208852841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29119967361544138945137121 21839975521158104208852841)
    ·
      refine ⟨16379981640868578156639631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21839975521158104208852841 16379981640868578156639631)
      ·
        refine ⟨24569972461302867234959447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16379981640868578156639631 24569972461302867234959447)
        ·
          refine ⟨36854958691954300852439171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24569972461302867234959447 36854958691954300852439171)
          ·
            refine ⟨55282438037931451278658757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36854958691954300852439171 55282438037931451278658757)
            ·
              refine ⟨10365457132112147114748517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55282438037931451278658757 10365457132112147114748517)
              ·
                refine ⟨1943523212271027584015347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10365457132112147114748517 1943523212271027584015347)
                ·
                  refine ⟨2915284818406541376023021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943523212271027584015347 2915284818406541376023021)
                  ·
                    refine ⟨1093231806902453016008633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915284818406541376023021 1093231806902453016008633)
                    ·
                      refine ⟨819923855176839762006475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093231806902453016008633 819923855176839762006475)
                      ·
                        rfl

theorem cell23_1596796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_1596796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596796 prefixEnd_1596796 := by exact prefixLift 1596796
  have htrace : WordTrace (prefixWord ++ tailWord_1596796) baseStart_1596796 baseEnd_1596796 := by
    simpa [prefixWord, tailWord_1596796, baseEnd_1596796] using wordTrace_append hprefix tailTrace_1596796
  have hstable : (prefixWord ++ tailWord_1596796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596796).length < 2 ^ (prefixWord ++ tailWord_1596796).sum := by decide
  have hdescent : baseEnd_1596796 < baseStart_1596796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596812 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1596812 : Nat := 118140960795 + 1596812 * 2 ^ 59
def prefixEnd_1596812 : Nat := 4983230072969 + 3 ^ 40 * 1596812 * 2
def baseEnd_1596812 : Nat := 819932070867311699406401

theorem tailTrace_1596812 : CollatzResearch.WordTrace tailWord_1596812 prefixEnd_1596812 819932070867311699406401 := by
  unfold tailWord_1596812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29120259145515156311428345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38827012194020208415237793 29120259145515156311428345)
  ·
    refine ⟨21840194359136367233571259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29120259145515156311428345 21840194359136367233571259)
    ·
      refine ⟨32760291538704550850356889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21840194359136367233571259 32760291538704550850356889)
      ·
        refine ⟨24570218654028413137767667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32760291538704550850356889 24570218654028413137767667)
        ·
          refine ⟨36855327981042619706651501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24570218654028413137767667 36855327981042619706651501)
          ·
            refine ⟨13820747992890982389994313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36855327981042619706651501 13820747992890982389994313)
            ·
              refine ⟨10365560994668236792495735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13820747992890982389994313 10365560994668236792495735)
              ·
                refine ⟨15548341492002355188743603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10365560994668236792495735 15548341492002355188743603)
                ·
                  refine ⟨23322512238003532783115405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15548341492002355188743603 23322512238003532783115405)
                  ·
                    refine ⟨8745942089251324793668277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23322512238003532783115405 8745942089251324793668277)
                    ·
                      refine ⟨819932070867311699406401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8745942089251324793668277 819932070867311699406401)
                      ·
                        rfl

theorem cell23_1596812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1596812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596812 prefixEnd_1596812 := by exact prefixLift 1596812
  have htrace : WordTrace (prefixWord ++ tailWord_1596812) baseStart_1596812 baseEnd_1596812 := by
    simpa [prefixWord, tailWord_1596812, baseEnd_1596812] using wordTrace_append hprefix tailTrace_1596812
  have hstable : (prefixWord ++ tailWord_1596812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596812).length < 2 ^ (prefixWord ++ tailWord_1596812).sum := by decide
  have hdescent : baseEnd_1596812 < baseStart_1596812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596820 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1596820 : Nat := 118140960795 + 1596820 * 2 ^ 59
def prefixEnd_1596820 : Nat := 4983230072969 + 3 ^ 40 * 1596820 * 2
def baseEnd_1596820 : Nat := 819936178712547668106365

theorem tailTrace_1596820 : CollatzResearch.WordTrace tailWord_1596820 prefixEnd_1596820 819936178712547668106365 := by
  unfold tailWord_1596820
  simp only [CollatzResearch.WordTrace]
  refine ⟨29120405037500664994573957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38827206716667553326098609 29120405037500664994573957)
  ·
    refine ⟨5460075944531374686482617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29120405037500664994573957 5460075944531374686482617)
    ·
      refine ⟨4095056958398531014861963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5460075944531374686482617 4095056958398531014861963)
      ·
        refine ⟨6142585437597796522292945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095056958398531014861963 6142585437597796522292945)
        ·
          refine ⟨4606939078198347391719709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6142585437597796522292945 4606939078198347391719709)
          ·
            refine ⟨1727602154324380271894891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4606939078198347391719709 1727602154324380271894891)
            ·
              refine ⟨2591403231486570407842337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727602154324380271894891 2591403231486570407842337)
              ·
                refine ⟨1943552423614927805881753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591403231486570407842337 1943552423614927805881753)
                ·
                  refine ⟨1457664317711195854411315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943552423614927805881753 1457664317711195854411315)
                  ·
                    refine ⟨2186496476566793781616973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457664317711195854411315 2186496476566793781616973)
                    ·
                      refine ⟨819936178712547668106365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2186496476566793781616973 819936178712547668106365)
                      ·
                        rfl

theorem cell23_1596820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1596820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596820 prefixEnd_1596820 := by exact prefixLift 1596820
  have htrace : WordTrace (prefixWord ++ tailWord_1596820) baseStart_1596820 baseEnd_1596820 := by
    simpa [prefixWord, tailWord_1596820, baseEnd_1596820] using wordTrace_append hprefix tailTrace_1596820
  have hstable : (prefixWord ++ tailWord_1596820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596820).length < 2 ^ (prefixWord ++ tailWord_1596820).sum := by decide
  have hdescent : baseEnd_1596820 < baseStart_1596820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596839 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1596839 : Nat := 118140960795 + 1596839 * 2 ^ 59
def prefixEnd_1596839 : Nat := 4983230072969 + 3 ^ 40 * 1596839 * 2
def baseEnd_1596839 : Nat := 819945934844983093768777

theorem tailTrace_1596839 : CollatzResearch.WordTrace tailWord_1596839 prefixEnd_1596839 819945934844983093768777 := by
  unfold tailWord_1596839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58241503061932496234089571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38827668707954997489393047 58241503061932496234089571)
  ·
    refine ⟨87362254592898744351134357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58241503061932496234089571 87362254592898744351134357)
    ·
      refine ⟨4095105684042128641459423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87362254592898744351134357 4095105684042128641459423)
      ·
        refine ⟨6142658526063192962189135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095105684042128641459423 6142658526063192962189135)
        ·
          refine ⟨9213987789094789443283703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6142658526063192962189135 9213987789094789443283703)
          ·
            refine ⟨13820981683642184164925555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9213987789094789443283703 13820981683642184164925555)
            ·
              refine ⟨20731472525463276247388333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13820981683642184164925555 20731472525463276247388333)
              ·
                refine ⟨7774302197048728592770625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20731472525463276247388333 7774302197048728592770625)
                ·
                  refine ⟨5830726647786546444577969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7774302197048728592770625 5830726647786546444577969)
                  ·
                    refine ⟨4373044985839909833433477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5830726647786546444577969 4373044985839909833433477)
                    ·
                      refine ⟨819945934844983093768777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4373044985839909833433477 819945934844983093768777)
                      ·
                        rfl

theorem cell23_1596839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1596839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596839 prefixEnd_1596839 := by exact prefixLift 1596839
  have htrace : WordTrace (prefixWord ++ tailWord_1596839) baseStart_1596839 baseEnd_1596839 := by
    simpa [prefixWord, tailWord_1596839, baseEnd_1596839] using wordTrace_append hprefix tailTrace_1596839
  have hstable : (prefixWord ++ tailWord_1596839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596839).length < 2 ^ (prefixWord ++ tailWord_1596839).sum := by decide
  have hdescent : baseEnd_1596839 < baseStart_1596839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596889 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1596889 : Nat := 118140960795 + 1596889 * 2 ^ 59
def prefixEnd_1596889 : Nat := 4983230072969 + 3 ^ 40 * 1596889 * 2
def baseEnd_1596889 : Nat := 819971608877707898143547

theorem tailTrace_1596889 : CollatzResearch.WordTrace tailWord_1596889 prefixEnd_1596889 819971608877707898143547 := by
  unfold tailWord_1596889
  simp only [CollatzResearch.WordTrace]
  refine ⟨58243326711751354773409721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38828884474500903182273147 58243326711751354773409721)
  ·
    refine ⟨43682495033813516080057291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58243326711751354773409721 43682495033813516080057291)
    ·
      refine ⟨65523742550720274120085937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43682495033813516080057291 65523742550720274120085937)
      ·
        refine ⟨49142806913040205590064453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65523742550720274120085937 49142806913040205590064453)
        ·
          refine ⟨9214276296195038548137085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49142806913040205590064453 9214276296195038548137085)
          ·
            refine ⟨3455353611073139455551407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9214276296195038548137085 3455353611073139455551407)
            ·
              refine ⟨5183030416609709183327111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455353611073139455551407 5183030416609709183327111)
              ·
                refine ⟨7774545624914563774990667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183030416609709183327111 7774545624914563774990667)
                ·
                  refine ⟨11661818437371845662486001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774545624914563774990667 11661818437371845662486001)
                  ·
                    refine ⟨8746363828028884246864501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11661818437371845662486001 8746363828028884246864501)
                    ·
                      refine ⟨819971608877707898143547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8746363828028884246864501 819971608877707898143547)
                      ·
                        rfl

theorem cell23_1596889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1596889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596889 prefixEnd_1596889 := by exact prefixLift 1596889
  have htrace : WordTrace (prefixWord ++ tailWord_1596889) baseStart_1596889 baseEnd_1596889 := by
    simpa [prefixWord, tailWord_1596889, baseEnd_1596889] using wordTrace_append hprefix tailTrace_1596889
  have hstable : (prefixWord ++ tailWord_1596889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596889).length < 2 ^ (prefixWord ++ tailWord_1596889).sum := by decide
  have hdescent : baseEnd_1596889 < baseStart_1596889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596936 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1596936 : Nat := 118140960795 + 1596936 * 2 ^ 59
def prefixEnd_1596936 : Nat := 4983230072969 + 3 ^ 40 * 1596936 * 2
def baseEnd_1596936 : Nat := 819995742468469214255831

theorem tailTrace_1596936 : CollatzResearch.WordTrace tailWord_1596936 prefixEnd_1596936 819995742468469214255831 := by
  unfold tailWord_1596936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122520471290540900185331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38830027295054054533580441 29122520471290540900185331)
  ·
    refine ⟨43683780706935811350277997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29122520471290540900185331 43683780706935811350277997)
    ·
      refine ⟨16381417765100929256354249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43683780706935811350277997 16381417765100929256354249)
      ·
        refine ⟨12286063323825696942265687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16381417765100929256354249 12286063323825696942265687)
        ·
          refine ⟨18429094985738545413398531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12286063323825696942265687 18429094985738545413398531)
          ·
            refine ⟨27643642478607818120097797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18429094985738545413398531 27643642478607818120097797)
            ·
              refine ⟨5183182964738965897518337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27643642478607818120097797 5183182964738965897518337)
              ·
                refine ⟨3887387223554224423138753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183182964738965897518337 3887387223554224423138753)
                ·
                  refine ⟨2915540417665668317354065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3887387223554224423138753 2915540417665668317354065)
                  ·
                    refine ⟨2186655313249251238015549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2915540417665668317354065 2186655313249251238015549)
                    ·
                      refine ⟨819995742468469214255831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2186655313249251238015549 819995742468469214255831)
                      ·
                        rfl

theorem cell23_1596936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1596936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596936 prefixEnd_1596936 := by exact prefixLift 1596936
  have htrace : WordTrace (prefixWord ++ tailWord_1596936) baseStart_1596936 baseEnd_1596936 := by
    simpa [prefixWord, tailWord_1596936, baseEnd_1596936] using wordTrace_append hprefix tailTrace_1596936
  have hstable : (prefixWord ++ tailWord_1596936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596936).length < 2 ^ (prefixWord ++ tailWord_1596936).sum := by decide
  have hdescent : baseEnd_1596936 < baseStart_1596936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596986 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_1596986 : Nat := 118140960795 + 1596986 * 2 ^ 59
def prefixEnd_1596986 : Nat := 4983230072969 + 3 ^ 40 * 1596986 * 2
def baseEnd_1596986 : Nat := 273340472167064672876867

theorem tailTrace_1596986 : CollatzResearch.WordTrace tailWord_1596986 prefixEnd_1596986 273340472167064672876867 := by
  unfold tailWord_1596986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561716148099985084922703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38831243061599960226460541 14561716148099985084922703)
  ·
    refine ⟨21842574222149977627384055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14561716148099985084922703 21842574222149977627384055)
    ·
      refine ⟨32763861333224966441076083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21842574222149977627384055 32763861333224966441076083)
      ·
        refine ⟨49145791999837449661614125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32763861333224966441076083 49145791999837449661614125)
        ·
          refine ⟨18429671999939043623105297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49145791999837449661614125 18429671999939043623105297)
          ·
            refine ⟨13822253999954282717328973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18429671999939043623105297 13822253999954282717328973)
            ·
              refine ⟨5183345249982856018998365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13822253999954282717328973 5183345249982856018998365)
              ·
                refine ⟨1943754468743571007124387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5183345249982856018998365 1943754468743571007124387)
                ·
                  refine ⟨2915631703115356510686581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943754468743571007124387 2915631703115356510686581)
                  ·
                    refine ⟨273340472167064672876867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2915631703115356510686581 273340472167064672876867)
                    ·
                      rfl

theorem cell23_1596986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_1596986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596986 prefixEnd_1596986 := by exact prefixLift 1596986
  have htrace : WordTrace (prefixWord ++ tailWord_1596986) baseStart_1596986 baseEnd_1596986 := by
    simpa [prefixWord, tailWord_1596986, baseEnd_1596986] using wordTrace_append hprefix tailTrace_1596986
  have hstable : (prefixWord ++ tailWord_1596986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596986).length < 2 ^ (prefixWord ++ tailWord_1596986).sum := by decide
  have hdescent : baseEnd_1596986 < baseStart_1596986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1596993 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1596993 : Nat := 118140960795 + 1596993 * 2 ^ 59
def prefixEnd_1596993 : Nat := 4983230072969 + 3 ^ 40 * 1596993 * 2
def baseEnd_1596993 : Nat := 820025010865775491243069

theorem tailTrace_1596993 : CollatzResearch.WordTrace tailWord_1596993 prefixEnd_1596993 820025010865775491243069 := by
  unfold tailWord_1596993
  simp only [CollatzResearch.WordTrace]
  refine ⟨58247119903374580535195633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38831413268916387023463755 58247119903374580535195633)
  ·
    refine ⟨43685339927530935401396725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58247119903374580535195633 43685339927530935401396725)
    ·
      refine ⟨4095500618206025193880943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43685339927530935401396725 4095500618206025193880943)
      ·
        refine ⟨6143250927309037790821415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095500618206025193880943 6143250927309037790821415)
        ·
          refine ⟨9214876390963556686232123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143250927309037790821415 9214876390963556686232123)
          ·
            refine ⟨13822314586445335029348185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214876390963556686232123 13822314586445335029348185)
            ·
              refine ⟨10366735939834001272011139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13822314586445335029348185 10366735939834001272011139)
              ·
                refine ⟨15550103909751001908016709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366735939834001272011139 15550103909751001908016709)
                ·
                  refine ⟨2915644483078312857753133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15550103909751001908016709 2915644483078312857753133)
                  ·
                    refine ⟨1093366681154367321657425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915644483078312857753133 1093366681154367321657425)
                    ·
                      refine ⟨820025010865775491243069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1093366681154367321657425 820025010865775491243069)
                      ·
                        rfl

theorem cell23_1596993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1596993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1596993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1596993 prefixEnd_1596993 := by exact prefixLift 1596993
  have htrace : WordTrace (prefixWord ++ tailWord_1596993) baseStart_1596993 baseEnd_1596993 := by
    simpa [prefixWord, tailWord_1596993, baseEnd_1596993] using wordTrace_append hprefix tailTrace_1596993
  have hstable : (prefixWord ++ tailWord_1596993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1596993).length < 2 ^ (prefixWord ++ tailWord_1596993).sum := by decide
  have hdescent : baseEnd_1596993 < baseStart_1596993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1596993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597046 : List Nat := [5, 1, 1, 2, 2, 1, 11]
def baseStart_1597046 : Nat := 118140960795 + 1597046 * 2 ^ 59
def prefixEnd_1597046 : Nat := 4983230072969 + 3 ^ 40 * 1597046 * 2
def baseEnd_1597046 : Nat := 10124101547413133134325

theorem tailTrace_1597046 : CollatzResearch.WordTrace tailWord_1597046 prefixEnd_1597046 10124101547413133134325 := by
  unfold tailWord_1597046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640565810761410661679687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38832701981455047057916661 3640565810761410661679687)
  ·
    refine ⟨5460848716142115992519531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640565810761410661679687 5460848716142115992519531)
    ·
      refine ⟨8191273074213173988779297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460848716142115992519531 8191273074213173988779297)
      ·
        refine ⟨6143454805659880491584473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8191273074213173988779297 6143454805659880491584473)
        ·
          refine ⟨4607591104244910368688355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6143454805659880491584473 4607591104244910368688355)
          ·
            refine ⟨6911386656367365553032533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607591104244910368688355 6911386656367365553032533)
            ·
              refine ⟨10124101547413133134325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6911386656367365553032533 10124101547413133134325)
              ·
                rfl

theorem cell23_1597046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 11].length) (baseStart_1597046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1597046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1597046 prefixEnd_1597046 := by exact prefixLift 1597046
  have htrace : WordTrace (prefixWord ++ tailWord_1597046) baseStart_1597046 baseEnd_1597046 := by
    simpa [prefixWord, tailWord_1597046, baseEnd_1597046] using wordTrace_append hprefix tailTrace_1597046
  have hstable : (prefixWord ++ tailWord_1597046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597046).length < 2 ^ (prefixWord ++ tailWord_1597046).sum := by decide
  have hdescent : baseEnd_1597046 < baseStart_1597046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
