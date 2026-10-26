import V185TrunkScan22Chunk189

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1695349 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1695349 : Nat := 118140960795 + 1695349 * 2 ^ 59
def prefixEnd_1695349 : Nat := 4983230072969 + 3 ^ 40 * 1695349 * 2
def baseEnd_1695349 : Nat := 580352609412928448627159

theorem tailTrace_1695349 : CollatzResearch.WordTrace tailWord_1695349 prefixEnd_1695349 580352609412928448627159 := by
  unfold tailWord_1695349
  simp only [CollatzResearch.WordTrace]
  refine ⟨61834457935047590402649101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41222971956698393601766067 61834457935047590402649101)
  ·
    refine ⟨23187921725642846400993413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61834457935047590402649101 23187921725642846400993413)
    ·
      refine ⟨4347735323558033700186265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23187921725642846400993413 4347735323558033700186265)
      ·
        refine ⟨3260801492668525275139699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4347735323558033700186265 3260801492668525275139699)
        ·
          refine ⟨4891202239002787912709549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260801492668525275139699 4891202239002787912709549)
          ·
            refine ⟨1834200839626045467266081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4891202239002787912709549 1834200839626045467266081)
            ·
              refine ⟨1375650629719534100449561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834200839626045467266081 1375650629719534100449561)
              ·
                refine ⟨1031737972289650575337171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375650629719534100449561 1031737972289650575337171)
                ·
                  refine ⟨1547606958434475863005757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031737972289650575337171 1547606958434475863005757)
                  ·
                    refine ⟨580352609412928448627159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547606958434475863005757 580352609412928448627159)
                    ·
                      rfl

theorem cell22_1695349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1695349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695349 prefixEnd_1695349 := by exact prefixLift 1695349
  have htrace : WordTrace (prefixWord ++ tailWord_1695349) baseStart_1695349 baseEnd_1695349 := by
    simpa [prefixWord, tailWord_1695349, baseEnd_1695349] using wordTrace_append hprefix tailTrace_1695349
  have hstable : (prefixWord ++ tailWord_1695349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695349).length < 2 ^ (prefixWord ++ tailWord_1695349).sum := by decide
  have hdescent : baseEnd_1695349 < baseStart_1695349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695371 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 1, 5]
def baseStart_1695371 : Nat := 118140960795 + 1695371 * 2 ^ 59
def prefixEnd_1695371 : Nat := 4983230072969 + 3 ^ 40 * 1695371 * 2
def baseEnd_1695371 : Nat := 580360140462527724577091

theorem tailTrace_1695371 : CollatzResearch.WordTrace tailWord_1695371 prefixEnd_1695371 580360140462527724577091 := by
  unfold tailWord_1695371
  simp only [CollatzResearch.WordTrace]
  refine ⟨61835260340967888159949967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41223506893978592106633311 61835260340967888159949967)
  ·
    refine ⟨92752890511451832239924951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61835260340967888159949967 92752890511451832239924951)
    ·
      refine ⟨139129335767177748359887427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92752890511451832239924951 139129335767177748359887427)
      ·
        refine ⟨208694003650766622539831141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139129335767177748359887427 208694003650766622539831141)
        ·
          refine ⟨39130125684518741726218339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208694003650766622539831141 39130125684518741726218339)
          ·
            refine ⟨58695188526778112589327509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39130125684518741726218339 58695188526778112589327509)
            ·
              refine ⟨2751336962192724027624727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58695188526778112589327509 2751336962192724027624727)
              ·
                refine ⟨4127005443289086041437091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751336962192724027624727 4127005443289086041437091)
                ·
                  refine ⟨6190508164933629062155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127005443289086041437091 6190508164933629062155637)
                  ·
                    refine ⟨580360140462527724577091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6190508164933629062155637 580360140462527724577091)
                    ·
                      rfl

theorem cell22_1695371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_1695371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695371 prefixEnd_1695371 := by exact prefixLift 1695371
  have htrace : WordTrace (prefixWord ++ tailWord_1695371) baseStart_1695371 baseEnd_1695371 := by
    simpa [prefixWord, tailWord_1695371, baseEnd_1695371] using wordTrace_append hprefix tailTrace_1695371
  have hstable : (prefixWord ++ tailWord_1695371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695371).length < 2 ^ (prefixWord ++ tailWord_1695371).sum := by decide
  have hdescent : baseEnd_1695371 < baseStart_1695371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695390 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1695390 : Nat := 118140960795 + 1695390 * 2 ^ 59
def prefixEnd_1695390 : Nat := 4983230072969 + 3 ^ 40 * 1695390 * 2
def baseEnd_1695390 : Nat := 193455548183606002784011

theorem tailTrace_1695390 : CollatzResearch.WordTrace tailWord_1695390 prefixEnd_1695390 193455548183606002784011 := by
  unfold tailWord_1695390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729494165987381800611453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41223968885266036269927749 7729494165987381800611453)
  ·
    refine ⟨2898560312245268175229295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7729494165987381800611453 2898560312245268175229295)
    ·
      refine ⟨4347840468367902262843943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898560312245268175229295 4347840468367902262843943)
      ·
        refine ⟨6521760702551853394265915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347840468367902262843943 6521760702551853394265915)
        ·
          refine ⟨9782641053827780091398873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521760702551853394265915 9782641053827780091398873)
          ·
            refine ⟨7336980790370835068549155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9782641053827780091398873 7336980790370835068549155)
            ·
              refine ⟨11005471185556252602823733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7336980790370835068549155 11005471185556252602823733)
              ·
                refine ⟨1031762923645898681514725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11005471185556252602823733 1031762923645898681514725)
                ·
                  refine ⟨193455548183606002784011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031762923645898681514725 193455548183606002784011)
                  ·
                    rfl

theorem cell22_1695390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1695390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695390 prefixEnd_1695390 := by exact prefixLift 1695390
  have htrace : WordTrace (prefixWord ++ tailWord_1695390) baseStart_1695390 baseEnd_1695390 := by
    simpa [prefixWord, tailWord_1695390, baseEnd_1695390] using wordTrace_append hprefix tailTrace_1695390
  have hstable : (prefixWord ++ tailWord_1695390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695390).length < 2 ^ (prefixWord ++ tailWord_1695390).sum := by decide
  have hdescent : baseEnd_1695390 < baseStart_1695390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695422 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1695422 : Nat := 118140960795 + 1695422 * 2 ^ 59
def prefixEnd_1695422 : Nat := 4983230072969 + 3 ^ 40 * 1695422 * 2
def baseEnd_1695422 : Nat := 580377598804780591551935

theorem tailTrace_1695422 : CollatzResearch.WordTrace tailWord_1695422 prefixEnd_1695422 580377598804780591551935 := by
  unfold tailWord_1695422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729640057972890483757065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41224746975855415913371013 7729640057972890483757065)
  ·
    refine ⟨5797230043479667862817799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7729640057972890483757065 5797230043479667862817799)
    ·
      refine ⟨8695845065219501794226699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5797230043479667862817799 8695845065219501794226699)
      ·
        refine ⟨13043767597829252691340049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695845065219501794226699 13043767597829252691340049)
        ·
          refine ⟨9782825698371939518505037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13043767597829252691340049 9782825698371939518505037)
          ·
            refine ⟨3668559636889477319439389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9782825698371939518505037 3668559636889477319439389)
            ·
              refine ⟨1375709863833553994789771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3668559636889477319439389 1375709863833553994789771)
              ·
                refine ⟨2063564795750330992184657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375709863833553994789771 2063564795750330992184657)
                ·
                  refine ⟨1547673596812748244138493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063564795750330992184657 1547673596812748244138493)
                  ·
                    refine ⟨580377598804780591551935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547673596812748244138493 580377598804780591551935)
                    ·
                      rfl

theorem cell22_1695422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1695422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695422 prefixEnd_1695422 := by exact prefixLift 1695422
  have htrace : WordTrace (prefixWord ++ tailWord_1695422) baseStart_1695422 baseEnd_1695422 := by
    simpa [prefixWord, tailWord_1695422, baseEnd_1695422] using wordTrace_append hprefix tailTrace_1695422
  have hstable : (prefixWord ++ tailWord_1695422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695422).length < 2 ^ (prefixWord ++ tailWord_1695422).sum := by decide
  have hdescent : baseEnd_1695422 < baseStart_1695422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695491 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 6]
def baseStart_1695491 : Nat := 118140960795 + 1695491 * 2 ^ 59
def prefixEnd_1695491 : Nat := 4983230072969 + 3 ^ 40 * 1695491 * 2
def baseEnd_1695491 : Nat := 193467072971629137192241

theorem tailTrace_1695491 : CollatzResearch.WordTrace tailWord_1695491 prefixEnd_1695491 193467072971629137192241 := by
  unfold tailWord_1695491
  simp only [CollatzResearch.WordTrace]
  refine ⟨61839637100533148654318327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41226424733688765769545551 61839637100533148654318327)
  ·
    refine ⟨92759455650799722981477491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61839637100533148654318327 92759455650799722981477491)
    ·
      refine ⟨139139183476199584472216237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92759455650799722981477491 139139183476199584472216237)
      ·
        refine ⟨52177193803574844177081089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139139183476199584472216237 52177193803574844177081089)
        ·
          refine ⟨39132895352681133132810817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52177193803574844177081089 39132895352681133132810817)
          ·
            refine ⟨29349671514510849849608113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39132895352681133132810817 29349671514510849849608113)
            ·
              refine ⟨22012253635883137387206085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29349671514510849849608113 22012253635883137387206085)
              ·
                refine ⟨4127297556728088260101141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22012253635883137387206085 4127297556728088260101141)
                ·
                  refine ⟨193467072971629137192241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4127297556728088260101141 193467072971629137192241)
                  ·
                    rfl

theorem cell22_1695491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 6].length) (baseStart_1695491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695491 prefixEnd_1695491 := by exact prefixLift 1695491
  have htrace : WordTrace (prefixWord ++ tailWord_1695491) baseStart_1695491 baseEnd_1695491 := by
    simpa [prefixWord, tailWord_1695491, baseEnd_1695491] using wordTrace_append hprefix tailTrace_1695491
  have hstable : (prefixWord ++ tailWord_1695491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695491).length < 2 ^ (prefixWord ++ tailWord_1695491).sum := by decide
  have hdescent : baseEnd_1695491 < baseStart_1695491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695523 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 4, 3]
def baseStart_1695523 : Nat := 118140960795 + 1695523 * 2 ^ 59
def prefixEnd_1695523 : Nat := 4983230072969 + 3 ^ 40 * 1695523 * 2
def baseEnd_1695523 : Nat := 580412173168849994776625

theorem tailTrace_1695523 : CollatzResearch.WordTrace tailWord_1695523 prefixEnd_1695523 580412173168849994776625 := by
  unfold tailWord_1695523
  simp only [CollatzResearch.WordTrace]
  refine ⟨61840804236417218119483223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41227202824278145412988815 61840804236417218119483223)
  ·
    refine ⟨92761206354625827179224835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61840804236417218119483223 92761206354625827179224835)
    ·
      refine ⟨139141809531938740768837253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92761206354625827179224835 139141809531938740768837253)
      ·
        refine ⟨26089089287238513894156985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139141809531938740768837253 26089089287238513894156985)
        ·
          refine ⟨19566816965428885420617739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26089089287238513894156985 19566816965428885420617739)
          ·
            refine ⟨29350225448143328130926609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19566816965428885420617739 29350225448143328130926609)
            ·
              refine ⟨22012669086107496098194957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29350225448143328130926609 22012669086107496098194957)
              ·
                refine ⟨8254750907290311036823109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22012669086107496098194957 8254750907290311036823109)
                ·
                  refine ⟨1547765795116933319404333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8254750907290311036823109 1547765795116933319404333)
                  ·
                    refine ⟨580412173168849994776625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547765795116933319404333 580412173168849994776625)
                    ·
                      rfl

theorem cell22_1695523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 3].length) (baseStart_1695523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695523 prefixEnd_1695523 := by exact prefixLift 1695523
  have htrace : WordTrace (prefixWord ++ tailWord_1695523) baseStart_1695523 baseEnd_1695523 := by
    simpa [prefixWord, tailWord_1695523, baseEnd_1695523] using wordTrace_append hprefix tailTrace_1695523
  have hstable : (prefixWord ++ tailWord_1695523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695523).length < 2 ^ (prefixWord ++ tailWord_1695523).sum := by decide
  have hdescent : baseEnd_1695523 < baseStart_1695523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695525 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 4]
def baseStart_1695525 : Nat := 118140960795 + 1695525 * 2 ^ 59
def prefixEnd_1695525 : Nat := 4983230072969 + 3 ^ 40 * 1695525 * 2
def baseEnd_1695525 : Nat := 193470952603240885408873

theorem tailTrace_1695525 : CollatzResearch.WordTrace tailWord_1695525 prefixEnd_1695525 193470952603240885408873 := by
  unfold tailWord_1695525
  simp only [CollatzResearch.WordTrace]
  refine ⟨61840877182409972461056029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41227251454939981640704019 61840877182409972461056029)
  ·
    refine ⟨23190328943403739672896011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61840877182409972461056029 23190328943403739672896011)
    ·
      refine ⟨34785493415105609509344017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23190328943403739672896011 34785493415105609509344017)
      ·
        refine ⟨26089120061329207132008013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34785493415105609509344017 26089120061329207132008013)
        ·
          refine ⟨9783420022998452674503005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26089120061329207132008013 9783420022998452674503005)
          ·
            refine ⟨3668782508624419752938627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9783420022998452674503005 3668782508624419752938627)
            ·
              refine ⟨5503173762936629629407941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668782508624419752938627 5503173762936629629407941)
              ·
                refine ⟨1031845080550618055513989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5503173762936629629407941 1031845080550618055513989)
                ·
                  refine ⟨193470952603240885408873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031845080550618055513989 193470952603240885408873)
                  ·
                    rfl

theorem cell22_1695525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_1695525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695525 prefixEnd_1695525 := by exact prefixLift 1695525
  have htrace : WordTrace (prefixWord ++ tailWord_1695525) baseStart_1695525 baseEnd_1695525 := by
    simpa [prefixWord, tailWord_1695525, baseEnd_1695525] using wordTrace_append hprefix tailTrace_1695525
  have hstable : (prefixWord ++ tailWord_1695525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695525).length < 2 ^ (prefixWord ++ tailWord_1695525).sum := by decide
  have hdescent : baseEnd_1695525 < baseStart_1695525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695540 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1695540 : Nat := 118140960795 + 1695540 * 2 ^ 59
def prefixEnd_1695540 : Nat := 4983230072969 + 3 ^ 40 * 1695540 * 2
def baseEnd_1695540 : Nat := 580417992616267617101573

theorem tailTrace_1695540 : CollatzResearch.WordTrace tailWord_1695540 prefixEnd_1695540 580417992616267617101573 := by
  unfold tailWord_1695540
  simp only [CollatzResearch.WordTrace]
  refine ⟨30920712138677815011426037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41227616184903753348568049 30920712138677815011426037)
  ·
    refine ⟨2898816763001045157321191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30920712138677815011426037 2898816763001045157321191)
    ·
      refine ⟨4348225144501567735981787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2898816763001045157321191 4348225144501567735981787)
      ·
        refine ⟨6522337716752351603972681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348225144501567735981787 6522337716752351603972681)
        ·
          refine ⟨4891753287564263702979511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522337716752351603972681 4891753287564263702979511)
          ·
            refine ⟨7337629931346395554469267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891753287564263702979511 7337629931346395554469267)
            ·
              refine ⟨11006444897019593331703901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337629931346395554469267 11006444897019593331703901)
              ·
                refine ⟨4127416836382347499388963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11006444897019593331703901 4127416836382347499388963)
                ·
                  refine ⟨6191125254573521249083445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127416836382347499388963 6191125254573521249083445)
                  ·
                    refine ⟨580417992616267617101573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6191125254573521249083445 580417992616267617101573)
                    ·
                      rfl

theorem cell22_1695540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1695540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695540 prefixEnd_1695540 := by exact prefixLift 1695540
  have htrace : WordTrace (prefixWord ++ tailWord_1695540) baseStart_1695540 baseEnd_1695540 := by
    simpa [prefixWord, tailWord_1695540, baseEnd_1695540] using wordTrace_append hprefix tailTrace_1695540
  have hstable : (prefixWord ++ tailWord_1695540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695540).length < 2 ^ (prefixWord ++ tailWord_1695540).sum := by decide
  have hdescent : baseEnd_1695540 < baseStart_1695540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695555 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 2, 4]
def baseStart_1695555 : Nat := 118140960795 + 1695555 * 2 ^ 59
def prefixEnd_1695555 : Nat := 4983230072969 + 3 ^ 40 * 1695555 * 2
def baseEnd_1695555 : Nat := 580423127422812577976527

theorem tailTrace_1695555 : CollatzResearch.WordTrace tailWord_1695555 prefixEnd_1695555 580423127422812577976527 := by
  unfold tailWord_1695555
  simp only [CollatzResearch.WordTrace]
  refine ⟨61841971372301287584648119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41227980914867525056432079 61841971372301287584648119)
  ·
    refine ⟨92762957058451931376972179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61841971372301287584648119 92762957058451931376972179)
    ·
      refine ⟨139144435587677897065458269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92762957058451931376972179 139144435587677897065458269)
      ·
        refine ⟨52179163345379211399546851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139144435587677897065458269 52179163345379211399546851)
        ·
          refine ⟨78268745018068817099320277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52179163345379211399546851 78268745018068817099320277)
          ·
            refine ⟨1834423711360987900765319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78268745018068817099320277 1834423711360987900765319)
            ·
              refine ⟨2751635567041481851147979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834423711360987900765319 2751635567041481851147979)
              ·
                refine ⟨4127453350562222776721969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751635567041481851147979 4127453350562222776721969)
                ·
                  refine ⟨3095590012921667082541477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127453350562222776721969 3095590012921667082541477)
                  ·
                    refine ⟨580423127422812577976527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3095590012921667082541477 580423127422812577976527)
                    ·
                      rfl

theorem cell22_1695555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 4].length) (baseStart_1695555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695555 prefixEnd_1695555 := by exact prefixLift 1695555
  have htrace : WordTrace (prefixWord ++ tailWord_1695555) baseStart_1695555 baseEnd_1695555 := by
    simpa [prefixWord, tailWord_1695555, baseEnd_1695555] using wordTrace_append hprefix tailTrace_1695555
  have hstable : (prefixWord ++ tailWord_1695555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695555).length < 2 ^ (prefixWord ++ tailWord_1695555).sum := by decide
  have hdescent : baseEnd_1695555 < baseStart_1695555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695568 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_1695568 : Nat := 118140960795 + 1695568 * 2 ^ 59
def prefixEnd_1695568 : Nat := 4983230072969 + 3 ^ 40 * 1695568 * 2
def baseEnd_1695568 : Nat := 580427577588484877401487

theorem tailTrace_1695568 : CollatzResearch.WordTrace tailWord_1695568 prefixEnd_1695568 580427577588484877401487 := by
  unfold tailWord_1695568
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921222760627095402435679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41228297014169460536580905 30921222760627095402435679)
  ·
    refine ⟨46381834140940643103653519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30921222760627095402435679 46381834140940643103653519)
    ·
      refine ⟨69572751211410964655480279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46381834140940643103653519 69572751211410964655480279)
      ·
        refine ⟨104359126817116446983220419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69572751211410964655480279 104359126817116446983220419)
        ·
          refine ⟨156538690225674670474830629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104359126817116446983220419 156538690225674670474830629)
          ·
            refine ⟨29351004417314000714030743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156538690225674670474830629 29351004417314000714030743)
            ·
              refine ⟨44026506625971001071046115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29351004417314000714030743 44026506625971001071046115)
              ·
                refine ⟨66039759938956501606569173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44026506625971001071046115 66039759938956501606569173)
                ·
                  refine ⟨1547806873569293006403965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66039759938956501606569173 1547806873569293006403965)
                  ·
                    refine ⟨580427577588484877401487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547806873569293006403965 580427577588484877401487)
                    ·
                      rfl

theorem cell22_1695568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_1695568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695568 prefixEnd_1695568 := by exact prefixLift 1695568
  have htrace : WordTrace (prefixWord ++ tailWord_1695568) baseStart_1695568 baseEnd_1695568 := by
    simpa [prefixWord, tailWord_1695568, baseEnd_1695568] using wordTrace_append hprefix tailTrace_1695568
  have hstable : (prefixWord ++ tailWord_1695568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695568).length < 2 ^ (prefixWord ++ tailWord_1695568).sum := by decide
  have hdescent : baseEnd_1695568 < baseStart_1695568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695585 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1695585 : Nat := 118140960795 + 1695585 * 2 ^ 59
def prefixEnd_1695585 : Nat := 4983230072969 + 3 ^ 40 * 1695585 * 2
def baseEnd_1695585 : Nat := 580433397035902499726435

theorem tailTrace_1695585 : CollatzResearch.WordTrace tailWord_1695585 prefixEnd_1695585 580433397035902499726435 := by
  unfold tailWord_1695585
  simp only [CollatzResearch.WordTrace]
  refine ⟨61843065562192602708240209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41228710374795068472160139 61843065562192602708240209)
  ·
    refine ⟨46382299171644452031180157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61843065562192602708240209 46382299171644452031180157)
    ·
      refine ⟨17393362189366669511692559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46382299171644452031180157 17393362189366669511692559)
      ·
        refine ⟨26090043284050004267538839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17393362189366669511692559 26090043284050004267538839)
        ·
          refine ⟨39135064926075006401308259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26090043284050004267538839 39135064926075006401308259)
          ·
            refine ⟨58702597389112509601962389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39135064926075006401308259 58702597389112509601962389)
            ·
              refine ⟨2751684252614648887591987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58702597389112509601962389 2751684252614648887591987)
              ·
                refine ⟨4127526378921973331387981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751684252614648887591987 4127526378921973331387981)
                ·
                  refine ⟨1547822392095739999270493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4127526378921973331387981 1547822392095739999270493)
                  ·
                    refine ⟨580433397035902499726435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547822392095739999270493 580433397035902499726435)
                    ·
                      rfl

theorem cell22_1695585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1695585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695585 prefixEnd_1695585 := by exact prefixLift 1695585
  have htrace : WordTrace (prefixWord ++ tailWord_1695585) baseStart_1695585 baseEnd_1695585 := by
    simpa [prefixWord, tailWord_1695585, baseEnd_1695585] using wordTrace_append hprefix tailTrace_1695585
  have hstable : (prefixWord ++ tailWord_1695585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695585).length < 2 ^ (prefixWord ++ tailWord_1695585).sum := by decide
  have hdescent : baseEnd_1695585 < baseStart_1695585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695619 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 1, 3]
def baseStart_1695619 : Nat := 118140960795 + 1695619 * 2 ^ 59
def prefixEnd_1695619 : Nat := 4983230072969 + 3 ^ 40 * 1695619 * 2
def baseEnd_1695619 : Nat := 580445035930737744376331

theorem tailTrace_1695619 : CollatzResearch.WordTrace tailWord_1695619 prefixEnd_1695619 580445035930737744376331 := by
  unfold tailWord_1695619
  simp only [CollatzResearch.WordTrace]
  refine ⟨61844305644069426514977911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41229537096046284343318607 61844305644069426514977911)
  ·
    refine ⟨92766458466104139772466867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61844305644069426514977911 92766458466104139772466867)
    ·
      refine ⟨139149687699156209658700301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92766458466104139772466867 139149687699156209658700301)
      ·
        refine ⟨52181132887183578622012613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139149687699156209658700301 52181132887183578622012613)
        ·
          refine ⟨9783962416346920991627365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52181132887183578622012613 9783962416346920991627365)
          ·
            refine ⟨1834492953065047685930131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9783962416346920991627365 1834492953065047685930131)
            ·
              refine ⟨2751739429597571528895197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834492953065047685930131 2751739429597571528895197)
              ·
                refine ⟨1031902286099089323335699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2751739429597571528895197 1031902286099089323335699)
                ·
                  refine ⟨1547853429148633985003549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031902286099089323335699 1547853429148633985003549)
                  ·
                    refine ⟨580445035930737744376331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547853429148633985003549 580445035930737744376331)
                    ·
                      rfl

theorem cell22_1695619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 3].length) (baseStart_1695619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695619 prefixEnd_1695619 := by exact prefixLift 1695619
  have htrace : WordTrace (prefixWord ++ tailWord_1695619) baseStart_1695619 baseEnd_1695619 := by
    simpa [prefixWord, tailWord_1695619, baseEnd_1695619] using wordTrace_append hprefix tailTrace_1695619
  have hstable : (prefixWord ++ tailWord_1695619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695619).length < 2 ^ (prefixWord ++ tailWord_1695619).sum := by decide
  have hdescent : baseEnd_1695619 < baseStart_1695619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695628 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_1695628 : Nat := 118140960795 + 1695628 * 2 ^ 59
def prefixEnd_1695628 : Nat := 4983230072969 + 3 ^ 40 * 1695628 * 2
def baseEnd_1695628 : Nat := 580448116814664720901303

theorem tailTrace_1695628 : CollatzResearch.WordTrace tailWord_1695628 prefixEnd_1695628 580448116814664720901303 := by
  unfold tailWord_1695628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30922316950518410526027769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41229755934024547368037025 30922316950518410526027769)
  ·
    refine ⟨23191737712888807894520827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30922316950518410526027769 23191737712888807894520827)
    ·
      refine ⟨34787606569333211841781241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23191737712888807894520827 34787606569333211841781241)
      ·
        refine ⟨26090704926999908881335931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34787606569333211841781241 26090704926999908881335931)
        ·
          refine ⟨39136057390499863322003897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26090704926999908881335931 39136057390499863322003897)
          ·
            refine ⟨29352043042874897491502923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39136057390499863322003897 29352043042874897491502923)
            ·
              refine ⟨44028064564312346237254385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29352043042874897491502923 44028064564312346237254385)
              ·
                refine ⟨33021048423234259677940789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44028064564312346237254385 33021048423234259677940789)
                ·
                  refine ⟨3095723289678211844806949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33021048423234259677940789 3095723289678211844806949)
                  ·
                    refine ⟨580448116814664720901303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3095723289678211844806949 580448116814664720901303)
                    ·
                      rfl

theorem cell22_1695628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_1695628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695628 prefixEnd_1695628 := by exact prefixLift 1695628
  have htrace : WordTrace (prefixWord ++ tailWord_1695628) baseStart_1695628 baseEnd_1695628 := by
    simpa [prefixWord, tailWord_1695628, baseEnd_1695628] using wordTrace_append hprefix tailTrace_1695628
  have hstable : (prefixWord ++ tailWord_1695628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695628).length < 2 ^ (prefixWord ++ tailWord_1695628).sum := by decide
  have hdescent : baseEnd_1695628 < baseStart_1695628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695636 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1695636 : Nat := 118140960795 + 1695636 * 2 ^ 59
def prefixEnd_1695636 : Nat := 4983230072969 + 3 ^ 40 * 1695636 * 2
def baseEnd_1695636 : Nat := 580450855378155366701279

theorem tailTrace_1695636 : CollatzResearch.WordTrace tailWord_1695636 prefixEnd_1695636 580450855378155366701279 := by
  unfold tailWord_1695636
  simp only [CollatzResearch.WordTrace]
  refine ⟨30922462842503919209173381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41229950456671892278897841 30922462842503919209173381)
  ·
    refine ⟨5797961782969484851720009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30922462842503919209173381 5797961782969484851720009)
    ·
      refine ⟨4348471337227113638790007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5797961782969484851720009 4348471337227113638790007)
      ·
        refine ⟨6522707005840670458185011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348471337227113638790007 6522707005840670458185011)
        ·
          refine ⟨9784060508761005687277517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522707005840670458185011 9784060508761005687277517)
          ·
            refine ⟨3669022690785377132729069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9784060508761005687277517 3669022690785377132729069)
            ·
              refine ⟨1375883509044516424773401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3669022690785377132729069 1375883509044516424773401)
              ·
                refine ⟨1031912631783387318580051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375883509044516424773401 1031912631783387318580051)
                ·
                  refine ⟨1547868947675080977870077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031912631783387318580051 1547868947675080977870077)
                  ·
                    refine ⟨580450855378155366701279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547868947675080977870077 580450855378155366701279)
                    ·
                      rfl

theorem cell22_1695636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1695636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695636 prefixEnd_1695636 := by exact prefixLift 1695636
  have htrace : WordTrace (prefixWord ++ tailWord_1695636) baseStart_1695636 baseEnd_1695636 := by
    simpa [prefixWord, tailWord_1695636, baseEnd_1695636] using wordTrace_append hprefix tailTrace_1695636
  have hstable : (prefixWord ++ tailWord_1695636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695636).length < 2 ^ (prefixWord ++ tailWord_1695636).sum := by decide
  have hdescent : baseEnd_1695636 < baseStart_1695636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695649 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 5]
def baseStart_1695649 : Nat := 118140960795 + 1695649 * 2 ^ 59
def prefixEnd_1695649 : Nat := 4983230072969 + 3 ^ 40 * 1695649 * 2
def baseEnd_1695649 : Nat := 193485101847942555375413

theorem tailTrace_1695649 : CollatzResearch.WordTrace tailWord_1695649 prefixEnd_1695649 193485101847942555375413 := by
  unfold tailWord_1695649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61845399833960741638570001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41230266555973827759046667 61845399833960741638570001)
  ·
    refine ⟨46384049875470556228927501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61845399833960741638570001 46384049875470556228927501)
    ·
      refine ⟨17394018703301458585847813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46384049875470556228927501 17394018703301458585847813)
      ·
        refine ⟨3261378506869023484846465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17394018703301458585847813 3261378506869023484846465)
        ·
          refine ⟨2446033880151767613634849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3261378506869023484846465 2446033880151767613634849)
          ·
            refine ⟨1834525410113825710226137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446033880151767613634849 1834525410113825710226137)
            ·
              refine ⟨1375894057585369282669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834525410113825710226137 1375894057585369282669603)
              ·
                refine ⟨2063841086378053924004405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375894057585369282669603 2063841086378053924004405)
                ·
                  refine ⟨193485101847942555375413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2063841086378053924004405 193485101847942555375413)
                  ·
                    rfl

theorem cell22_1695649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_1695649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695649 prefixEnd_1695649 := by exact prefixLift 1695649
  have htrace : WordTrace (prefixWord ++ tailWord_1695649) baseStart_1695649 baseEnd_1695649 := by
    simpa [prefixWord, tailWord_1695649, baseEnd_1695649] using wordTrace_append hprefix tailTrace_1695649
  have hstable : (prefixWord ++ tailWord_1695649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695649).length < 2 ^ (prefixWord ++ tailWord_1695649).sum := by decide
  have hdescent : baseEnd_1695649 < baseStart_1695649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695688 : List Nat := [2, 1, 3, 1, 4, 11]
def baseStart_1695688 : Nat := 118140960795 + 1695688 * 2 ^ 59
def prefixEnd_1695688 : Nat := 4983230072969 + 3 ^ 40 * 1695688 * 2
def baseEnd_1695688 : Nat := 7166279704207957585199

theorem tailTrace_1695688 : CollatzResearch.WordTrace tailWord_1695688 prefixEnd_1695688 7166279704207957585199 := by
  unfold tailWord_1695688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30923411140409725649619859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41231214853879634199493145 30923411140409725649619859)
  ·
    refine ⟨46385116710614588474429789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30923411140409725649619859 46385116710614588474429789)
    ·
      refine ⟨17394418766480470677911171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46385116710614588474429789 17394418766480470677911171)
      ·
        refine ⟨26091628149720706016866757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17394418766480470677911171 26091628149720706016866757)
        ·
          refine ⟨4892180278072632378162517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26091628149720706016866757 4892180278072632378162517)
          ·
            refine ⟨7166279704207957585199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4892180278072632378162517 7166279704207957585199)
            ·
              rfl

theorem cell22_1695688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 11].length) (baseStart_1695688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695688 prefixEnd_1695688 := by exact prefixLift 1695688
  have htrace : WordTrace (prefixWord ++ tailWord_1695688) baseStart_1695688 baseEnd_1695688 := by
    simpa [prefixWord, tailWord_1695688, baseEnd_1695688] using wordTrace_append hprefix tailTrace_1695688
  have hstable : (prefixWord ++ tailWord_1695688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695688).length < 2 ^ (prefixWord ++ tailWord_1695688).sum := by decide
  have hdescent : baseEnd_1695688 < baseStart_1695688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695690 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1695690 : Nat := 118140960795 + 1695690 * 2 ^ 59
def prefixEnd_1695690 : Nat := 4983230072969 + 3 ^ 40 * 1695690 * 2
def baseEnd_1695690 : Nat := 580469340681717225851113

theorem tailTrace_1695690 : CollatzResearch.WordTrace tailWord_1695690 prefixEnd_1695690 580469340681717225851113 := by
  unfold tailWord_1695690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461723806703051410203131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41231263484541470427208349 15461723806703051410203131)
  ·
    refine ⟨23192585710054577115304697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15461723806703051410203131 23192585710054577115304697)
    ·
      refine ⟨17394439282540932836478523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23192585710054577115304697 17394439282540932836478523)
      ·
        refine ⟨26091658923811399254717785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17394439282540932836478523 26091658923811399254717785)
        ·
          refine ⟨19568744192858549441038339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26091658923811399254717785 19568744192858549441038339)
          ·
            refine ⟨29353116289287824161557509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19568744192858549441038339 29353116289287824161557509)
            ·
              refine ⟨5503709304241467030292033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29353116289287824161557509 5503709304241467030292033)
              ·
                refine ⟨4127781978181100272719025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503709304241467030292033 4127781978181100272719025)
                ·
                  refine ⟨3095836483635825204539269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127781978181100272719025 3095836483635825204539269)
                  ·
                    refine ⟨580469340681717225851113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3095836483635825204539269 580469340681717225851113)
                    ·
                      rfl

theorem cell22_1695690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1695690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695690 prefixEnd_1695690 := by exact prefixLift 1695690
  have htrace : WordTrace (prefixWord ++ tailWord_1695690) baseStart_1695690 baseEnd_1695690 := by
    simpa [prefixWord, tailWord_1695690, baseEnd_1695690] using wordTrace_append hprefix tailTrace_1695690
  have hstable : (prefixWord ++ tailWord_1695690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695690).length < 2 ^ (prefixWord ++ tailWord_1695690).sum := by decide
  have hdescent : baseEnd_1695690 < baseStart_1695690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695692 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_1695692 : Nat := 118140960795 + 1695692 * 2 ^ 59
def prefixEnd_1695692 : Nat := 4983230072969 + 3 ^ 40 * 1695692 * 2
def baseEnd_1695692 : Nat := 580470025322589887301107

theorem tailTrace_1695692 : CollatzResearch.WordTrace tailWord_1695692 prefixEnd_1695692 580470025322589887301107 := by
  unfold tailWord_1695692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30923484086402479991192665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41231312115203306654923553 30923484086402479991192665)
  ·
    refine ⟨23192613064801859993394499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30923484086402479991192665 23192613064801859993394499)
    ·
      refine ⟨34788919597202789990091749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23192613064801859993394499 34788919597202789990091749)
      ·
        refine ⟨6522922424475523123142203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34788919597202789990091749 6522922424475523123142203)
        ·
          refine ⟨9784383636713284684713305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522922424475523123142203 9784383636713284684713305)
          ·
            refine ⟨7338287727534963513534979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9784383636713284684713305 7338287727534963513534979)
            ·
              refine ⟨11007431591302445270302469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7338287727534963513534979 11007431591302445270302469)
              ·
                refine ⟨2063893423369208488181713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11007431591302445270302469 2063893423369208488181713)
                ·
                  refine ⟨1547920067526906366136285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2063893423369208488181713 1547920067526906366136285)
                  ·
                    refine ⟨580470025322589887301107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547920067526906366136285 580470025322589887301107)
                    ·
                      rfl

theorem cell22_1695692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_1695692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695692 prefixEnd_1695692 := by exact prefixLift 1695692
  have htrace : WordTrace (prefixWord ++ tailWord_1695692) baseStart_1695692 baseEnd_1695692 := by
    simpa [prefixWord, tailWord_1695692, baseEnd_1695692] using wordTrace_append hprefix tailTrace_1695692
  have hstable : (prefixWord ++ tailWord_1695692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695692).length < 2 ^ (prefixWord ++ tailWord_1695692).sum := by decide
  have hdescent : baseEnd_1695692 < baseStart_1695692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695754 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1695754 : Nat := 118140960795 + 1695754 * 2 ^ 59
def prefixEnd_1695754 : Nat := 4983230072969 + 3 ^ 40 * 1695754 * 2
def baseEnd_1695754 : Nat := 580491249189642392250917

theorem tailTrace_1695754 : CollatzResearch.WordTrace tailWord_1695754 prefixEnd_1695754 580491249189642392250917 := by
  unfold tailWord_1695754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15462307374645086142785579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41232819665720229714094877 15462307374645086142785579)
  ·
    refine ⟨23193461061967629214178369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15462307374645086142785579 23193461061967629214178369)
    ·
      refine ⟨17395095796475721910633777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23193461061967629214178369 17395095796475721910633777)
      ·
        refine ⟨13046321847356791432975333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17395095796475721910633777 13046321847356791432975333)
        ·
          refine ⟨2446185346379398393682875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13046321847356791432975333 2446185346379398393682875)
          ·
            refine ⟨3669278019569097590524313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446185346379398393682875 3669278019569097590524313)
            ·
              refine ⟨2751958514676823192893235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669278019569097590524313 2751958514676823192893235)
              ·
                refine ⟨4127937772015234789339853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751958514676823192893235 4127937772015234789339853)
                ·
                  refine ⟨1547976664505713046002445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4127937772015234789339853 1547976664505713046002445)
                  ·
                    refine ⟨580491249189642392250917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1547976664505713046002445 580491249189642392250917)
                    ·
                      rfl

theorem cell22_1695754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1695754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695754 prefixEnd_1695754 := by exact prefixLift 1695754
  have htrace : WordTrace (prefixWord ++ tailWord_1695754) baseStart_1695754 baseEnd_1695754 := by
    simpa [prefixWord, tailWord_1695754, baseEnd_1695754] using wordTrace_append hprefix tailTrace_1695754
  have hstable : (prefixWord ++ tailWord_1695754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695754).length < 2 ^ (prefixWord ++ tailWord_1695754).sum := by decide
  have hdescent : baseEnd_1695754 < baseStart_1695754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695797 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1695797 : Nat := 118140960795 + 1695797 * 2 ^ 59
def prefixEnd_1695797 : Nat := 4983230072969 + 3 ^ 40 * 1695797 * 2
def baseEnd_1695797 : Nat := 580505968968404613425785

theorem tailTrace_1695797 : CollatzResearch.WordTrace tailWord_1695797 prefixEnd_1695797 580505968968404613425785 := by
  unfold tailWord_1695797
  simp only [CollatzResearch.WordTrace]
  refine ⟨61850797837424562914957645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41233865224949708609971763 61850797837424562914957645)
  ·
    refine ⟨23194049189034211093109117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61850797837424562914957645 23194049189034211093109117)
    ·
      refine ⟨8697768445887829159915919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23194049189034211093109117 8697768445887829159915919)
      ·
        refine ⟨13046652668831743739873879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8697768445887829159915919 13046652668831743739873879)
        ·
          refine ⟨19569979003247615609810819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13046652668831743739873879 19569979003247615609810819)
          ·
            refine ⟨29354968504871423414716229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19569979003247615609810819 29354968504871423414716229)
            ·
              refine ⟨5504056594663391890259293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29354968504871423414716229 5504056594663391890259293)
              ·
                refine ⟨2064021222998771958847235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5504056594663391890259293 2064021222998771958847235)
                ·
                  refine ⟨3096031834498157938270853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064021222998771958847235 3096031834498157938270853)
                  ·
                    refine ⟨580505968968404613425785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096031834498157938270853 580505968968404613425785)
                    ·
                      rfl

theorem cell22_1695797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1695797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695797 prefixEnd_1695797 := by exact prefixLift 1695797
  have htrace : WordTrace (prefixWord ++ tailWord_1695797) baseStart_1695797 baseEnd_1695797 := by
    simpa [prefixWord, tailWord_1695797, baseEnd_1695797] using wordTrace_append hprefix tailTrace_1695797
  have hstable : (prefixWord ++ tailWord_1695797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695797).length < 2 ^ (prefixWord ++ tailWord_1695797).sum := by decide
  have hdescent : baseEnd_1695797 < baseStart_1695797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695814 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1695814 : Nat := 118140960795 + 1695814 * 2 ^ 59
def prefixEnd_1695814 : Nat := 4983230072969 + 3 ^ 40 * 1695814 * 2
def baseEnd_1695814 : Nat := 580511788415822235750733

theorem tailTrace_1695814 : CollatzResearch.WordTrace tailWord_1695814 prefixEnd_1695814 580511788415822235750733 := by
  unfold tailWord_1695814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932856808698842963072703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41234278585575316545550997 1932856808698842963072703)
  ·
    refine ⟨2899285213048264444609055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932856808698842963072703 2899285213048264444609055)
    ·
      refine ⟨4348927819572396666913583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2899285213048264444609055 4348927819572396666913583)
      ·
        refine ⟨6523391729358595000370375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348927819572396666913583 6523391729358595000370375)
        ·
          refine ⟨9785087594037892500555563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6523391729358595000370375 9785087594037892500555563)
          ·
            refine ⟨14677631391056838750833345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785087594037892500555563 14677631391056838750833345)
            ·
              refine ⟨11008223543292629063125009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14677631391056838750833345 11008223543292629063125009)
              ·
                refine ⟨8256167657469471797343757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11008223543292629063125009 8256167657469471797343757)
                ·
                  refine ⟨3096062871551051924003909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8256167657469471797343757 3096062871551051924003909)
                  ·
                    refine ⟨580511788415822235750733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096062871551051924003909 580511788415822235750733)
                    ·
                      rfl

theorem cell22_1695814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1695814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695814 prefixEnd_1695814 := by exact prefixLift 1695814
  have htrace : WordTrace (prefixWord ++ tailWord_1695814) baseStart_1695814 baseEnd_1695814 := by
    simpa [prefixWord, tailWord_1695814, baseEnd_1695814] using wordTrace_append hprefix tailTrace_1695814
  have hstable : (prefixWord ++ tailWord_1695814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695814).length < 2 ^ (prefixWord ++ tailWord_1695814).sum := by decide
  have hdescent : baseEnd_1695814 < baseStart_1695814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695825 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1695825 : Nat := 118140960795 + 1695825 * 2 ^ 59
def prefixEnd_1695825 : Nat := 4983230072969 + 3 ^ 40 * 1695825 * 2
def baseEnd_1695825 : Nat := 580515553940621873725699

theorem tailTrace_1695825 : CollatzResearch.WordTrace tailWord_1695825 prefixEnd_1695825 580515553940621873725699 := by
  unfold tailWord_1695825
  simp only [CollatzResearch.WordTrace]
  refine ⟨61851819081323123696976929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41234546054215415797984619 61851819081323123696976929)
  ·
    refine ⟨46388864310992342772732697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61851819081323123696976929 46388864310992342772732697)
    ·
      refine ⟨34791648233244257079549523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46388864310992342772732697 34791648233244257079549523)
      ·
        refine ⟨52187472349866385619324285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34791648233244257079549523 52187472349866385619324285)
        ·
          refine ⟨19570302131199894607246607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52187472349866385619324285 19570302131199894607246607)
          ·
            refine ⟨29355453196799841910869911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19570302131199894607246607 29355453196799841910869911)
            ·
              refine ⟨44033179795199762866304867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29355453196799841910869911 44033179795199762866304867)
              ·
                refine ⟨66049769692799644299457301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44033179795199762866304867 66049769692799644299457301)
                ·
                  refine ⟨3096082954349983326537061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66049769692799644299457301 3096082954349983326537061)
                  ·
                    refine ⟨580515553940621873725699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096082954349983326537061 580515553940621873725699)
                    ·
                      rfl

theorem cell22_1695825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1695825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695825 prefixEnd_1695825 := by exact prefixLift 1695825
  have htrace : WordTrace (prefixWord ++ tailWord_1695825) baseStart_1695825 baseEnd_1695825 := by
    simpa [prefixWord, tailWord_1695825, baseEnd_1695825] using wordTrace_append hprefix tailTrace_1695825
  have hstable : (prefixWord ++ tailWord_1695825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695825).length < 2 ^ (prefixWord ++ tailWord_1695825).sum := by decide
  have hdescent : baseEnd_1695825 < baseStart_1695825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695840 : List Nat := [2, 1, 1, 3, 2, 3, 2, 8]
def baseStart_1695840 : Nat := 118140960795 + 1695840 * 2 ^ 59
def prefixEnd_1695840 : Nat := 4983230072969 + 3 ^ 40 * 1695840 * 2
def baseEnd_1695840 : Nat := 64502298749685203844517

theorem tailTrace_1695840 : CollatzResearch.WordTrace tailWord_1695840 prefixEnd_1695840 64502298749685203844517 := by
  unfold tailWord_1695840
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926183088134390629386487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41234910784179187505848649 30926183088134390629386487)
  ·
    refine ⟨46389274632201585944079731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30926183088134390629386487 46389274632201585944079731)
    ·
      refine ⟨69583911948302378916119597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46389274632201585944079731 69583911948302378916119597)
      ·
        refine ⟨26093966980613392093544849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69583911948302378916119597 26093966980613392093544849)
        ·
          refine ⟨19570475235460044070158637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26093966980613392093544849 19570475235460044070158637)
          ·
            refine ⟨7338928213297516526309489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19570475235460044070158637 7338928213297516526309489)
            ·
              refine ⟨5504196159973137394732117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7338928213297516526309489 5504196159973137394732117)
              ·
                refine ⟨64502298749685203844517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5504196159973137394732117 64502298749685203844517)
                ·
                  rfl

theorem cell22_1695840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_1695840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695840 prefixEnd_1695840 := by exact prefixLift 1695840
  have htrace : WordTrace (prefixWord ++ tailWord_1695840) baseStart_1695840 baseEnd_1695840 := by
    simpa [prefixWord, tailWord_1695840, baseEnd_1695840] using wordTrace_append hprefix tailTrace_1695840
  have hstable : (prefixWord ++ tailWord_1695840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695840).length < 2 ^ (prefixWord ++ tailWord_1695840).sum := by decide
  have hdescent : baseEnd_1695840 < baseStart_1695840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695872 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_1695872 : Nat := 118140960795 + 1695872 * 2 ^ 59
def prefixEnd_1695872 : Nat := 4983230072969 + 3 ^ 40 * 1695872 * 2
def baseEnd_1695872 : Nat := 580531643001129417800555

theorem tailTrace_1695872 : CollatzResearch.WordTrace tailWord_1695872 prefixEnd_1695872 580531643001129417800555 := by
  unfold tailWord_1695872
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926766656076425361968935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41235688874768567149291913 30926766656076425361968935)
  ·
    refine ⟨46390149984114638042953403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30926766656076425361968935 46390149984114638042953403)
    ·
      refine ⟨69585224976171957064430105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46390149984114638042953403 69585224976171957064430105)
      ·
        refine ⟨52188918732128967798322579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69585224976171957064430105 52188918732128967798322579)
        ·
          refine ⟨78283378098193451697483869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52188918732128967798322579 78283378098193451697483869)
          ·
            refine ⟨29356266786822544386556451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78283378098193451697483869 29356266786822544386556451)
            ·
              refine ⟨44034400180233816579834677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29356266786822544386556451 44034400180233816579834677)
              ·
                refine ⟨4128225016896920304359501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44034400180233816579834677 4128225016896920304359501)
                ·
                  refine ⟨1548084381336345114134813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4128225016896920304359501 1548084381336345114134813)
                  ·
                    refine ⟨580531643001129417800555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548084381336345114134813 580531643001129417800555)
                    ·
                      rfl

theorem cell22_1695872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_1695872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695872 prefixEnd_1695872 := by exact prefixLift 1695872
  have htrace : WordTrace (prefixWord ++ tailWord_1695872) baseStart_1695872 baseEnd_1695872 := by
    simpa [prefixWord, tailWord_1695872, baseEnd_1695872] using wordTrace_append hprefix tailTrace_1695872
  have hstable : (prefixWord ++ tailWord_1695872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695872).length < 2 ^ (prefixWord ++ tailWord_1695872).sum := by decide
  have hdescent : baseEnd_1695872 < baseStart_1695872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695962 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1695962 : Nat := 118140960795 + 1695962 * 2 ^ 59
def prefixEnd_1695962 : Nat := 4983230072969 + 3 ^ 40 * 1695962 * 2
def baseEnd_1695962 : Nat := 580562451840399183050279

theorem tailTrace_1695962 : CollatzResearch.WordTrace tailWord_1695962 prefixEnd_1695962 580562451840399183050279 := by
  unfold tailWord_1695962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464203970456699023678535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41237877254551197396476093 15464203970456699023678535)
  ·
    refine ⟨23196305955685048535517803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15464203970456699023678535 23196305955685048535517803)
    ·
      refine ⟨34794458933527572803276705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23196305955685048535517803 34794458933527572803276705)
      ·
        refine ⟨26095844200145679602457529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34794458933527572803276705 26095844200145679602457529)
        ·
          refine ⟨19571883150109259701843147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26095844200145679602457529 19571883150109259701843147)
          ·
            refine ⟨29357824725163889552764721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19571883150109259701843147 29357824725163889552764721)
            ·
              refine ⟨22018368543872917164573541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29357824725163889552764721 22018368543872917164573541)
              ·
                refine ⟨4128444101976171968357539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22018368543872917164573541 4128444101976171968357539)
                ·
                  refine ⟨6192666152964257952536309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128444101976171968357539 6192666152964257952536309)
                  ·
                    refine ⟨580562451840399183050279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6192666152964257952536309 580562451840399183050279)
                    ·
                      rfl

theorem cell22_1695962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1695962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695962 prefixEnd_1695962 := by exact prefixLift 1695962
  have htrace : WordTrace (prefixWord ++ tailWord_1695962) baseStart_1695962 baseEnd_1695962 := by
    simpa [prefixWord, tailWord_1695962, baseEnd_1695962] using wordTrace_append hprefix tailTrace_1695962
  have hstable : (prefixWord ++ tailWord_1695962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695962).length < 2 ^ (prefixWord ++ tailWord_1695962).sum := by decide
  have hdescent : baseEnd_1695962 < baseStart_1695962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695977 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_1695977 : Nat := 118140960795 + 1695977 * 2 ^ 59
def prefixEnd_1695977 : Nat := 4983230072969 + 3 ^ 40 * 1695977 * 2
def baseEnd_1695977 : Nat := 580567586646944143925233

theorem tailTrace_1695977 : CollatzResearch.WordTrace tailWord_1695977 prefixEnd_1695977 580567586646944143925233 := by
  unfold tailWord_1695977
  simp only [CollatzResearch.WordTrace]
  refine ⟨61857362976772453656510185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41238241984514969104340123 61857362976772453656510185)
  ·
    refine ⟨46393022232579340242382639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61857362976772453656510185 46393022232579340242382639)
    ·
      refine ⟨69589533348869010363573959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46393022232579340242382639 69589533348869010363573959)
      ·
        refine ⟨104384300023303515545360939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69589533348869010363573959 104384300023303515545360939)
        ·
          refine ⟨156576450034955273318041409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104384300023303515545360939 156576450034955273318041409)
          ·
            refine ⟨117432337526216454988531057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156576450034955273318041409 117432337526216454988531057)
            ·
              refine ⟨88074253144662341241398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117432337526216454988531057 88074253144662341241398293)
              ·
                refine ⟨4128480616156047245690545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88074253144662341241398293 4128480616156047245690545)
                ·
                  refine ⟨3096360462117035434267909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128480616156047245690545 3096360462117035434267909)
                  ·
                    refine ⟨580567586646944143925233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096360462117035434267909 580567586646944143925233)
                    ·
                      rfl

theorem cell22_1695977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_1695977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695977 prefixEnd_1695977 := by exact prefixLift 1695977
  have htrace : WordTrace (prefixWord ++ tailWord_1695977) baseStart_1695977 baseEnd_1695977 := by
    simpa [prefixWord, tailWord_1695977, baseEnd_1695977] using wordTrace_append hprefix tailTrace_1695977
  have hstable : (prefixWord ++ tailWord_1695977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695977).length < 2 ^ (prefixWord ++ tailWord_1695977).sum := by decide
  have hdescent : baseEnd_1695977 < baseStart_1695977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695979 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 2, 3]
def baseStart_1695979 : Nat := 118140960795 + 1695979 * 2 ^ 59
def prefixEnd_1695979 : Nat := 4983230072969 + 3 ^ 40 * 1695979 * 2
def baseEnd_1695979 : Nat := 580568271287816805375227

theorem tailTrace_1695979 : CollatzResearch.WordTrace tailWord_1695979 prefixEnd_1695979 580568271287816805375227 := by
  unfold tailWord_1695979
  simp only [CollatzResearch.WordTrace]
  refine ⟨61857435922765207998082991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41238290615176805332055327 61857435922765207998082991)
  ·
    refine ⟨92786153884147811997124487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61857435922765207998082991 92786153884147811997124487)
    ·
      refine ⟨139179230826221717995686731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92786153884147811997124487 139179230826221717995686731)
      ·
        refine ⟨208768846239332576993530097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139179230826221717995686731 208768846239332576993530097)
        ·
          refine ⟨156576634679499432745147573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208768846239332576993530097 156576634679499432745147573)
          ·
            refine ⟨14679059501203071819857585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156576634679499432745147573 14679059501203071819857585)
            ·
              refine ⟨11009294625902303864893189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14679059501203071819857585 11009294625902303864893189)
              ·
                refine ⟨2064242742356681974667473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11009294625902303864893189 2064242742356681974667473)
                ·
                  refine ⟨1548182056767511481000605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064242742356681974667473 1548182056767511481000605)
                  ·
                    refine ⟨580568271287816805375227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548182056767511481000605 580568271287816805375227)
                    ·
                      rfl

theorem cell22_1695979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 3].length) (baseStart_1695979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695979 prefixEnd_1695979 := by exact prefixLift 1695979
  have htrace : WordTrace (prefixWord ++ tailWord_1695979) baseStart_1695979 baseEnd_1695979 := by
    simpa [prefixWord, tailWord_1695979, baseEnd_1695979] using wordTrace_append hprefix tailTrace_1695979
  have hstable : (prefixWord ++ tailWord_1695979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695979).length < 2 ^ (prefixWord ++ tailWord_1695979).sum := by decide
  have hdescent : baseEnd_1695979 < baseStart_1695979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695981 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1695981 : Nat := 118140960795 + 1695981 * 2 ^ 59
def prefixEnd_1695981 : Nat := 4983230072969 + 3 ^ 40 * 1695981 * 2
def baseEnd_1695981 : Nat := 193522985309563155608407

theorem tailTrace_1695981 : CollatzResearch.WordTrace tailWord_1695981 prefixEnd_1695981 193522985309563155608407 := by
  unfold tailWord_1695981
  simp only [CollatzResearch.WordTrace]
  refine ⟨61857508868757962339655797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41238339245838641559770531 61857508868757962339655797)
  ·
    refine ⟨5799141456446058969342731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61857508868757962339655797 5799141456446058969342731)
    ·
      refine ⟨8698712184669088454014097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799141456446058969342731 8698712184669088454014097)
      ·
        refine ⟨6524034138501816340510573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8698712184669088454014097 6524034138501816340510573)
        ·
          refine ⟨2446512801938181127691465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6524034138501816340510573 2446512801938181127691465)
          ·
            refine ⟨1834884601453635845768599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446512801938181127691465 1834884601453635845768599)
            ·
              refine ⟨2752326902180453768652899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834884601453635845768599 2752326902180453768652899)
              ·
                refine ⟨4128490353270680652979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752326902180453768652899 4128490353270680652979349)
                ·
                  refine ⟨193522985309563155608407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4128490353270680652979349 193522985309563155608407)
                  ·
                    rfl

theorem cell22_1695981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1695981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695981 prefixEnd_1695981 := by exact prefixLift 1695981
  have htrace : WordTrace (prefixWord ++ tailWord_1695981) baseStart_1695981 baseEnd_1695981 := by
    simpa [prefixWord, tailWord_1695981, baseEnd_1695981] using wordTrace_append hprefix tailTrace_1695981
  have hstable : (prefixWord ++ tailWord_1695981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695981).length < 2 ^ (prefixWord ++ tailWord_1695981).sum := by decide
  have hdescent : baseEnd_1695981 < baseStart_1695981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695996 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1695996 : Nat := 118140960795 + 1695996 * 2 ^ 59
def prefixEnd_1695996 : Nat := 4983230072969 + 3 ^ 40 * 1695996 * 2
def baseEnd_1695996 : Nat := 580574090735234427700175

theorem tailTrace_1695996 : CollatzResearch.WordTrace tailWord_1695996 prefixEnd_1695996 580574090735234427700175 := by
  unfold tailWord_1695996
  simp only [CollatzResearch.WordTrace]
  refine ⟨30929027981851809950725921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41238703975802413267634561 30929027981851809950725921)
  ·
    refine ⟨23196770986388857463044441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30929027981851809950725921 23196770986388857463044441)
    ·
      refine ⟨17397578239791643097283331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23196770986388857463044441 17397578239791643097283331)
      ·
        refine ⟨26096367359687464645924997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17397578239791643097283331 26096367359687464645924997)
        ·
          refine ⟨4893068879941399621110937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26096367359687464645924997 4893068879941399621110937)
          ·
            refine ⟨3669801659956049715833203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4893068879941399621110937 3669801659956049715833203)
            ·
              refine ⟨5504702489934074573749805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669801659956049715833203 5504702489934074573749805)
              ·
                refine ⟨2064263433725277965156177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5504702489934074573749805 2064263433725277965156177)
                ·
                  refine ⟨1548197575293958473867133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064263433725277965156177 1548197575293958473867133)
                  ·
                    refine ⟨580574090735234427700175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548197575293958473867133 580574090735234427700175)
                    ·
                      rfl

theorem cell22_1695996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1695996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1695996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1695996 prefixEnd_1695996 := by exact prefixLift 1695996
  have htrace : WordTrace (prefixWord ++ tailWord_1695996) baseStart_1695996 baseEnd_1695996 := by
    simpa [prefixWord, tailWord_1695996, baseEnd_1695996] using wordTrace_append hprefix tailTrace_1695996
  have hstable : (prefixWord ++ tailWord_1695996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695996).length < 2 ^ (prefixWord ++ tailWord_1695996).sum := by decide
  have hdescent : baseEnd_1695996 < baseStart_1695996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696030 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1696030 : Nat := 118140960795 + 1696030 * 2 ^ 59
def prefixEnd_1696030 : Nat := 4983230072969 + 3 ^ 40 * 1696030 * 2
def baseEnd_1696030 : Nat := 580585729630069672350071

theorem tailTrace_1696030 : CollatzResearch.WordTrace tailWord_1696030 prefixEnd_1696030 580585729630069672350071 := by
  unfold tailWord_1696030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732412005697555463523693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41239530697053629138793029 7732412005697555463523693)
  ·
    refine ⟨2899654502136583298821385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7732412005697555463523693 2899654502136583298821385)
    ·
      refine ⟨2174740876602437474116039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2899654502136583298821385 2174740876602437474116039)
      ·
        refine ⟨3262111314903656211174059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174740876602437474116039 3262111314903656211174059)
        ·
          refine ⟨4893166972355484316761089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262111314903656211174059 4893166972355484316761089)
          ·
            refine ⟨3669875229266613237570817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4893166972355484316761089 3669875229266613237570817)
            ·
              refine ⟨2752406421949959928178113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669875229266613237570817 2752406421949959928178113)
              ·
                refine ⟨2064304816462469946133585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752406421949959928178113 2064304816462469946133585)
                ·
                  refine ⟨1548228612346852459600189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064304816462469946133585 1548228612346852459600189)
                  ·
                    refine ⟨580585729630069672350071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548228612346852459600189 580585729630069672350071)
                    ·
                      rfl

theorem cell22_1696030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1696030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696030 prefixEnd_1696030 := by exact prefixLift 1696030
  have htrace : WordTrace (prefixWord ++ tailWord_1696030) baseStart_1696030 baseEnd_1696030 := by
    simpa [prefixWord, tailWord_1696030, baseEnd_1696030] using wordTrace_append hprefix tailTrace_1696030
  have hstable : (prefixWord ++ tailWord_1696030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696030).length < 2 ^ (prefixWord ++ tailWord_1696030).sum := by decide
  have hdescent : baseEnd_1696030 < baseStart_1696030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696097 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1696097 : Nat := 118140960795 + 1696097 * 2 ^ 59
def prefixEnd_1696097 : Nat := 4983230072969 + 3 ^ 40 * 1696097 * 2
def baseEnd_1696097 : Nat := 580608665099303830924865

theorem tailTrace_1696097 : CollatzResearch.WordTrace tailWord_1696097 prefixEnd_1696097 580608665099303830924865 := by
  unfold tailWord_1696097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61861739736337714150878545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41241159824225142767252363 61861739736337714150878545)
  ·
    refine ⟨46396304802253285613158909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61861739736337714150878545 46396304802253285613158909)
    ·
      refine ⟨17398614300844982104934591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46396304802253285613158909 17398614300844982104934591)
      ·
        refine ⟨26097921451267473157401887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17398614300844982104934591 26097921451267473157401887)
        ·
          refine ⟨39146882176901209736102831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26097921451267473157401887 39146882176901209736102831)
          ·
            refine ⟨58720323265351814604154247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39146882176901209736102831 58720323265351814604154247)
            ·
              refine ⟨88080484898027721906231371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58720323265351814604154247 88080484898027721906231371)
              ·
                refine ⟨132120727347041582859347057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88080484898027721906231371 132120727347041582859347057)
                ·
                  refine ⟨99090545510281187144510293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132120727347041582859347057 99090545510281187144510293)
                  ·
                    refine ⟨580608665099303830924865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99090545510281187144510293 580608665099303830924865)
                    ·
                      rfl

theorem cell22_1696097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1696097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696097 prefixEnd_1696097 := by exact prefixLift 1696097
  have htrace : WordTrace (prefixWord ++ tailWord_1696097) baseStart_1696097 baseEnd_1696097 := by
    simpa [prefixWord, tailWord_1696097, baseEnd_1696097] using wordTrace_append hprefix tailTrace_1696097
  have hstable : (prefixWord ++ tailWord_1696097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696097).length < 2 ^ (prefixWord ++ tailWord_1696097).sum := by decide
  have hdescent : baseEnd_1696097 < baseStart_1696097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696099 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 6]
def baseStart_1696099 : Nat := 118140960795 + 1696099 * 2 ^ 59
def prefixEnd_1696099 : Nat := 4983230072969 + 3 ^ 40 * 1696099 * 2
def baseEnd_1696099 : Nat := 193536449913392164124953

theorem tailTrace_1696099 : CollatzResearch.WordTrace tailWord_1696099 prefixEnd_1696099 193536449913392164124953 := by
  unfold tailWord_1696099
  simp only [CollatzResearch.WordTrace]
  refine ⟨61861812682330468492451351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41241208454886978994967567 61861812682330468492451351)
  ·
    refine ⟨92792719023495702738677027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61861812682330468492451351 92792719023495702738677027)
    ·
      refine ⟨139189078535243554108015541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92792719023495702738677027 139189078535243554108015541)
      ·
        refine ⟨13048976112679083197626457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139189078535243554108015541 13048976112679083197626457)
        ·
          refine ⟨9786732084509312398219843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13048976112679083197626457 9786732084509312398219843)
          ·
            refine ⟨14680098126763968597329765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9786732084509312398219843 14680098126763968597329765)
            ·
              refine ⟨2752518398768244111999331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14680098126763968597329765 2752518398768244111999331)
              ·
                refine ⟨4128777598152366167998997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752518398768244111999331 4128777598152366167998997)
                ·
                  refine ⟨193536449913392164124953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4128777598152366167998997 193536449913392164124953)
                  ·
                    rfl

theorem cell22_1696099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 6].length) (baseStart_1696099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696099 prefixEnd_1696099 := by exact prefixLift 1696099
  have htrace : WordTrace (prefixWord ++ tailWord_1696099) baseStart_1696099 baseEnd_1696099 := by
    simpa [prefixWord, tailWord_1696099, baseEnd_1696099] using wordTrace_append hprefix tailTrace_1696099
  have hstable : (prefixWord ++ tailWord_1696099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696099).length < 2 ^ (prefixWord ++ tailWord_1696099).sum := by decide
  have hdescent : baseEnd_1696099 < baseStart_1696099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696127 : List Nat := [1, 1, 2, 2, 1, 1, 2, 12]
def baseStart_1696127 : Nat := 118140960795 + 1696127 * 2 ^ 59
def prefixEnd_1696127 : Nat := 4983230072969 + 3 ^ 40 * 1696127 * 2
def baseEnd_1696127 : Nat := 64513214968043750297197

theorem tailTrace_1696127 : CollatzResearch.WordTrace tailWord_1696127 prefixEnd_1696127 64513214968043750297197 := by
  unfold tailWord_1696127
  simp only [CollatzResearch.WordTrace]
  refine ⟨61862833926229029274470635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41241889284152686182980423 61862833926229029274470635)
  ·
    refine ⟨92794250889343543911705953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61862833926229029274470635 92794250889343543911705953)
    ·
      refine ⟨69595688167007657933779465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92794250889343543911705953 69595688167007657933779465)
      ·
        refine ⟨52196766125255743450334599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69595688167007657933779465 52196766125255743450334599)
        ·
          refine ⟨78295149187883615175501899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52196766125255743450334599 78295149187883615175501899)
          ·
            refine ⟨117442723781825422763252849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78295149187883615175501899 117442723781825422763252849)
            ·
              refine ⟨88082042836369067072439637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117442723781825422763252849 88082042836369067072439637)
              ·
                refine ⟨64513214968043750297197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 88082042836369067072439637 64513214968043750297197)
                ·
                  rfl

theorem cell22_1696127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 12].length) (baseStart_1696127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696127 prefixEnd_1696127 := by exact prefixLift 1696127
  have htrace : WordTrace (prefixWord ++ tailWord_1696127) baseStart_1696127 baseEnd_1696127 := by
    simpa [prefixWord, tailWord_1696127, baseEnd_1696127] using wordTrace_append hprefix tailTrace_1696127
  have hstable : (prefixWord ++ tailWord_1696127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696127).length < 2 ^ (prefixWord ++ tailWord_1696127).sum := by decide
  have hdescent : baseEnd_1696127 < baseStart_1696127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696221 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1696221 : Nat := 118140960795 + 1696221 * 2 ^ 59
def prefixEnd_1696221 : Nat := 4983230072969 + 3 ^ 40 * 1696221 * 2
def baseEnd_1696221 : Nat := 580651112833408840824485

theorem tailTrace_1696221 : CollatzResearch.WordTrace tailWord_1696221 prefixEnd_1696221 580651112833408840824485 := by
  unfold tailWord_1696221
  simp only [CollatzResearch.WordTrace]
  refine ⟨61866262387888483328392517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41244174925258988885595011 61866262387888483328392517)
  ·
    refine ⟨11599924197729090624073597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61866262387888483328392517 11599924197729090624073597)
    ·
      refine ⟨4349971574148408984027599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11599924197729090624073597 4349971574148408984027599)
      ·
        refine ⟨6524957361222613476041399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349971574148408984027599 6524957361222613476041399)
        ·
          refine ⟨9787436041833920214062099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524957361222613476041399 9787436041833920214062099)
          ·
            refine ⟨14681154062750880321093149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9787436041833920214062099 14681154062750880321093149)
            ·
              refine ⟨5505432773531580120409931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14681154062750880321093149 5505432773531580120409931)
              ·
                refine ⟨8258149160297370180614897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505432773531580120409931 8258149160297370180614897)
                ·
                  refine ⟨6193611870223027635461173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258149160297370180614897 6193611870223027635461173)
                  ·
                    refine ⟨580651112833408840824485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6193611870223027635461173 580651112833408840824485)
                    ·
                      rfl

theorem cell22_1696221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1696221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696221 prefixEnd_1696221 := by exact prefixLift 1696221
  have htrace : WordTrace (prefixWord ++ tailWord_1696221) baseStart_1696221 baseEnd_1696221 := by
    simpa [prefixWord, tailWord_1696221, baseEnd_1696221] using wordTrace_append hprefix tailTrace_1696221
  have hstable : (prefixWord ++ tailWord_1696221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696221).length < 2 ^ (prefixWord ++ tailWord_1696221).sum := by decide
  have hdescent : baseEnd_1696221 < baseStart_1696221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696236 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_1696236 : Nat := 118140960795 + 1696236 * 2 ^ 59
def prefixEnd_1696236 : Nat := 4983230072969 + 3 ^ 40 * 1696236 * 2
def baseEnd_1696236 : Nat := 580656247639953801699439

theorem tailTrace_1696236 : CollatzResearch.WordTrace tailWord_1696236 prefixEnd_1696236 580656247639953801699439 := by
  unfold tailWord_1696236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30933404741417070445094281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41244539655222760593459041 30933404741417070445094281)
  ·
    refine ⟨23200053556062802833820711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30933404741417070445094281 23200053556062802833820711)
    ·
      refine ⟨34800080334094204250731067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23200053556062802833820711 34800080334094204250731067)
      ·
        refine ⟨52200120501141306376096601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34800080334094204250731067 52200120501141306376096601)
        ·
          refine ⟨39150090375855979782072451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52200120501141306376096601 39150090375855979782072451)
          ·
            refine ⟨58725135563783969673108677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39150090375855979782072451 58725135563783969673108677)
            ·
              refine ⟨11010962918209494313707877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58725135563783969673108677 11010962918209494313707877)
              ·
                refine ⟨2064555547164280183820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11010962918209494313707877 2064555547164280183820227)
                ·
                  refine ⟨3096833320746420275730341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064555547164280183820227 3096833320746420275730341)
                  ·
                    refine ⟨580656247639953801699439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096833320746420275730341 580656247639953801699439)
                    ·
                      rfl

theorem cell22_1696236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_1696236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696236 prefixEnd_1696236 := by exact prefixLift 1696236
  have htrace : WordTrace (prefixWord ++ tailWord_1696236) baseStart_1696236 baseEnd_1696236 := by
    simpa [prefixWord, tailWord_1696236, baseEnd_1696236] using wordTrace_append hprefix tailTrace_1696236
  have hstable : (prefixWord ++ tailWord_1696236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696236).length < 2 ^ (prefixWord ++ tailWord_1696236).sum := by decide
  have hdescent : baseEnd_1696236 < baseStart_1696236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696268 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_1696268 : Nat := 118140960795 + 1696268 * 2 ^ 59
def prefixEnd_1696268 : Nat := 4983230072969 + 3 ^ 40 * 1696268 * 2
def baseEnd_1696268 : Nat := 193555733964638794966447

theorem tailTrace_1696268 : CollatzResearch.WordTrace tailWord_1696268 prefixEnd_1696268 193555733964638794966447 := by
  unfold tailWord_1696268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30933988309359105177676729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41245317745812140236902305 30933988309359105177676729)
  ·
    refine ⟨23200491232019328883257547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30933988309359105177676729 23200491232019328883257547)
    ·
      refine ⟨34800736848028993324886321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23200491232019328883257547 34800736848028993324886321)
      ·
        refine ⟨26100552636021744993664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34800736848028993324886321 26100552636021744993664741)
        ·
          refine ⟨4893853619254077186312139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26100552636021744993664741 4893853619254077186312139)
          ·
            refine ⟨7340780428881115779468209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893853619254077186312139 7340780428881115779468209)
            ·
              refine ⟨5505585321660836834601157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340780428881115779468209 5505585321660836834601157)
              ·
                refine ⟨1032297247811406906487717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5505585321660836834601157 1032297247811406906487717)
                ·
                  refine ⟨193555733964638794966447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032297247811406906487717 193555733964638794966447)
                  ·
                    rfl

theorem cell22_1696268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_1696268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696268 prefixEnd_1696268 := by exact prefixLift 1696268
  have htrace : WordTrace (prefixWord ++ tailWord_1696268) baseStart_1696268 baseEnd_1696268 := by
    simpa [prefixWord, tailWord_1696268, baseEnd_1696268] using wordTrace_append hprefix tailTrace_1696268
  have hstable : (prefixWord ++ tailWord_1696268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696268).length < 2 ^ (prefixWord ++ tailWord_1696268).sum := by decide
  have hdescent : baseEnd_1696268 < baseStart_1696268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696302 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_1696302 : Nat := 118140960795 + 1696302 * 2 ^ 59
def prefixEnd_1696302 : Nat := 4983230072969 + 3 ^ 40 * 1696302 * 2
def baseEnd_1696302 : Nat := 193559613596250543183079

theorem tailTrace_1696302 : CollatzResearch.WordTrace tailWord_1696302 prefixEnd_1696302 193559613596250543183079 := by
  unfold tailWord_1696302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733652087574379270261395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41246144467063356108060773 7733652087574379270261395)
  ·
    refine ⟨11600478131361568905392093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7733652087574379270261395 11600478131361568905392093)
    ·
      refine ⟨4350179299260588339522035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11600478131361568905392093 4350179299260588339522035)
      ·
        refine ⟨6525268948890882509283053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350179299260588339522035 6525268948890882509283053)
        ·
          refine ⟨2446975855834080940981145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6525268948890882509283053 2446975855834080940981145)
          ·
            refine ⟨1835231891875560705735859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446975855834080940981145 1835231891875560705735859)
            ·
              refine ⟨2752847837813341058603789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835231891875560705735859 2752847837813341058603789)
              ·
                refine ⟨1032317939180002896976421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2752847837813341058603789 1032317939180002896976421)
                ·
                  refine ⟨193559613596250543183079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032317939180002896976421 193559613596250543183079)
                  ·
                    rfl

theorem cell22_1696302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_1696302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696302 prefixEnd_1696302 := by exact prefixLift 1696302
  have htrace : WordTrace (prefixWord ++ tailWord_1696302) baseStart_1696302 baseEnd_1696302 := by
    simpa [prefixWord, tailWord_1696302, baseEnd_1696302] using wordTrace_append hprefix tailTrace_1696302
  have hstable : (prefixWord ++ tailWord_1696302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696302).length < 2 ^ (prefixWord ++ tailWord_1696302).sum := by decide
  have hdescent : baseEnd_1696302 < baseStart_1696302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696388 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1696388 : Nat := 118140960795 + 1696388 * 2 ^ 59
def prefixEnd_1696388 : Nat := 4983230072969 + 3 ^ 40 * 1696388 * 2
def baseEnd_1696388 : Nat := 580708280346276071898973

theorem tailTrace_1696388 : CollatzResearch.WordTrace tailWord_1696388 prefixEnd_1696388 580708280346276071898973 := by
  unfold tailWord_1696388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30936176689141735424860909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41248235585522313899814545 30936176689141735424860909)
  ·
    refine ⟨11601066258428150784322841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30936176689141735424860909 11601066258428150784322841)
    ·
      refine ⟨8700799693821113088242131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11601066258428150784322841 8700799693821113088242131)
      ·
        refine ⟨13051199540731669632363197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8700799693821113088242131 13051199540731669632363197)
        ·
          refine ⟨4894199827774376112136199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13051199540731669632363197 4894199827774376112136199)
          ·
            refine ⟨7341299741661564168204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894199827774376112136199 7341299741661564168204299)
            ·
              refine ⟨11011949612492346252306449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341299741661564168204299 11011949612492346252306449)
              ·
                refine ⟨8258962209369259689229837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011949612492346252306449 8258962209369259689229837)
                ·
                  refine ⟨3097110828513472383461189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8258962209369259689229837 3097110828513472383461189)
                  ·
                    refine ⟨580708280346276071898973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3097110828513472383461189 580708280346276071898973)
                    ·
                      rfl

theorem cell22_1696388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1696388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696388 prefixEnd_1696388 := by exact prefixLift 1696388
  have htrace : WordTrace (prefixWord ++ tailWord_1696388) baseStart_1696388 baseEnd_1696388 := by
    simpa [prefixWord, tailWord_1696388, baseEnd_1696388] using wordTrace_append hprefix tailTrace_1696388
  have hstable : (prefixWord ++ tailWord_1696388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696388).length < 2 ^ (prefixWord ++ tailWord_1696388).sum := by decide
  have hdescent : baseEnd_1696388 < baseStart_1696388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696420 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1696420 : Nat := 118140960795 + 1696420 * 2 ^ 59
def prefixEnd_1696420 : Nat := 4983230072969 + 3 ^ 40 * 1696420 * 2
def baseEnd_1696420 : Nat := 193573078200079551699625

theorem tailTrace_1696420 : CollatzResearch.WordTrace tailWord_1696420 prefixEnd_1696420 193573078200079551699625 := by
  unfold tailWord_1696420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30936760257083770157443357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41249013676111693543257809 30936760257083770157443357)
  ·
    refine ⟨11601285096406413809041259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30936760257083770157443357 11601285096406413809041259)
    ·
      refine ⟨17401927644609620713561889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601285096406413809041259 17401927644609620713561889)
      ·
        refine ⟨13051445733457215535171417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17401927644609620713561889 13051445733457215535171417)
        ·
          refine ⟨9788584300092911651378563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13051445733457215535171417 9788584300092911651378563)
          ·
            refine ⟨14682876450139367477067845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788584300092911651378563 14682876450139367477067845)
            ·
              refine ⟨2753039334401131401950221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14682876450139367477067845 2753039334401131401950221)
              ·
                refine ⟨1032389750400424275731333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2753039334401131401950221 1032389750400424275731333)
                ·
                  refine ⟨193573078200079551699625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032389750400424275731333 193573078200079551699625)
                  ·
                    rfl

theorem cell22_1696420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1696420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696420 prefixEnd_1696420 := by exact prefixLift 1696420
  have htrace : WordTrace (prefixWord ++ tailWord_1696420) baseStart_1696420 baseEnd_1696420 := by
    simpa [prefixWord, tailWord_1696420, baseEnd_1696420] using wordTrace_append hprefix tailTrace_1696420
  have hstable : (prefixWord ++ tailWord_1696420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696420).length < 2 ^ (prefixWord ++ tailWord_1696420).sum := by decide
  have hdescent : baseEnd_1696420 < baseStart_1696420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696431 : List Nat := [1, 1, 2, 1, 2, 6, 9]
def baseStart_1696431 : Nat := 118140960795 + 1696431 * 2 ^ 59
def prefixEnd_1696431 : Nat := 4983230072969 + 3 ^ 40 * 1696431 * 2
def baseEnd_1696431 : Nat := 21508259263890307150883

theorem tailTrace_1696431 : CollatzResearch.WordTrace tailWord_1696431 prefixEnd_1696431 21508259263890307150883 := by
  unfold tailWord_1696431
  simp only [CollatzResearch.WordTrace]
  refine ⟨61873921717127689193537147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41249281144751792795691431 61873921717127689193537147)
  ·
    refine ⟨92810882575691533790305721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61873921717127689193537147 92810882575691533790305721)
    ·
      refine ⟨69608161931768650342729291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92810882575691533790305721 69608161931768650342729291)
      ·
        refine ⟨104412242897652975514093937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69608161931768650342729291 104412242897652975514093937)
        ·
          refine ⟨78309182173239731635570453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104412242897652975514093937 78309182173239731635570453)
          ·
            refine ⟨3670742914370612420417365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78309182173239731635570453 3670742914370612420417365)
            ·
              refine ⟨21508259263890307150883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3670742914370612420417365 21508259263890307150883)
              ·
                rfl

theorem cell22_1696431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 9].length) (baseStart_1696431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696431 prefixEnd_1696431 := by exact prefixLift 1696431
  have htrace : WordTrace (prefixWord ++ tailWord_1696431) baseStart_1696431 baseEnd_1696431 := by
    simpa [prefixWord, tailWord_1696431, baseEnd_1696431] using wordTrace_append hprefix tailTrace_1696431
  have hstable : (prefixWord ++ tailWord_1696431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696431).length < 2 ^ (prefixWord ++ tailWord_1696431).sum := by decide
  have hdescent : baseEnd_1696431 < baseStart_1696431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696435 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 2, 3]
def baseStart_1696435 : Nat := 118140960795 + 1696435 * 2 ^ 59
def prefixEnd_1696435 : Nat := 4983230072969 + 3 ^ 40 * 1696435 * 2
def baseEnd_1696435 : Nat := 580724369406783615973829

theorem tailTrace_1696435 : CollatzResearch.WordTrace tailWord_1696435 prefixEnd_1696435 580724369406783615973829 := by
  unfold tailWord_1696435
  simp only [CollatzResearch.WordTrace]
  refine ⟨61874067609113197876682759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41249378406075465251121839 61874067609113197876682759)
  ·
    refine ⟨92811101413669796815024139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61874067609113197876682759 92811101413669796815024139)
    ·
      refine ⟨139216652120504695222536209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92811101413669796815024139 139216652120504695222536209)
      ·
        refine ⟨104412489090378521416902157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139216652120504695222536209 104412489090378521416902157)
        ·
          refine ⟨39154683408891945531338309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104412489090378521416902157 39154683408891945531338309)
          ·
            refine ⟨7341503139167239787125933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39154683408891945531338309 7341503139167239787125933)
            ·
              refine ⟨2753063677187714920172225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7341503139167239787125933 2753063677187714920172225)
              ·
                refine ⟨2064797757890786190129169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753063677187714920172225 2064797757890786190129169)
                ·
                  refine ⟨1548598318418089642596877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2064797757890786190129169 1548598318418089642596877)
                  ·
                    refine ⟨580724369406783615973829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548598318418089642596877 580724369406783615973829)
                    ·
                      rfl

theorem cell22_1696435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 3].length) (baseStart_1696435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696435 prefixEnd_1696435 := by exact prefixLift 1696435
  have htrace : WordTrace (prefixWord ++ tailWord_1696435) baseStart_1696435 baseEnd_1696435 := by
    simpa [prefixWord, tailWord_1696435, baseEnd_1696435] using wordTrace_append hprefix tailTrace_1696435
  have hstable : (prefixWord ++ tailWord_1696435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696435).length < 2 ^ (prefixWord ++ tailWord_1696435).sum := by decide
  have hdescent : baseEnd_1696435 < baseStart_1696435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696493 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1696493 : Nat := 118140960795 + 1696493 * 2 ^ 59
def prefixEnd_1696493 : Nat := 4983230072969 + 3 ^ 40 * 1696493 * 2
def baseEnd_1696493 : Nat := 193581407997363599341217

theorem tailTrace_1696493 : CollatzResearch.WordTrace tailWord_1696493 prefixEnd_1696493 193581407997363599341217 := by
  unfold tailWord_1696493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61876183042903073782294133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41250788695268715854862755 61876183042903073782294133)
  ·
    refine ⟨5800892160272163167090075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61876183042903073782294133 5800892160272163167090075)
    ·
      refine ⟨8701338240408244750635113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5800892160272163167090075 8701338240408244750635113)
      ·
        refine ⟨6526003680306183562976335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8701338240408244750635113 6526003680306183562976335)
        ·
          refine ⟨9789005520459275344464503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526003680306183562976335 9789005520459275344464503)
          ·
            refine ⟨14683508280688913016696755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789005520459275344464503 14683508280688913016696755)
            ·
              refine ⟨22025262421033369525045133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14683508280688913016696755 22025262421033369525045133)
              ·
                refine ⟨8259473407887513571891925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22025262421033369525045133 8259473407887513571891925)
                ·
                  refine ⟨193581407997363599341217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8259473407887513571891925 193581407997363599341217)
                  ·
                    rfl

theorem cell22_1696493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1696493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696493 prefixEnd_1696493 := by exact prefixLift 1696493
  have htrace : WordTrace (prefixWord ++ tailWord_1696493) baseStart_1696493 baseEnd_1696493 := by
    simpa [prefixWord, tailWord_1696493, baseEnd_1696493] using wordTrace_append hprefix tailTrace_1696493
  have hstable : (prefixWord ++ tailWord_1696493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696493).length < 2 ^ (prefixWord ++ tailWord_1696493).sum := by decide
  have hdescent : baseEnd_1696493 < baseStart_1696493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696548 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_1696548 : Nat := 118140960795 + 1696548 * 2 ^ 59
def prefixEnd_1696548 : Nat := 4983230072969 + 3 ^ 40 * 1696548 * 2
def baseEnd_1696548 : Nat := 580763051616088987898483

theorem tailTrace_1696548 : CollatzResearch.WordTrace tailWord_1696548 prefixEnd_1696548 580763051616088987898483 := by
  unfold tailWord_1696548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30939094528851909087773149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41252126038469212117030865 30939094528851909087773149)
  ·
    refine ⟨11602160448319465907914931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30939094528851909087773149 11602160448319465907914931)
    ·
      refine ⟨17403240672479198861872397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11602160448319465907914931 17403240672479198861872397)
      ·
        refine ⟨6526215252179699573202149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17403240672479198861872397 6526215252179699573202149)
        ·
          refine ⟨1223665359783693669975403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6526215252179699573202149 1223665359783693669975403)
          ·
            refine ⟨1835498039675540504963105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223665359783693669975403 1835498039675540504963105)
            ·
              refine ⟨1376623529756655378722329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835498039675540504963105 1376623529756655378722329)
              ·
                refine ⟨1032467647317491534041747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376623529756655378722329 1032467647317491534041747)
                ·
                  refine ⟨1548701470976237301062621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032467647317491534041747 1548701470976237301062621)
                  ·
                    refine ⟨580763051616088987898483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548701470976237301062621 580763051616088987898483)
                    ·
                      rfl

theorem cell22_1696548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_1696548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696548 prefixEnd_1696548 := by exact prefixLift 1696548
  have htrace : WordTrace (prefixWord ++ tailWord_1696548) baseStart_1696548 baseEnd_1696548 := by
    simpa [prefixWord, tailWord_1696548, baseEnd_1696548] using wordTrace_append hprefix tailTrace_1696548
  have hstable : (prefixWord ++ tailWord_1696548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696548).length < 2 ^ (prefixWord ++ tailWord_1696548).sum := by decide
  have hdescent : baseEnd_1696548 < baseStart_1696548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696568 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1696568 : Nat := 118140960795 + 1696568 * 2 ^ 59
def prefixEnd_1696568 : Nat := 4983230072969 + 3 ^ 40 * 1696568 * 2
def baseEnd_1696568 : Nat := 580769898024815602398421

theorem tailTrace_1696568 : CollatzResearch.WordTrace tailWord_1696568 prefixEnd_1696568 580769898024815602398421 := by
  unfold tailWord_1696568
  simp only [CollatzResearch.WordTrace]
  refine ⟨30939459258815680795637179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41252612345087574394182905 30939459258815680795637179)
  ·
    refine ⟨46409188888223521193455769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30939459258815680795637179 46409188888223521193455769)
    ·
      refine ⟨34806891666167640895091827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46409188888223521193455769 34806891666167640895091827)
      ·
        refine ⟨52210337499251461342637741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34806891666167640895091827 52210337499251461342637741)
        ·
          refine ⟨19578876562219298003489153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52210337499251461342637741 19578876562219298003489153)
          ·
            refine ⟨14684157421664473502616865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19578876562219298003489153 14684157421664473502616865)
            ·
              refine ⟨11013118066248355126962649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14684157421664473502616865 11013118066248355126962649)
              ·
                refine ⟨8259838549686266345221987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11013118066248355126962649 8259838549686266345221987)
                ·
                  refine ⟨12389757824529399517832981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8259838549686266345221987 12389757824529399517832981)
                  ·
                    refine ⟨580769898024815602398421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12389757824529399517832981 580769898024815602398421)
                    ·
                      rfl

theorem cell22_1696568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1696568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696568 prefixEnd_1696568 := by exact prefixLift 1696568
  have htrace : WordTrace (prefixWord ++ tailWord_1696568) baseStart_1696568 baseEnd_1696568 := by
    simpa [prefixWord, tailWord_1696568, baseEnd_1696568] using wordTrace_append hprefix tailTrace_1696568
  have hstable : (prefixWord ++ tailWord_1696568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696568).length < 2 ^ (prefixWord ++ tailWord_1696568).sum := by decide
  have hdescent : baseEnd_1696568 < baseStart_1696568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696585 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_1696585 : Nat := 118140960795 + 1696585 * 2 ^ 59
def prefixEnd_1696585 : Nat := 4983230072969 + 3 ^ 40 * 1696585 * 2
def baseEnd_1696585 : Nat := 580775717472233224723369

theorem tailTrace_1696585 : CollatzResearch.WordTrace tailWord_1696585 prefixEnd_1696585 580775717472233224723369 := by
  unfold tailWord_1696585
  simp only [CollatzResearch.WordTrace]
  refine ⟨61879538558569773494643209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41253025705713182329762139 61879538558569773494643209)
  ·
    refine ⟨46409653918927330120982407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61879538558569773494643209 46409653918927330120982407)
    ·
      refine ⟨69614480878390995181473611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46409653918927330120982407 69614480878390995181473611)
      ·
        refine ⟨104421721317586492772210417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69614480878390995181473611 104421721317586492772210417)
        ·
          refine ⟨78316290988189869579157813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104421721317586492772210417 78316290988189869579157813)
          ·
            refine ⟨7342152280142800273046045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78316290988189869579157813 7342152280142800273046045)
            ·
              refine ⟨2753307105053550102392267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7342152280142800273046045 2753307105053550102392267)
              ·
                refine ⟨4129960657580325153588401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753307105053550102392267 4129960657580325153588401)
                ·
                  refine ⟨3097470493185243865191301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129960657580325153588401 3097470493185243865191301)
                  ·
                    refine ⟨580775717472233224723369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3097470493185243865191301 580775717472233224723369)
                    ·
                      rfl

theorem cell22_1696585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_1696585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696585 prefixEnd_1696585 := by exact prefixLift 1696585
  have htrace : WordTrace (prefixWord ++ tailWord_1696585) baseStart_1696585 baseEnd_1696585 := by
    simpa [prefixWord, tailWord_1696585, baseEnd_1696585] using wordTrace_append hprefix tailTrace_1696585
  have hstable : (prefixWord ++ tailWord_1696585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696585).length < 2 ^ (prefixWord ++ tailWord_1696585).sum := by decide
  have hdescent : baseEnd_1696585 < baseStart_1696585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696604 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1696604 : Nat := 118140960795 + 1696604 * 2 ^ 59
def prefixEnd_1696604 : Nat := 4983230072969 + 3 ^ 40 * 1696604 * 2
def baseEnd_1696604 : Nat := 580782221560523508498311

theorem tailTrace_1696604 : CollatzResearch.WordTrace tailWord_1696604 prefixEnd_1696604 580782221560523508498311 := by
  unfold tailWord_1696604
  simp only [CollatzResearch.WordTrace]
  refine ⟨30940115772750469869792433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41253487697000626493056577 30940115772750469869792433)
  ·
    refine ⟨23205086829562852402344325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30940115772750469869792433 23205086829562852402344325)
    ·
      refine ⟨4350953780543034825439561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23205086829562852402344325 4350953780543034825439561)
      ·
        refine ⟨3263215335407276119079671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4350953780543034825439561 3263215335407276119079671)
        ·
          refine ⟨4894823003110914178619507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263215335407276119079671 4894823003110914178619507)
          ·
            refine ⟨7342234504666371267929261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894823003110914178619507 7342234504666371267929261)
            ·
              refine ⟨2753337939249889225473473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7342234504666371267929261 2753337939249889225473473)
              ·
                refine ⟨2065003454437416919105105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753337939249889225473473 2065003454437416919105105)
                ·
                  refine ⟨1548752590828062689328829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2065003454437416919105105 1548752590828062689328829)
                  ·
                    refine ⟨580782221560523508498311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548752590828062689328829 580782221560523508498311)
                    ·
                      rfl

theorem cell22_1696604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1696604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696604 prefixEnd_1696604 := by exact prefixLift 1696604
  have htrace : WordTrace (prefixWord ++ tailWord_1696604) baseStart_1696604 baseEnd_1696604 := by
    simpa [prefixWord, tailWord_1696604, baseEnd_1696604] using wordTrace_append hprefix tailTrace_1696604
  have hstable : (prefixWord ++ tailWord_1696604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696604).length < 2 ^ (prefixWord ++ tailWord_1696604).sum := by decide
  have hdescent : baseEnd_1696604 < baseStart_1696604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696613 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1696613 : Nat := 118140960795 + 1696613 * 2 ^ 59
def prefixEnd_1696613 : Nat := 4983230072969 + 3 ^ 40 * 1696613 * 2
def baseEnd_1696613 : Nat := 580785302444450485023283

theorem tailTrace_1696613 : CollatzResearch.WordTrace tailWord_1696613 prefixEnd_1696613 580785302444450485023283 := by
  unfold tailWord_1696613
  simp only [CollatzResearch.WordTrace]
  refine ⟨61880559802468334276662493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41253706534978889517774995 61880559802468334276662493)
  ·
    refine ⟨23205209925925625353748435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61880559802468334276662493 23205209925925625353748435)
    ·
      refine ⟨34807814888888438030622653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23205209925925625353748435 34807814888888438030622653)
      ·
        refine ⟨13052930583333164261483495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34807814888888438030622653 13052930583333164261483495)
        ·
          refine ⟨19579395874999746392225243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13052930583333164261483495 19579395874999746392225243)
          ·
            refine ⟨29369093812499619588337865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19579395874999746392225243 29369093812499619588337865)
            ·
              refine ⟨22026820359374714691253399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29369093812499619588337865 22026820359374714691253399)
              ·
                refine ⟨33040230539062072036880099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22026820359374714691253399 33040230539062072036880099)
                ·
                  refine ⟨49560345808593108055320149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33040230539062072036880099 49560345808593108055320149)
                  ·
                    refine ⟨580785302444450485023283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49560345808593108055320149 580785302444450485023283)
                    ·
                      rfl

theorem cell22_1696613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1696613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696613 prefixEnd_1696613 := by exact prefixLift 1696613
  have htrace : WordTrace (prefixWord ++ tailWord_1696613) baseStart_1696613 baseEnd_1696613 := by
    simpa [prefixWord, tailWord_1696613, baseEnd_1696613] using wordTrace_append hprefix tailTrace_1696613
  have hstable : (prefixWord ++ tailWord_1696613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696613).length < 2 ^ (prefixWord ++ tailWord_1696613).sum := by decide
  have hdescent : baseEnd_1696613 < baseStart_1696613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696649 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 1, 3]
def baseStart_1696649 : Nat := 118140960795 + 1696649 * 2 ^ 59
def prefixEnd_1696649 : Nat := 4983230072969 + 3 ^ 40 * 1696649 * 2
def baseEnd_1696649 : Nat := 580797625980158391123173

theorem tailTrace_1696649 : CollatzResearch.WordTrace tailWord_1696649 prefixEnd_1696649 580797625980158391123173 := by
  unfold tailWord_1696649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881872830337912424973001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41254581886891941616648667 61881872830337912424973001)
  ·
    refine ⟨46411404622753434318729751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61881872830337912424973001 46411404622753434318729751)
    ·
      refine ⟨69617106934130151478094627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46411404622753434318729751 69617106934130151478094627)
      ·
        refine ⟨104425660401195227217141941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69617106934130151478094627 104425660401195227217141941)
        ·
          refine ⟨9789905662612052551607057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104425660401195227217141941 9789905662612052551607057)
          ·
            refine ⟨7342429246959039413705293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789905662612052551607057 7342429246959039413705293)
            ·
              refine ⟨2753410967609639780139485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7342429246959039413705293 2753410967609639780139485)
              ·
                refine ⟨1032529112853614917552307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2753410967609639780139485 1032529112853614917552307)
                ·
                  refine ⟨1548793669280422376328461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032529112853614917552307 1548793669280422376328461)
                  ·
                    refine ⟨580797625980158391123173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548793669280422376328461 580797625980158391123173)
                    ·
                      rfl

theorem cell22_1696649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_1696649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696649 prefixEnd_1696649 := by exact prefixLift 1696649
  have htrace : WordTrace (prefixWord ++ tailWord_1696649) baseStart_1696649 baseEnd_1696649 := by
    simpa [prefixWord, tailWord_1696649, baseEnd_1696649] using wordTrace_append hprefix tailTrace_1696649
  have hstable : (prefixWord ++ tailWord_1696649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696649).length < 2 ^ (prefixWord ++ tailWord_1696649).sum := by decide
  have hdescent : baseEnd_1696649 < baseStart_1696649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696666 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_1696666 : Nat := 118140960795 + 1696666 * 2 ^ 59
def prefixEnd_1696666 : Nat := 4983230072969 + 3 ^ 40 * 1696666 * 2
def baseEnd_1696666 : Nat := 580803445427576013448121

theorem tailTrace_1696666 : CollatzResearch.WordTrace tailWord_1696666 prefixEnd_1696666 580803445427576013448121 := by
  unfold tailWord_1696666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15470623217819081082085463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41254995247517549552227901 15470623217819081082085463)
  ·
    refine ⟨23205934826728621623128195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15470623217819081082085463 23205934826728621623128195)
    ·
      refine ⟨34808902240092932434692293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23205934826728621623128195 34808902240092932434692293)
      ·
        refine ⟨6526669170017424831504805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34808902240092932434692293 6526669170017424831504805)
        ·
          refine ⟨1223750469378267155907151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6526669170017424831504805 1223750469378267155907151)
          ·
            refine ⟨1835625704067400733860727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223750469378267155907151 1835625704067400733860727)
            ·
              refine ⟨2753438556101101100791091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835625704067400733860727 2753438556101101100791091)
              ·
                refine ⟨4130157834151651651186637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753438556101101100791091 4130157834151651651186637)
                ·
                  refine ⟨1548809187806869369194989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4130157834151651651186637 1548809187806869369194989)
                  ·
                    refine ⟨580803445427576013448121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548809187806869369194989 580803445427576013448121)
                    ·
                      rfl

theorem cell22_1696666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_1696666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696666 prefixEnd_1696666 := by exact prefixLift 1696666
  have htrace : WordTrace (prefixWord ++ tailWord_1696666) baseStart_1696666 baseEnd_1696666 := by
    simpa [prefixWord, tailWord_1696666, baseEnd_1696666] using wordTrace_append hprefix tailTrace_1696666
  have hstable : (prefixWord ++ tailWord_1696666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696666).length < 2 ^ (prefixWord ++ tailWord_1696666).sum := by decide
  have hdescent : baseEnd_1696666 < baseStart_1696666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696724 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1696724 : Nat := 118140960795 + 1696724 * 2 ^ 59
def prefixEnd_1696724 : Nat := 4983230072969 + 3 ^ 40 * 1696724 * 2
def baseEnd_1696724 : Nat := 193607766670961065165981

theorem tailTrace_1696724 : CollatzResearch.WordTrace tailWord_1696724 prefixEnd_1696724 193607766670961065165981 := by
  unfold tailWord_1696724
  simp only [CollatzResearch.WordTrace]
  refine ⟨30942304152533100116976613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41256405536710800155968817 30942304152533100116976613)
  ·
    refine ⟨5801682028599956271933115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30942304152533100116976613 5801682028599956271933115)
    ·
      refine ⟨8702523042899934407899673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801682028599956271933115 8702523042899934407899673)
      ·
        refine ⟨6526892282174950805924755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8702523042899934407899673 6526892282174950805924755)
        ·
          refine ⟨9790338423262426208887133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526892282174950805924755 9790338423262426208887133)
          ·
            refine ⟨3671376908723409828332675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9790338423262426208887133 3671376908723409828332675)
            ·
              refine ⟨5507065363085114742499013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671376908723409828332675 5507065363085114742499013)
              ·
                refine ⟨1032574755578459014218565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5507065363085114742499013 1032574755578459014218565)
                ·
                  refine ⟨193607766670961065165981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1032574755578459014218565 193607766670961065165981)
                  ·
                    rfl

theorem cell22_1696724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1696724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696724 prefixEnd_1696724 := by exact prefixLift 1696724
  have htrace : WordTrace (prefixWord ++ tailWord_1696724) baseStart_1696724 baseEnd_1696724 := by
    simpa [prefixWord, tailWord_1696724, baseEnd_1696724] using wordTrace_append hprefix tailTrace_1696724
  have hstable : (prefixWord ++ tailWord_1696724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696724).length < 2 ^ (prefixWord ++ tailWord_1696724).sum := by decide
  have hdescent : baseEnd_1696724 < baseStart_1696724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696754 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1696754 : Nat := 118140960795 + 1696754 * 2 ^ 59
def prefixEnd_1696754 : Nat := 4983230072969 + 3 ^ 40 * 1696754 * 2
def baseEnd_1696754 : Nat := 580833569625973117247851

theorem tailTrace_1696754 : CollatzResearch.WordTrace tailWord_1696754 prefixEnd_1696754 580833569625973117247851 := by
  unfold tailWord_1696754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471425623739378839386329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41257134996638343571696877 15471425623739378839386329)
  ·
    refine ⟨11603569217804534129539747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15471425623739378839386329 11603569217804534129539747)
    ·
      refine ⟨17405353826706801194309621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11603569217804534129539747 17405353826706801194309621)
      ·
        refine ⟨1631751921253762611966527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17405353826706801194309621 1631751921253762611966527)
        ·
          refine ⟨2447627881880643917949791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631751921253762611966527 2447627881880643917949791)
          ·
            refine ⟨3671441822820965876924687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447627881880643917949791 3671441822820965876924687)
            ·
              refine ⟨5507162734231448815387031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671441822820965876924687 5507162734231448815387031)
              ·
                refine ⟨8260744101347173223080547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507162734231448815387031 8260744101347173223080547)
                ·
                  refine ⟨12391116152020759834620821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8260744101347173223080547 12391116152020759834620821)
                  ·
                    refine ⟨580833569625973117247851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12391116152020759834620821 580833569625973117247851)
                    ·
                      rfl

theorem cell22_1696754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1696754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696754 prefixEnd_1696754 := by exact prefixLift 1696754
  have htrace : WordTrace (prefixWord ++ tailWord_1696754) baseStart_1696754 baseEnd_1696754 := by
    simpa [prefixWord, tailWord_1696754, baseEnd_1696754] using wordTrace_append hprefix tailTrace_1696754
  have hstable : (prefixWord ++ tailWord_1696754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696754).length < 2 ^ (prefixWord ++ tailWord_1696754).sum := by decide
  have hdescent : baseEnd_1696754 < baseStart_1696754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696842 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_1696842 : Nat := 118140960795 + 1696842 * 2 ^ 59
def prefixEnd_1696842 : Nat := 4983230072969 + 3 ^ 40 * 1696842 * 2
def baseEnd_1696842 : Nat := 193621231274790073682527

theorem tailTrace_1696842 : CollatzResearch.WordTrace tailWord_1696842 prefixEnd_1696842 193621231274790073682527 := by
  unfold tailWord_1696842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472228029659676596687195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41259274745759137591165853 15472228029659676596687195)
  ·
    refine ⟨23208342044489514895030793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15472228029659676596687195 23208342044489514895030793)
    ·
      refine ⟨17406256533367136171273095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23208342044489514895030793 17406256533367136171273095)
      ·
        refine ⟨26109384800050704256909643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17406256533367136171273095 26109384800050704256909643)
        ·
          refine ⟨39164077200076056385364465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26109384800050704256909643 39164077200076056385364465)
          ·
            refine ⟨29373057900057042289023349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39164077200076056385364465 29373057900057042289023349)
            ·
              refine ⟨2753724178130347714595939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29373057900057042289023349 2753724178130347714595939)
              ·
                refine ⟨4130586267195521571893909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753724178130347714595939 4130586267195521571893909)
                ·
                  refine ⟨193621231274790073682527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4130586267195521571893909 193621231274790073682527)
                  ·
                    rfl

theorem cell22_1696842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_1696842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696842 prefixEnd_1696842 := by exact prefixLift 1696842
  have htrace : WordTrace (prefixWord ++ tailWord_1696842) baseStart_1696842 baseEnd_1696842 := by
    simpa [prefixWord, tailWord_1696842, baseEnd_1696842] using wordTrace_append hprefix tailTrace_1696842
  have hstable : (prefixWord ++ tailWord_1696842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696842).length < 2 ^ (prefixWord ++ tailWord_1696842).sum := by decide
  have hdescent : baseEnd_1696842 < baseStart_1696842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696857 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_1696857 : Nat := 118140960795 + 1696857 * 2 ^ 59
def prefixEnd_1696857 : Nat := 4983230072969 + 3 ^ 40 * 1696857 * 2
def baseEnd_1696857 : Nat := 580868828630915181922535

theorem tailTrace_1696857 : CollatzResearch.WordTrace tailWord_1696857 prefixEnd_1696857 580868828630915181922535 := by
  unfold tailWord_1696857
  simp only [CollatzResearch.WordTrace]
  refine ⟨61889459213584363948544825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41259639475722909299029883 61889459213584363948544825)
  ·
    refine ⟨46417094410188272961408619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61889459213584363948544825 46417094410188272961408619)
    ·
      refine ⟨69625641615282409442112929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46417094410188272961408619 69625641615282409442112929)
      ·
        refine ⟨52219231211461807081584697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69625641615282409442112929 52219231211461807081584697)
        ·
          refine ⟨39164423408596355311188523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52219231211461807081584697 39164423408596355311188523)
          ·
            refine ⟨58746635112894532966782785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39164423408596355311188523 58746635112894532966782785)
            ·
              refine ⟨44059976334670899725087089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58746635112894532966782785 44059976334670899725087089)
              ·
                refine ⟨33044982251003174793815317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44059976334670899725087089 33044982251003174793815317)
                ·
                  refine ⟨1548983543015773818460093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33044982251003174793815317 1548983543015773818460093)
                  ·
                    refine ⟨580868828630915181922535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1548983543015773818460093 580868828630915181922535)
                    ·
                      rfl

theorem cell22_1696857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_1696857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696857 prefixEnd_1696857 := by exact prefixLift 1696857
  have htrace : WordTrace (prefixWord ++ tailWord_1696857) baseStart_1696857 baseEnd_1696857 := by
    simpa [prefixWord, tailWord_1696857, baseEnd_1696857] using wordTrace_append hprefix tailTrace_1696857
  have hstable : (prefixWord ++ tailWord_1696857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696857).length < 2 ^ (prefixWord ++ tailWord_1696857).sum := by decide
  have hdescent : baseEnd_1696857 < baseStart_1696857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696861 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1696861 : Nat := 118140960795 + 1696861 * 2 ^ 59
def prefixEnd_1696861 : Nat := 4983230072969 + 3 ^ 40 * 1696861 * 2
def baseEnd_1696861 : Nat := 580870197912660504822523

theorem tailTrace_1696861 : CollatzResearch.WordTrace tailWord_1696861 prefixEnd_1696861 580870197912660504822523 := by
  unfold tailWord_1696861
  simp only [CollatzResearch.WordTrace]
  refine ⟨61889605105569872631690437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41259736737046581754460291 61889605105569872631690437)
  ·
    refine ⟨11604300957294351118441957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61889605105569872631690437 11604300957294351118441957)
    ·
      refine ⟨2175806429492690834707867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11604300957294351118441957 2175806429492690834707867)
      ·
        refine ⟨3263709644239036252061801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175806429492690834707867 3263709644239036252061801)
        ·
          refine ⟨2447782233179277189046351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3263709644239036252061801 2447782233179277189046351)
          ·
            refine ⟨3671673349768915783569527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447782233179277189046351 3671673349768915783569527)
            ·
              refine ⟨5507510024653373675354291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671673349768915783569527 5507510024653373675354291)
              ·
                refine ⟨8261265036980060513031437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507510024653373675354291 8261265036980060513031437)
                ·
                  refine ⟨3097974388867522692386789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8261265036980060513031437 3097974388867522692386789)
                  ·
                    refine ⟨580870197912660504822523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3097974388867522692386789 580870197912660504822523)
                    ·
                      rfl

theorem cell22_1696861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1696861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696861 prefixEnd_1696861 := by exact prefixLift 1696861
  have htrace : WordTrace (prefixWord ++ tailWord_1696861) baseStart_1696861 baseEnd_1696861 := by
    simpa [prefixWord, tailWord_1696861, baseEnd_1696861] using wordTrace_append hprefix tailTrace_1696861
  have hstable : (prefixWord ++ tailWord_1696861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696861).length < 2 ^ (prefixWord ++ tailWord_1696861).sum := by decide
  have hdescent : baseEnd_1696861 < baseStart_1696861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696874 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1696874 : Nat := 118140960795 + 1696874 * 2 ^ 59
def prefixEnd_1696874 : Nat := 4983230072969 + 3 ^ 40 * 1696874 * 2
def baseEnd_1696874 : Nat := 580874648078332804247483

theorem tailTrace_1696874 : CollatzResearch.WordTrace tailWord_1696874 prefixEnd_1696874 580874648078332804247483 := by
  unfold tailWord_1696874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472519813630693962978419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41260052836348517234609117 15472519813630693962978419)
  ·
    refine ⟨23208779720446040944467629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15472519813630693962978419 23208779720446040944467629)
    ·
      refine ⟨8703292395167265354175361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23208779720446040944467629 8703292395167265354175361)
      ·
        refine ⟨6527469296375449015631521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8703292395167265354175361 6527469296375449015631521)
        ·
          refine ⟨4895601972281586761723641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527469296375449015631521 4895601972281586761723641)
          ·
            refine ⟨3671701479211190071292731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4895601972281586761723641 3671701479211190071292731)
            ·
              refine ⟨5507552218816785106939097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671701479211190071292731 5507552218816785106939097)
              ·
                refine ⟨4130664164112588830204323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507552218816785106939097 4130664164112588830204323)
                ·
                  refine ⟨6195996246168883245306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130664164112588830204323 6195996246168883245306485)
                  ·
                    refine ⟨580874648078332804247483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6195996246168883245306485 580874648078332804247483)
                    ·
                      rfl

theorem cell22_1696874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1696874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696874 prefixEnd_1696874 := by exact prefixLift 1696874
  have htrace : WordTrace (prefixWord ++ tailWord_1696874) baseStart_1696874 baseEnd_1696874 := by
    simpa [prefixWord, tailWord_1696874, baseEnd_1696874] using wordTrace_append hprefix tailTrace_1696874
  have hstable : (prefixWord ++ tailWord_1696874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696874).length < 2 ^ (prefixWord ++ tailWord_1696874).sum := by decide
  have hdescent : baseEnd_1696874 < baseStart_1696874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696919 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 5, 3]
def baseStart_1696919 : Nat := 118140960795 + 1696919 * 2 ^ 59
def prefixEnd_1696919 : Nat := 4983230072969 + 3 ^ 40 * 1696919 * 2
def baseEnd_1696919 : Nat := 580890052497967686872345

theorem tailTrace_1696919 : CollatzResearch.WordTrace tailWord_1696919 prefixEnd_1696919 580890052497967686872345 := by
  unfold tailWord_1696919
  simp only [CollatzResearch.WordTrace]
  refine ⟨61891720539359748537301811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41261147026239832358201207 61891720539359748537301811)
  ·
    refine ⟨92837580809039622805952717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61891720539359748537301811 92837580809039622805952717)
    ·
      refine ⟨34814092803389858552232269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92837580809039622805952717 34814092803389858552232269)
      ·
        refine ⟨13055284801271196957087101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34814092803389858552232269 13055284801271196957087101)
        ·
          refine ⟨4895731800476698858907663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13055284801271196957087101 4895731800476698858907663)
          ·
            refine ⟨7343597700715048288361495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895731800476698858907663 7343597700715048288361495)
            ·
              refine ⟨11015396551072572432542243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343597700715048288361495 11015396551072572432542243)
              ·
                refine ⟨16523094826608858648813365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015396551072572432542243 16523094826608858648813365)
                ·
                  refine ⟨1549040139994580498326253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16523094826608858648813365 1549040139994580498326253)
                  ·
                    refine ⟨580890052497967686872345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1549040139994580498326253 580890052497967686872345)
                    ·
                      rfl

theorem cell22_1696919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_1696919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696919 prefixEnd_1696919 := by exact prefixLift 1696919
  have htrace : WordTrace (prefixWord ++ tailWord_1696919) baseStart_1696919 baseEnd_1696919 := by
    simpa [prefixWord, tailWord_1696919, baseEnd_1696919] using wordTrace_append hprefix tailTrace_1696919
  have hstable : (prefixWord ++ tailWord_1696919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696919).length < 2 ^ (prefixWord ++ tailWord_1696919).sum := by decide
  have hdescent : baseEnd_1696919 < baseStart_1696919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696947 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_1696947 : Nat := 118140960795 + 1696947 * 2 ^ 59
def prefixEnd_1696947 : Nat := 4983230072969 + 3 ^ 40 * 1696947 * 2
def baseEnd_1696947 : Nat := 580899637470184947172259

theorem tailTrace_1696947 : CollatzResearch.WordTrace tailWord_1696947 prefixEnd_1696947 580899637470184947172259 := by
  unfold tailWord_1696947
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892741783258309319321095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41261827855505539546214063 61892741783258309319321095)
  ·
    refine ⟨92839112674887463978981643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61892741783258309319321095 92839112674887463978981643)
    ·
      refine ⟨139258669012331195968472465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92839112674887463978981643 139258669012331195968472465)
      ·
        refine ⟨104444001759248396976354349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139258669012331195968472465 104444001759248396976354349)
        ·
          refine ⟨39166500659718148866132881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104444001759248396976354349 39166500659718148866132881)
          ·
            refine ⟨29374875494788611649599661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39166500659718148866132881 29374875494788611649599661)
            ·
              refine ⟨11015578310545729368599873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29374875494788611649599661 11015578310545729368599873)
              ·
                refine ⟨8261683732909297026449905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11015578310545729368599873 8261683732909297026449905)
                ·
                  refine ⟨6196262799681972769837429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8261683732909297026449905 6196262799681972769837429)
                  ·
                    refine ⟨580899637470184947172259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6196262799681972769837429 580899637470184947172259)
                    ·
                      rfl

theorem cell22_1696947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_1696947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1696947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1696947 prefixEnd_1696947 := by exact prefixLift 1696947
  have htrace : WordTrace (prefixWord ++ tailWord_1696947) baseStart_1696947 baseEnd_1696947 := by
    simpa [prefixWord, tailWord_1696947, baseEnd_1696947] using wordTrace_append hprefix tailTrace_1696947
  have hstable : (prefixWord ++ tailWord_1696947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696947).length < 2 ^ (prefixWord ++ tailWord_1696947).sum := by decide
  have hdescent : baseEnd_1696947 < baseStart_1696947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697178 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1697178 : Nat := 118140960795 + 1697178 * 2 ^ 59
def prefixEnd_1697178 : Nat := 4983230072969 + 3 ^ 40 * 1697178 * 2
def baseEnd_1697178 : Nat := 580978713490977344646551

theorem tailTrace_1697178 : CollatzResearch.WordTrace tailWord_1697178 prefixEnd_1697178 580978713490977344646551 := by
  unfold tailWord_1697178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475291761355358942745047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41267444696947623847320125 15475291761355358942745047)
  ·
    refine ⟨23212937642033038414117571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15475291761355358942745047 23212937642033038414117571)
    ·
      refine ⟨34819406463049557621176357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23212937642033038414117571 34819406463049557621176357)
      ·
        refine ⟨6528638711821792053970567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34819406463049557621176357 6528638711821792053970567)
        ·
          refine ⟨9792958067732688080955851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528638711821792053970567 9792958067732688080955851)
          ·
            refine ⟨14689437101599032121433777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9792958067732688080955851 14689437101599032121433777)
            ·
              refine ⟨11017077826199274091075333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14689437101599032121433777 11017077826199274091075333)
              ·
                refine ⟨2065702092412363892076625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11017077826199274091075333 2065702092412363892076625)
                ·
                  refine ⟨1549276569309272919057469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2065702092412363892076625 1549276569309272919057469)
                  ·
                    refine ⟨580978713490977344646551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1549276569309272919057469 580978713490977344646551)
                    ·
                      rfl

theorem cell22_1697178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1697178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697178 prefixEnd_1697178 := by exact prefixLift 1697178
  have htrace : WordTrace (prefixWord ++ tailWord_1697178) baseStart_1697178 baseEnd_1697178 := by
    simpa [prefixWord, tailWord_1697178, baseEnd_1697178] using wordTrace_append hprefix tailTrace_1697178
  have hstable : (prefixWord ++ tailWord_1697178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697178).length < 2 ^ (prefixWord ++ tailWord_1697178).sum := by decide
  have hdescent : baseEnd_1697178 < baseStart_1697178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697180 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1697180 : Nat := 118140960795 + 1697180 * 2 ^ 59
def prefixEnd_1697180 : Nat := 4983230072969 + 3 ^ 40 * 1697180 * 2
def baseEnd_1697180 : Nat := 193659799377283335365515

theorem tailTrace_1697180 : CollatzResearch.WordTrace tailWord_1697180 prefixEnd_1697180 193659799377283335365515 := by
  unfold tailWord_1697180
  simp only [CollatzResearch.WordTrace]
  refine ⟨30950619995707095056276497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41267493327609460075035329 30950619995707095056276497)
  ·
    refine ⟨23212964996780321292207373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30950619995707095056276497 23212964996780321292207373)
    ·
      refine ⟨8704861873792620484577765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23212964996780321292207373 8704861873792620484577765)
      ·
        refine ⟨1632161601336116340858331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8704861873792620484577765 1632161601336116340858331)
        ·
          refine ⟨2448242402004174511287497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632161601336116340858331 2448242402004174511287497)
          ·
            refine ⟨1836181801503130883465623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448242402004174511287497 1836181801503130883465623)
            ·
              refine ⟨2754272702254696325198435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836181801503130883465623 2754272702254696325198435)
              ·
                refine ⟨4131409053382044487797653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754272702254696325198435 4131409053382044487797653)
                ·
                  refine ⟨193659799377283335365515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4131409053382044487797653 193659799377283335365515)
                  ·
                    rfl

theorem cell22_1697180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1697180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697180 prefixEnd_1697180 := by exact prefixLift 1697180
  have htrace : WordTrace (prefixWord ++ tailWord_1697180) baseStart_1697180 baseEnd_1697180 := by
    simpa [prefixWord, tailWord_1697180, baseEnd_1697180] using wordTrace_append hprefix tailTrace_1697180
  have hstable : (prefixWord ++ tailWord_1697180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697180).length < 2 ^ (prefixWord ++ tailWord_1697180).sum := by decide
  have hdescent : baseEnd_1697180 < baseStart_1697180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1697189 : Nat := 118140960795 + 1697189 * 2 ^ 59
def prefixEnd_1697189 : Nat := 4983230072969 + 3 ^ 40 * 1697189 * 2
def baseEnd_1697189 : Nat := 580982479015776982621517

theorem tailTrace_1697189 : CollatzResearch.WordTrace tailWord_1697189 prefixEnd_1697189 580982479015776982621517 := by
  unfold tailWord_1697189
  simp only [CollatzResearch.WordTrace]
  refine ⟨61901568248381584649630621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41267712165587723099753747 61901568248381584649630621)
  ·
    refine ⟨23213088093143094243611483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61901568248381584649630621 23213088093143094243611483)
    ·
      refine ⟨34819632139714641365417225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23213088093143094243611483 34819632139714641365417225)
      ·
        refine ⟨26114724104785981024062919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34819632139714641365417225 26114724104785981024062919)
        ·
          refine ⟨39172086157178971536094379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26114724104785981024062919 39172086157178971536094379)
          ·
            refine ⟨58758129235768457304141569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39172086157178971536094379 58758129235768457304141569)
            ·
              refine ⟨44068596926826342978106177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58758129235768457304141569 44068596926826342978106177)
              ·
                refine ⟨33051447695119757233579633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44068596926826342978106177 33051447695119757233579633)
                ·
                  refine ⟨24788585771339817925184725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33051447695119757233579633 24788585771339817925184725)
                  ·
                    refine ⟨580982479015776982621517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24788585771339817925184725 580982479015776982621517)
                    ·
                      rfl

theorem cell22_1697189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1697189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697189 prefixEnd_1697189 := by exact prefixLift 1697189
  have htrace : WordTrace (prefixWord ++ tailWord_1697189) baseStart_1697189 baseEnd_1697189 := by
    simpa [prefixWord, tailWord_1697189, baseEnd_1697189] using wordTrace_append hprefix tailTrace_1697189
  have hstable : (prefixWord ++ tailWord_1697189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697189).length < 2 ^ (prefixWord ++ tailWord_1697189).sum := by decide
  have hdescent : baseEnd_1697189 < baseStart_1697189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697191 : List Nat := [1, 1, 6, 1, 1, 1, 4, 7]
def baseStart_1697191 : Nat := 118140960795 + 1697191 * 2 ^ 59
def prefixEnd_1697191 : Nat := 4983230072969 + 3 ^ 40 * 1697191 * 2
def baseEnd_1697191 : Nat := 64553684850738849341279

theorem tailTrace_1697191 : CollatzResearch.WordTrace tailWord_1697191 prefixEnd_1697191 64553684850738849341279 := by
  unfold tailWord_1697191
  simp only [CollatzResearch.WordTrace]
  refine ⟨61901641194374338991203427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41267760796249559327468951 61901641194374338991203427)
  ·
    refine ⟨92852461791561508486805141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61901641194374338991203427 92852461791561508486805141)
    ·
      refine ⟨4352459146479445710318991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92852461791561508486805141 4352459146479445710318991)
      ·
        refine ⟨6528688719719168565478487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352459146479445710318991 6528688719719168565478487)
        ·
          refine ⟨9793033079578752848217731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528688719719168565478487 9793033079578752848217731)
          ·
            refine ⟨14689549619368129272326597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9793033079578752848217731 14689549619368129272326597)
            ·
              refine ⟨2754290553631524238561237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14689549619368129272326597 2754290553631524238561237)
              ·
                refine ⟨64553684850738849341279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2754290553631524238561237 64553684850738849341279)
                ·
                  rfl

theorem cell22_1697191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 7].length) (baseStart_1697191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697191 prefixEnd_1697191 := by exact prefixLift 1697191
  have htrace : WordTrace (prefixWord ++ tailWord_1697191) baseStart_1697191 baseEnd_1697191 := by
    simpa [prefixWord, tailWord_1697191, baseEnd_1697191] using wordTrace_append hprefix tailTrace_1697191
  have hstable : (prefixWord ++ tailWord_1697191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697191).length < 2 ^ (prefixWord ++ tailWord_1697191).sum := by decide
  have hdescent : baseEnd_1697191 < baseStart_1697191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697219 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 9]
def baseStart_1697219 : Nat := 118140960795 + 1697219 * 2 ^ 59
def prefixEnd_1697219 : Nat := 4983230072969 + 3 ^ 40 * 1697219 * 2
def baseEnd_1697219 : Nat := 193664249542955634790475

theorem tailTrace_1697219 : CollatzResearch.WordTrace tailWord_1697219 prefixEnd_1697219 193664249542955634790475 := by
  unfold tailWord_1697219
  simp only [CollatzResearch.WordTrace]
  refine ⟨61902662438272899773222711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41268441625515266515481807 61902662438272899773222711)
  ·
    refine ⟨92853993657409349659834067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61902662438272899773222711 92853993657409349659834067)
    ·
      refine ⟨139280990486114024489751101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92853993657409349659834067 139280990486114024489751101)
      ·
        refine ⟨52230371432292759183656663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139280990486114024489751101 52230371432292759183656663)
        ·
          refine ⟨78345557148439138775484995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52230371432292759183656663 78345557148439138775484995)
          ·
            refine ⟨117518335722658708163227493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78345557148439138775484995 117518335722658708163227493)
            ·
              refine ⟨22034687947998507780605155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117518335722658708163227493 22034687947998507780605155)
              ·
                refine ⟨33052031921997761670907733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22034687947998507780605155 33052031921997761670907733)
                ·
                  refine ⟨193664249542955634790475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33052031921997761670907733 193664249542955634790475)
                  ·
                    rfl

theorem cell22_1697219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_1697219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697219 prefixEnd_1697219 := by exact prefixLift 1697219
  have htrace : WordTrace (prefixWord ++ tailWord_1697219) baseStart_1697219 baseEnd_1697219 := by
    simpa [prefixWord, tailWord_1697219, baseEnd_1697219] using wordTrace_append hprefix tailTrace_1697219
  have hstable : (prefixWord ++ tailWord_1697219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697219).length < 2 ^ (prefixWord ++ tailWord_1697219).sum := by decide
  have hdescent : baseEnd_1697219 < baseStart_1697219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697238 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1697238 : Nat := 118140960795 + 1697238 * 2 ^ 59
def prefixEnd_1697238 : Nat := 4983230072969 + 3 ^ 40 * 1697238 * 2
def baseEnd_1697238 : Nat := 580999252717157188146367

theorem tailTrace_1697238 : CollatzResearch.WordTrace tailWord_1697238 prefixEnd_1697238 580999252717157188146367 := by
  unfold tailWord_1697238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868959714075254126135273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41268903616802710678776245 3868959714075254126135273)
  ·
    refine ⟨2901719785556440594601455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3868959714075254126135273 2901719785556440594601455)
    ·
      refine ⟨4352579678334660891902183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901719785556440594601455 4352579678334660891902183)
      ·
        refine ⟨6528869517501991337853275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352579678334660891902183 6528869517501991337853275)
        ·
          refine ⟨9793304276252987006779913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528869517501991337853275 9793304276252987006779913)
          ·
            refine ⟨7344978207189740255084935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793304276252987006779913 7344978207189740255084935)
            ·
              refine ⟨11017467310784610382627403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7344978207189740255084935 11017467310784610382627403)
              ·
                refine ⟨16526200966176915573941105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017467310784610382627403 16526200966176915573941105)
                ·
                  refine ⟨12394650724632686680455829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16526200966176915573941105 12394650724632686680455829)
                  ·
                    refine ⟨580999252717157188146367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12394650724632686680455829 580999252717157188146367)
                    ·
                      rfl

theorem cell22_1697238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1697238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697238 prefixEnd_1697238 := by exact prefixLift 1697238
  have htrace : WordTrace (prefixWord ++ tailWord_1697238) baseStart_1697238 baseEnd_1697238 := by
    simpa [prefixWord, tailWord_1697238, baseEnd_1697238] using wordTrace_append hprefix tailTrace_1697238
  have hstable : (prefixWord ++ tailWord_1697238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697238).length < 2 ^ (prefixWord ++ tailWord_1697238).sum := by decide
  have hdescent : baseEnd_1697238 < baseStart_1697238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697251 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_1697251 : Nat := 118140960795 + 1697251 * 2 ^ 59
def prefixEnd_1697251 : Nat := 4983230072969 + 3 ^ 40 * 1697251 * 2
def baseEnd_1697251 : Nat := 581003702882829487571327

theorem tailTrace_1697251 : CollatzResearch.WordTrace tailWord_1697251 prefixEnd_1697251 581003702882829487571327 := by
  unfold tailWord_1697251
  simp only [CollatzResearch.WordTrace]
  refine ⟨61903829574156969238387607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41269219716104646158925071 61903829574156969238387607)
  ·
    refine ⟨92855744361235453857581411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61903829574156969238387607 92855744361235453857581411)
    ·
      refine ⟨139283616541853180786372117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92855744361235453857581411 139283616541853180786372117)
      ·
        refine ⟨6528919525399367849361193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139283616541853180786372117 6528919525399367849361193)
        ·
          refine ⟨4896689644049525887020895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6528919525399367849361193 4896689644049525887020895)
          ·
            refine ⟨7345034466074288830531343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896689644049525887020895 7345034466074288830531343)
            ·
              refine ⟨11017551699111433245797015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7345034466074288830531343 11017551699111433245797015)
              ·
                refine ⟨16526327548667149868695523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11017551699111433245797015 16526327548667149868695523)
                ·
                  refine ⟨24789491323000724803043285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16526327548667149868695523 24789491323000724803043285)
                  ·
                    refine ⟨581003702882829487571327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24789491323000724803043285 581003702882829487571327)
                    ·
                      rfl

theorem cell22_1697251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_1697251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697251 prefixEnd_1697251 := by exact prefixLift 1697251
  have htrace : WordTrace (prefixWord ++ tailWord_1697251) baseStart_1697251 baseEnd_1697251 := by
    simpa [prefixWord, tailWord_1697251, baseEnd_1697251] using wordTrace_append hprefix tailTrace_1697251
  have hstable : (prefixWord ++ tailWord_1697251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697251).length < 2 ^ (prefixWord ++ tailWord_1697251).sum := by decide
  have hdescent : baseEnd_1697251 < baseStart_1697251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697253 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 5]
def baseStart_1697253 : Nat := 118140960795 + 1697253 * 2 ^ 59
def prefixEnd_1697253 : Nat := 4983230072969 + 3 ^ 40 * 1697253 * 2
def baseEnd_1697253 : Nat := 193668129174567383007107

theorem tailTrace_1697253 : CollatzResearch.WordTrace tailWord_1697253 prefixEnd_1697253 193668129174567383007107 := by
  unfold tailWord_1697253
  simp only [CollatzResearch.WordTrace]
  refine ⟨61903902520149723579960413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41269268346766482386640275 61903902520149723579960413)
  ·
    refine ⟨23213963445056146342485155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61903902520149723579960413 23213963445056146342485155)
    ·
      refine ⟨34820945167584219513727733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23213963445056146342485155 34820945167584219513727733)
      ·
        refine ⟨3264463609461020579411975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34820945167584219513727733 3264463609461020579411975)
        ·
          refine ⟨4896695414191530869117963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264463609461020579411975 4896695414191530869117963)
          ·
            refine ⟨7345043121287296303676945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4896695414191530869117963 7345043121287296303676945)
            ·
              refine ⟨5508782340965472227757709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7345043121287296303676945 5508782340965472227757709)
              ·
                refine ⟨2065793377862052085409141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5508782340965472227757709 2065793377862052085409141)
                ·
                  refine ⟨193668129174567383007107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065793377862052085409141 193668129174567383007107)
                  ·
                    rfl

theorem cell22_1697253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_1697253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697253 prefixEnd_1697253 := by exact prefixLift 1697253
  have htrace : WordTrace (prefixWord ++ tailWord_1697253) baseStart_1697253 baseEnd_1697253 := by
    simpa [prefixWord, tailWord_1697253, baseEnd_1697253] using wordTrace_append hprefix tailTrace_1697253
  have hstable : (prefixWord ++ tailWord_1697253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697253).length < 2 ^ (prefixWord ++ tailWord_1697253).sum := by decide
  have hdescent : baseEnd_1697253 < baseStart_1697253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697311 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_1697311 : Nat := 118140960795 + 1697311 * 2 ^ 59
def prefixEnd_1697311 : Nat := 4983230072969 + 3 ^ 40 * 1697311 * 2
def baseEnd_1697311 : Nat := 581024242109009331071143

theorem tailTrace_1697311 : CollatzResearch.WordTrace tailWord_1697311 prefixEnd_1697311 581024242109009331071143 := by
  unfold tailWord_1697311
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906017953939599485571787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41270678635959732990381191 61906017953939599485571787)
  ·
    refine ⟨92859026930909399228357681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61906017953939599485571787 92859026930909399228357681)
    ·
      refine ⟨69644270198182049421268261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92859026930909399228357681 69644270198182049421268261)
      ·
        refine ⟨13058300662159134266487799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69644270198182049421268261 13058300662159134266487799)
        ·
          refine ⟨19587450993238701399731699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13058300662159134266487799 19587450993238701399731699)
          ·
            refine ⟨29381176489858052099597549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19587450993238701399731699 29381176489858052099597549)
            ·
              refine ⟨11017941183696769537349081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29381176489858052099597549 11017941183696769537349081)
              ·
                refine ⟨8263455887772577153011811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11017941183696769537349081 8263455887772577153011811)
                ·
                  refine ⟨12395183831658865729517717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8263455887772577153011811 12395183831658865729517717)
                  ·
                    refine ⟨581024242109009331071143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12395183831658865729517717 581024242109009331071143)
                    ·
                      rfl

theorem cell22_1697311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_1697311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697311 prefixEnd_1697311 := by exact prefixLift 1697311
  have htrace : WordTrace (prefixWord ++ tailWord_1697311) baseStart_1697311 baseEnd_1697311 := by
    simpa [prefixWord, tailWord_1697311, baseEnd_1697311] using wordTrace_append hprefix tailTrace_1697311
  have hstable : (prefixWord ++ tailWord_1697311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697311).length < 2 ^ (prefixWord ++ tailWord_1697311).sum := by decide
  have hdescent : baseEnd_1697311 < baseStart_1697311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697313 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1697313 : Nat := 118140960795 + 1697313 * 2 ^ 59
def prefixEnd_1697313 : Nat := 4983230072969 + 3 ^ 40 * 1697313 * 2
def baseEnd_1697313 : Nat := 581024926749881992521137

theorem tailTrace_1697313 : CollatzResearch.WordTrace tailWord_1697313 prefixEnd_1697313 581024926749881992521137 := by
  unfold tailWord_1697313
  simp only [CollatzResearch.WordTrace]
  refine ⟨61906090899932353827144593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41270727266621569218096395 61906090899932353827144593)
  ·
    refine ⟨46429568174949265370358445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61906090899932353827144593 46429568174949265370358445)
    ·
      refine ⟨17411088065605974513884417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46429568174949265370358445 17411088065605974513884417)
      ·
        refine ⟨13058316049204480885413313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17411088065605974513884417 13058316049204480885413313)
        ·
          refine ⟨9793737036903360664059985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13058316049204480885413313 9793737036903360664059985)
          ·
            refine ⟨7345302777677520498044989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793737036903360664059985 7345302777677520498044989)
            ·
              refine ⟨2754488541629070186766871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7345302777677520498044989 2754488541629070186766871)
              ·
                refine ⟨4131732812443605280150307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754488541629070186766871 4131732812443605280150307)
                ·
                  refine ⟨6197599218665407920225461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4131732812443605280150307 6197599218665407920225461)
                  ·
                    refine ⟨581024926749881992521137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6197599218665407920225461 581024926749881992521137)
                    ·
                      rfl

theorem cell22_1697313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1697313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697313 prefixEnd_1697313 := by exact prefixLift 1697313
  have htrace : WordTrace (prefixWord ++ tailWord_1697313) baseStart_1697313 baseEnd_1697313 := by
    simpa [prefixWord, tailWord_1697313, baseEnd_1697313] using wordTrace_append hprefix tailTrace_1697313
  have hstable : (prefixWord ++ tailWord_1697313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697313).length < 2 ^ (prefixWord ++ tailWord_1697313).sum := by decide
  have hdescent : baseEnd_1697313 < baseStart_1697313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697405 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 5]
def baseStart_1697405 : Nat := 118140960795 + 1697405 * 2 ^ 59
def prefixEnd_1697405 : Nat := 4983230072969 + 3 ^ 40 * 1697405 * 2
def baseEnd_1697405 : Nat := 193685473410008139740285

theorem tailTrace_1697405 : CollatzResearch.WordTrace tailWord_1697405 prefixEnd_1697405 193685473410008139740285 := by
  unfold tailWord_1697405
  simp only [CollatzResearch.WordTrace]
  refine ⟨61909446415599053539493669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41272964277066035692995779 61909446415599053539493669)
  ·
    refine ⟨11608021202924822538655063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61909446415599053539493669 11608021202924822538655063)
    ·
      refine ⟨17412031804387233807982595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11608021202924822538655063 17412031804387233807982595)
      ·
        refine ⟨26118047706580850711973893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17412031804387233807982595 26118047706580850711973893)
        ·
          refine ⟨4897133944983909508495105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26118047706580850711973893 4897133944983909508495105)
          ·
            refine ⟨3672850458737932131371329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897133944983909508495105 3672850458737932131371329)
            ·
              refine ⟨2754637844053449098528497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672850458737932131371329 2754637844053449098528497)
              ·
                refine ⟨2065978383040086823896373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2754637844053449098528497 2065978383040086823896373)
                ·
                  refine ⟨193685473410008139740285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2065978383040086823896373 193685473410008139740285)
                  ·
                    rfl

theorem cell22_1697405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_1697405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697405 prefixEnd_1697405 := by exact prefixLift 1697405
  have htrace : WordTrace (prefixWord ++ tailWord_1697405) baseStart_1697405 baseEnd_1697405 := by
    simpa [prefixWord, tailWord_1697405, baseEnd_1697405] using wordTrace_append hprefix tailTrace_1697405
  have hstable : (prefixWord ++ tailWord_1697405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697405).length < 2 ^ (prefixWord ++ tailWord_1697405).sum := by decide
  have hdescent : baseEnd_1697405 < baseStart_1697405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697409 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1697409 : Nat := 118140960795 + 1697409 * 2 ^ 59
def prefixEnd_1697409 : Nat := 4983230072969 + 3 ^ 40 * 1697409 * 2
def baseEnd_1697409 : Nat := 581057789511769742120843

theorem tailTrace_1697409 : CollatzResearch.WordTrace tailWord_1697409 prefixEnd_1697409 581057789511769742120843 := by
  unfold tailWord_1697409
  simp only [CollatzResearch.WordTrace]
  refine ⟨61909592307584562222639281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41273061538389708148426187 61909592307584562222639281)
  ·
    refine ⟨46432194230688421666979461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61909592307584562222639281 46432194230688421666979461)
    ·
      refine ⟨8706036418254079062558649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46432194230688421666979461 8706036418254079062558649)
      ·
        refine ⟨6529527313690559296918987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8706036418254079062558649 6529527313690559296918987)
        ·
          refine ⟨9794290970535838945378481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529527313690559296918987 9794290970535838945378481)
          ·
            refine ⟨7345718227901879209033861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794290970535838945378481 7345718227901879209033861)
            ·
              refine ⟨1377322167731602351693849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7345718227901879209033861 1377322167731602351693849)
              ·
                refine ⟨1032991625798701763770387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377322167731602351693849 1032991625798701763770387)
                ·
                  refine ⟨1549487438698052645655581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032991625798701763770387 1549487438698052645655581)
                  ·
                    refine ⟨581057789511769742120843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1549487438698052645655581 581057789511769742120843)
                    ·
                      rfl

theorem cell22_1697409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1697409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697409 prefixEnd_1697409 := by exact prefixLift 1697409
  have htrace : WordTrace (prefixWord ++ tailWord_1697409) baseStart_1697409 baseEnd_1697409 := by
    simpa [prefixWord, tailWord_1697409, baseEnd_1697409] using wordTrace_append hprefix tailTrace_1697409
  have hstable : (prefixWord ++ tailWord_1697409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697409).length < 2 ^ (prefixWord ++ tailWord_1697409).sum := by decide
  have hdescent : baseEnd_1697409 < baseStart_1697409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697482 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1697482 : Nat := 118140960795 + 1697482 * 2 ^ 59
def prefixEnd_1697482 : Nat := 4983230072969 + 3 ^ 40 * 1697482 * 2
def baseEnd_1697482 : Nat := 581082778903621885045619

theorem tailTrace_1697482 : CollatzResearch.WordTrace tailWord_1697482 prefixEnd_1697482 581082778903621885045619 := by
  unfold tailWord_1697482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15478063709080023922511675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41274836557546730460031133 15478063709080023922511675)
  ·
    refine ⟨23217095563620035883767513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15478063709080023922511675 23217095563620035883767513)
    ·
      refine ⟨17412821672715026912825635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23217095563620035883767513 17412821672715026912825635)
      ·
        refine ⟨26119232509072540369238453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17412821672715026912825635 26119232509072540369238453)
        ·
          refine ⟨2448678047725550659616105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26119232509072540369238453 2448678047725550659616105)
          ·
            refine ⟨1836508535794162994712079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448678047725550659616105 1836508535794162994712079)
            ·
              refine ⟨2754762803691244492068119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836508535794162994712079 2754762803691244492068119)
              ·
                refine ⟨4132144205536866738102179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754762803691244492068119 4132144205536866738102179)
                ·
                  refine ⟨6198216308305300107153269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4132144205536866738102179 6198216308305300107153269)
                  ·
                    refine ⟨581082778903621885045619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6198216308305300107153269 581082778903621885045619)
                    ·
                      rfl

theorem cell22_1697482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1697482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697482 prefixEnd_1697482 := by exact prefixLift 1697482
  have htrace : WordTrace (prefixWord ++ tailWord_1697482) baseStart_1697482 baseEnd_1697482 := by
    simpa [prefixWord, tailWord_1697482, baseEnd_1697482] using wordTrace_append hprefix tailTrace_1697482
  have hstable : (prefixWord ++ tailWord_1697482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697482).length < 2 ^ (prefixWord ++ tailWord_1697482).sum := by decide
  have hdescent : baseEnd_1697482 < baseStart_1697482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697501 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 4]
def baseStart_1697501 : Nat := 118140960795 + 1697501 * 2 ^ 59
def prefixEnd_1697501 : Nat := 4983230072969 + 3 ^ 40 * 1697501 * 2
def baseEnd_1697501 : Nat := 193696427663970722940187

theorem tailTrace_1697501 : CollatzResearch.WordTrace tailWord_1697501 prefixEnd_1697501 193696427663970722940187 := by
  unfold tailWord_1697501
  simp only [CollatzResearch.WordTrace]
  refine ⟨61912947823251261934988357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41275298548834174623325571 61912947823251261934988357)
  ·
    refine ⟨11608677716859611612810317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61912947823251261934988357 11608677716859611612810317)
    ·
      refine ⟨4353254143822354354803869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11608677716859611612810317 4353254143822354354803869)
      ·
        refine ⟨1632470303933382883051451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4353254143822354354803869 1632470303933382883051451)
        ·
          refine ⟨2448705455900074324577177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632470303933382883051451 2448705455900074324577177)
          ·
            refine ⟨1836529091925055743432883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448705455900074324577177 1836529091925055743432883)
            ·
              refine ⟨2754793637887583615149325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836529091925055743432883 2754793637887583615149325)
              ·
                refine ⟨1033047614207843855680997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2754793637887583615149325 1033047614207843855680997)
                ·
                  refine ⟨193696427663970722940187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033047614207843855680997 193696427663970722940187)
                  ·
                    rfl

theorem cell22_1697501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_1697501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697501 prefixEnd_1697501 := by exact prefixLift 1697501
  have htrace : WordTrace (prefixWord ++ tailWord_1697501) baseStart_1697501 baseEnd_1697501 := by
    simpa [prefixWord, tailWord_1697501, baseEnd_1697501] using wordTrace_append hprefix tailTrace_1697501
  have hstable : (prefixWord ++ tailWord_1697501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697501).length < 2 ^ (prefixWord ++ tailWord_1697501).sum := by decide
  have hdescent : baseEnd_1697501 < baseStart_1697501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697523 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 7]
def baseStart_1697523 : Nat := 118140960795 + 1697523 * 2 ^ 59
def prefixEnd_1697523 : Nat := 4983230072969 + 3 ^ 40 * 1697523 * 2
def baseEnd_1697523 : Nat := 193698938013837148256831

theorem tailTrace_1697523 : CollatzResearch.WordTrace tailWord_1697523 prefixEnd_1697523 193698938013837148256831 := by
  unfold tailWord_1697523
  simp only [CollatzResearch.WordTrace]
  refine ⟨61913750229171559692289223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41275833486114373128192815 61913750229171559692289223)
  ·
    refine ⟨92870625343757339538433835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61913750229171559692289223 92870625343757339538433835)
    ·
      refine ⟨139305938015636009307650753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92870625343757339538433835 139305938015636009307650753)
      ·
        refine ⟨104479453511727006980738065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139305938015636009307650753 104479453511727006980738065)
        ·
          refine ⟨78359590133795255235553549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104479453511727006980738065 78359590133795255235553549)
          ·
            refine ⟨29384846300173220713332581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78359590133795255235553549 29384846300173220713332581)
            ·
              refine ⟨5509658681282478883749859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29384846300173220713332581 5509658681282478883749859)
              ·
                refine ⟨8264488021923718325624789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5509658681282478883749859 8264488021923718325624789)
                ·
                  refine ⟨193698938013837148256831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8264488021923718325624789 193698938013837148256831)
                  ·
                    rfl

theorem cell22_1697523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_1697523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697523 prefixEnd_1697523 := by exact prefixLift 1697523
  have htrace : WordTrace (prefixWord ++ tailWord_1697523) baseStart_1697523 baseEnd_1697523 := by
    simpa [prefixWord, tailWord_1697523, baseEnd_1697523] using wordTrace_append hprefix tailTrace_1697523
  have hstable : (prefixWord ++ tailWord_1697523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697523).length < 2 ^ (prefixWord ++ tailWord_1697523).sum := by decide
  have hdescent : baseEnd_1697523 < baseStart_1697523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697527 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 1, 3]
def baseStart_1697527 : Nat := 118140960795 + 1697527 * 2 ^ 59
def prefixEnd_1697527 : Nat := 4983230072969 + 3 ^ 40 * 1697527 * 2
def baseEnd_1697527 : Nat := 581098183323256767670481

theorem tailTrace_1697527 : CollatzResearch.WordTrace tailWord_1697527 prefixEnd_1697527 581098183323256767670481 := by
  unfold tailWord_1697527
  simp only [CollatzResearch.WordTrace]
  refine ⟨61913896121157068375434835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41275930747438045583623223 61913896121157068375434835)
  ·
    refine ⟨92870844181735602563152253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61913896121157068375434835 92870844181735602563152253)
    ·
      refine ⟨34826566568150850961182095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92870844181735602563152253 34826566568150850961182095)
      ·
        refine ⟨52239849852226276441773143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34826566568150850961182095 52239849852226276441773143)
        ·
          refine ⟨78359774778339414662659715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52239849852226276441773143 78359774778339414662659715)
          ·
            refine ⟨117539662167509121993989573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78359774778339414662659715 117539662167509121993989573)
            ·
              refine ⟨22038686656407960373873045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117539662167509121993989573 22038686656407960373873045)
              ·
                refine ⟨1033063437019123142525299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22038686656407960373873045 1033063437019123142525299)
                ·
                  refine ⟨1549595155528684713787949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033063437019123142525299 1549595155528684713787949)
                  ·
                    refine ⟨581098183323256767670481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1549595155528684713787949 581098183323256767670481)
                    ·
                      rfl

theorem cell22_1697527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_1697527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697527 prefixEnd_1697527 := by exact prefixLift 1697527
  have htrace : WordTrace (prefixWord ++ tailWord_1697527) baseStart_1697527 baseEnd_1697527 := by
    simpa [prefixWord, tailWord_1697527, baseEnd_1697527] using wordTrace_append hprefix tailTrace_1697527
  have hstable : (prefixWord ++ tailWord_1697527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697527).length < 2 ^ (prefixWord ++ tailWord_1697527).sum := by decide
  have hdescent : baseEnd_1697527 < baseStart_1697527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697600 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_1697600 : Nat := 118140960795 + 1697600 * 2 ^ 59
def prefixEnd_1697600 : Nat := 4983230072969 + 3 ^ 40 * 1697600 * 2
def baseEnd_1697600 : Nat := 581123172715108910595257

theorem tailTrace_1697600 : CollatzResearch.WordTrace tailWord_1697600 prefixEnd_1697600 581123172715108910595257 := by
  unfold tailWord_1697600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30958279324946300921421127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41277705766595067895228169 30958279324946300921421127)
  ·
    refine ⟨46437418987419451382131691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30958279324946300921421127 46437418987419451382131691)
    ·
      refine ⟨69656128481129177073197537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46437418987419451382131691 69656128481129177073197537)
      ·
        refine ⟨52242096360846882804898153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69656128481129177073197537 52242096360846882804898153)
        ·
          refine ⟨39181572270635162103673615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52242096360846882804898153 39181572270635162103673615)
          ·
            refine ⟨58772358405952743155510423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39181572270635162103673615 58772358405952743155510423)
            ·
              refine ⟨88158537608929114733265635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58772358405952743155510423 88158537608929114733265635)
              ·
                refine ⟨132237806413393672099898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88158537608929114733265635 132237806413393672099898453)
                ·
                  refine ⟨1549661793906957094920685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 132237806413393672099898453 1549661793906957094920685)
                  ·
                    refine ⟨581123172715108910595257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1549661793906957094920685 581123172715108910595257)
                    ·
                      rfl

theorem cell22_1697600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_1697600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697600 prefixEnd_1697600 := by exact prefixLift 1697600
  have htrace : WordTrace (prefixWord ++ tailWord_1697600) baseStart_1697600 baseEnd_1697600 := by
    simpa [prefixWord, tailWord_1697600, baseEnd_1697600] using wordTrace_append hprefix tailTrace_1697600
  have hstable : (prefixWord ++ tailWord_1697600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697600).length < 2 ^ (prefixWord ++ tailWord_1697600).sum := by decide
  have hdescent : baseEnd_1697600 < baseStart_1697600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697634 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1697634 : Nat := 118140960795 + 1697634 * 2 ^ 59
def prefixEnd_1697634 : Nat := 4983230072969 + 3 ^ 40 * 1697634 * 2
def baseEnd_1697634 : Nat := 581134811609944155245153

theorem tailTrace_1697634 : CollatzResearch.WordTrace tailWord_1697634 prefixEnd_1697634 581134811609944155245153 := by
  unfold tailWord_1697634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15479449682942356412394989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41278532487846283766386637 15479449682942356412394989)
  ·
    refine ⟨5804793631103383654648121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15479449682942356412394989 5804793631103383654648121)
    ·
      refine ⟨4353595223327537740986091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5804793631103383654648121 4353595223327537740986091)
      ·
        refine ⟨6530392834991306611479137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353595223327537740986091 6530392834991306611479137)
        ·
          refine ⟨4897794626243479958609353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6530392834991306611479137 4897794626243479958609353)
          ·
            refine ⟨3673345969682609968957015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897794626243479958609353 3673345969682609968957015)
            ·
              refine ⟨5510018954523914953435523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673345969682609968957015 5510018954523914953435523)
              ·
                refine ⟨8265028431785872430153285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510018954523914953435523 8265028431785872430153285)
                ·
                  refine ⟨1549692830959851080653741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8265028431785872430153285 1549692830959851080653741)
                  ·
                    refine ⟨581134811609944155245153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1549692830959851080653741 581134811609944155245153)
                    ·
                      rfl

theorem cell22_1697634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1697634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697634 prefixEnd_1697634 := by exact prefixLift 1697634
  have htrace : WordTrace (prefixWord ++ tailWord_1697634) baseStart_1697634 baseEnd_1697634 := by
    simpa [prefixWord, tailWord_1697634, baseEnd_1697634] using wordTrace_append hprefix tailTrace_1697634
  have hstable : (prefixWord ++ tailWord_1697634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697634).length < 2 ^ (prefixWord ++ tailWord_1697634).sum := by decide
  have hdescent : baseEnd_1697634 < baseStart_1697634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697692 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_1697692 : Nat := 118140960795 + 1697692 * 2 ^ 59
def prefixEnd_1697692 : Nat := 4983230072969 + 3 ^ 40 * 1697692 * 2
def baseEnd_1697692 : Nat := 193718222065083779098325

theorem tailTrace_1697692 : CollatzResearch.WordTrace tailWord_1697692 prefixEnd_1697692 193718222065083779098325 := by
  unfold tailWord_1697692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30959957082779650777595665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41279942777039534370127553 30959957082779650777595665)
  ·
    refine ⟨23219967812084738083196749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30959957082779650777595665 23219967812084738083196749)
    ·
      refine ⟨8707487929531776781198781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23219967812084738083196749 8707487929531776781198781)
      ·
        refine ⟨3265307973574416292949543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8707487929531776781198781 3265307973574416292949543)
        ·
          refine ⟨4897961960361624439424315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265307973574416292949543 4897961960361624439424315)
          ·
            refine ⟨7346942940542436659136473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4897961960361624439424315 7346942940542436659136473)
            ·
              refine ⟨5510207205406827494352355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7346942940542436659136473 5510207205406827494352355)
              ·
                refine ⟨8265310808110241241528533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510207205406827494352355 8265310808110241241528533)
                ·
                  refine ⟨193718222065083779098325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8265310808110241241528533 193718222065083779098325)
                  ·
                    rfl

theorem cell22_1697692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_1697692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697692 prefixEnd_1697692 := by exact prefixLift 1697692
  have htrace : WordTrace (prefixWord ++ tailWord_1697692) baseStart_1697692 baseEnd_1697692 := by
    simpa [prefixWord, tailWord_1697692, baseEnd_1697692] using wordTrace_append hprefix tailTrace_1697692
  have hstable : (prefixWord ++ tailWord_1697692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697692).length < 2 ^ (prefixWord ++ tailWord_1697692).sum := by decide
  have hdescent : baseEnd_1697692 < baseStart_1697692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697720 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 8]
def baseStart_1697720 : Nat := 118140960795 + 1697720 * 2 ^ 59
def prefixEnd_1697720 : Nat := 4983230072969 + 3 ^ 40 * 1697720 * 2
def baseEnd_1697720 : Nat := 193721417055822865864963

theorem tailTrace_1697720 : CollatzResearch.WordTrace tailWord_1697720 prefixEnd_1697720 193721417055822865864963 := by
  unfold tailWord_1697720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30960467704728931168605307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41280623606305241558140409 30960467704728931168605307)
  ·
    refine ⟨46440701557093396752907961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30960467704728931168605307 46440701557093396752907961)
    ·
      refine ⟨34830526167820047564680971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46440701557093396752907961 34830526167820047564680971)
      ·
        refine ⟨52245789251730071347021457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34830526167820047564680971 52245789251730071347021457)
        ·
          refine ⟨39184341938797553510266093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52245789251730071347021457 39184341938797553510266093)
          ·
            refine ⟨14694128227049082566349785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39184341938797553510266093 14694128227049082566349785)
            ·
              refine ⟨11020596170286811924762339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14694128227049082566349785 11020596170286811924762339)
              ·
                refine ⟨16530894255430217887143509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11020596170286811924762339 16530894255430217887143509)
                ·
                  refine ⟨193721417055822865864963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16530894255430217887143509 193721417055822865864963)
                  ·
                    rfl

theorem cell22_1697720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_1697720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697720 prefixEnd_1697720 := by exact prefixLift 1697720
  have htrace : WordTrace (prefixWord ++ tailWord_1697720) baseStart_1697720 baseEnd_1697720 := by
    simpa [prefixWord, tailWord_1697720, baseEnd_1697720] using wordTrace_append hprefix tailTrace_1697720
  have hstable : (prefixWord ++ tailWord_1697720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697720).length < 2 ^ (prefixWord ++ tailWord_1697720).sum := by decide
  have hdescent : baseEnd_1697720 < baseStart_1697720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697722 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1697722 : Nat := 118140960795 + 1697722 * 2 ^ 59
def prefixEnd_1697722 : Nat := 4983230072969 + 3 ^ 40 * 1697722 * 2
def baseEnd_1697722 : Nat := 581164935808341259044883

theorem tailTrace_1697722 : CollatzResearch.WordTrace tailWord_1697722 prefixEnd_1697722 581164935808341259044883 := by
  unfold tailWord_1697722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480252088862654169695855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41280672236967077785855613 15480252088862654169695855)
  ·
    refine ⟨23220378133293981254543783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15480252088862654169695855 23220378133293981254543783)
    ·
      refine ⟨34830567199940971881815675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23220378133293981254543783 34830567199940971881815675)
      ·
        refine ⟨52245850799911457822723513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34830567199940971881815675 52245850799911457822723513)
        ·
          refine ⟨39184388099933593367042635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52245850799911457822723513 39184388099933593367042635)
          ·
            refine ⟨58776582149900390050563953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39184388099933593367042635 58776582149900390050563953)
            ·
              refine ⟨44082436612425292537922965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58776582149900390050563953 44082436612425292537922965)
              ·
                refine ⟨2066364216207435587715139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44082436612425292537922965 2066364216207435587715139)
                ·
                  refine ⟨3099546324311153381572709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066364216207435587715139 3099546324311153381572709)
                  ·
                    refine ⟨581164935808341259044883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099546324311153381572709 581164935808341259044883)
                    ·
                      rfl

theorem cell22_1697722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1697722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697722 prefixEnd_1697722 := by exact prefixLift 1697722
  have htrace : WordTrace (prefixWord ++ tailWord_1697722) baseStart_1697722 baseEnd_1697722 := by
    simpa [prefixWord, tailWord_1697722, baseEnd_1697722] using wordTrace_append hprefix tailTrace_1697722
  have hstable : (prefixWord ++ tailWord_1697722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697722).length < 2 ^ (prefixWord ++ tailWord_1697722).sum := by decide
  have hdescent : baseEnd_1697722 < baseStart_1697722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697739 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 1, 4]
def baseStart_1697739 : Nat := 118140960795 + 1697739 * 2 ^ 59
def prefixEnd_1697739 : Nat := 4983230072969 + 3 ^ 40 * 1697739 * 2
def baseEnd_1697739 : Nat := 581170755255758881369831

theorem tailTrace_1697739 : CollatzResearch.WordTrace tailWord_1697739 prefixEnd_1697739 581170755255758881369831 := by
  unfold tailWord_1697739
  simp only [CollatzResearch.WordTrace]
  refine ⟨61921628396389028582152271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41281085597592685721434847 61921628396389028582152271)
  ·
    refine ⟨92882442594583542873228407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61921628396389028582152271 92882442594583542873228407)
    ·
      refine ⟨139323663891875314309842611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92882442594583542873228407 139323663891875314309842611)
      ·
        refine ⟨208985495837812971464763917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139323663891875314309842611 208985495837812971464763917)
        ·
          refine ⟨78369560939179864299286469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208985495837812971464763917 78369560939179864299286469)
          ·
            refine ⟨14694292676096224556116213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78369560939179864299286469 14694292676096224556116213)
            ·
              refine ⟨1377589938384021052135895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14694292676096224556116213 1377589938384021052135895)
              ·
                refine ⟨2066384907576031578203843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377589938384021052135895 2066384907576031578203843)
                ·
                  refine ⟨3099577361364047367305765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066384907576031578203843 3099577361364047367305765)
                  ·
                    refine ⟨581170755255758881369831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3099577361364047367305765 581170755255758881369831)
                    ·
                      rfl

theorem cell22_1697739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 4].length) (baseStart_1697739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697739 prefixEnd_1697739 := by exact prefixLift 1697739
  have htrace : WordTrace (prefixWord ++ tailWord_1697739) baseStart_1697739 baseEnd_1697739 := by
    simpa [prefixWord, tailWord_1697739, baseEnd_1697739] using wordTrace_append hprefix tailTrace_1697739
  have hstable : (prefixWord ++ tailWord_1697739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697739).length < 2 ^ (prefixWord ++ tailWord_1697739).sum := by decide
  have hdescent : baseEnd_1697739 < baseStart_1697739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697878 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1697878 : Nat := 118140960795 + 1697878 * 2 ^ 59
def prefixEnd_1697878 : Nat := 4983230072969 + 3 ^ 40 * 1697878 * 2
def baseEnd_1697878 : Nat := 193739445932136284048135

theorem tailTrace_1697878 : CollatzResearch.WordTrace tailWord_1697878 prefixEnd_1697878 193739445932136284048135 := by
  unfold tailWord_1697878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870418633930340957591393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41284465428590303547641525 3870418633930340957591393)
  ·
    refine ⟨2902813975447755718193545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870418633930340957591393 2902813975447755718193545)
    ·
      refine ⟨2177110481585816788645159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2902813975447755718193545 2177110481585816788645159)
      ·
        refine ⟨3265665722378725182967739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177110481585816788645159 3265665722378725182967739)
        ·
          refine ⟨4898498583568087774451609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265665722378725182967739 4898498583568087774451609)
          ·
            refine ⟨3673873937676065830838707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898498583568087774451609 3673873937676065830838707)
            ·
              refine ⟨5510810906514098746258061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673873937676065830838707 5510810906514098746258061)
              ·
                refine ⟨2066554089942787029846773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5510810906514098746258061 2066554089942787029846773)
                ·
                  refine ⟨193739445932136284048135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2066554089942787029846773 193739445932136284048135)
                  ·
                    rfl

theorem cell22_1697878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1697878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697878 prefixEnd_1697878 := by exact prefixLift 1697878
  have htrace : WordTrace (prefixWord ++ tailWord_1697878) baseStart_1697878 baseEnd_1697878 := by
    simpa [prefixWord, tailWord_1697878, baseEnd_1697878] using wordTrace_append hprefix tailTrace_1697878
  have hstable : (prefixWord ++ tailWord_1697878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697878).length < 2 ^ (prefixWord ++ tailWord_1697878).sum := by decide
  have hdescent : baseEnd_1697878 < baseStart_1697878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697904 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_1697904 : Nat := 118140960795 + 1697904 * 2 ^ 59
def prefixEnd_1697904 : Nat := 4983230072969 + 3 ^ 40 * 1697904 * 2
def baseEnd_1697904 : Nat := 581227238127753450994325

theorem tailTrace_1697904 : CollatzResearch.WordTrace tailWord_1697904 prefixEnd_1697904 581227238127753450994325 := by
  unfold tailWord_1697904
  simp only [CollatzResearch.WordTrace]
  refine ⟨30963823220395630880954383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41285097627194174507939177 30963823220395630880954383)
  ·
    refine ⟨46445734830593446321431575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30963823220395630880954383 46445734830593446321431575)
    ·
      refine ⟨69668602245890169482147363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46445734830593446321431575 69668602245890169482147363)
      ·
        refine ⟨104502903368835254223221045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69668602245890169482147363 104502903368835254223221045)
        ·
          refine ⟨9797147190828305083426973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104502903368835254223221045 9797147190828305083426973)
          ·
            refine ⟨3673930196560614406285115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9797147190828305083426973 3673930196560614406285115)
            ·
              refine ⟨5510895294840921609427673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673930196560614406285115 5510895294840921609427673)
              ·
                refine ⟨4133171471130691207070755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5510895294840921609427673 4133171471130691207070755)
                ·
                  refine ⟨6199757206696036810606133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4133171471130691207070755 6199757206696036810606133)
                  ·
                    refine ⟨581227238127753450994325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6199757206696036810606133 581227238127753450994325)
                    ·
                      rfl

theorem cell22_1697904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_1697904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697904 prefixEnd_1697904 := by exact prefixLift 1697904
  have htrace : WordTrace (prefixWord ++ tailWord_1697904) baseStart_1697904 baseEnd_1697904 := by
    simpa [prefixWord, tailWord_1697904, baseEnd_1697904] using wordTrace_append hprefix tailTrace_1697904
  have hstable : (prefixWord ++ tailWord_1697904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697904).length < 2 ^ (prefixWord ++ tailWord_1697904).sum := by decide
  have hdescent : baseEnd_1697904 < baseStart_1697904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697917 : List Nat := [1, 4, 1, 1, 3, 12]
def baseStart_1697917 : Nat := 118140960795 + 1697917 * 2 ^ 59
def prefixEnd_1697917 : Nat := 4983230072969 + 3 ^ 40 * 1697917 * 2
def baseEnd_1697917 : Nat := 7175699855474391980485

theorem tailTrace_1697917 : CollatzResearch.WordTrace tailWord_1697917 prefixEnd_1697917 7175699855474391980485 := by
  unfold tailWord_1697917
  simp only [CollatzResearch.WordTrace]
  refine ⟨61928120589744164982132005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41285413726496109988088003 61928120589744164982132005)
  ·
    refine ⟨11611522610577030934149751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61928120589744164982132005 11611522610577030934149751)
    ·
      refine ⟨17417283915865546401224627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11611522610577030934149751 17417283915865546401224627)
      ·
        refine ⟨26125925873798319601836941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417283915865546401224627 26125925873798319601836941)
        ·
          refine ⟨9797222202674369850688853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26125925873798319601836941 9797222202674369850688853)
          ·
            refine ⟨7175699855474391980485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9797222202674369850688853 7175699855474391980485)
            ·
              rfl

theorem cell22_1697917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 12].length) (baseStart_1697917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697917 prefixEnd_1697917 := by exact prefixLift 1697917
  have htrace : WordTrace (prefixWord ++ tailWord_1697917) baseStart_1697917 baseEnd_1697917 := by
    simpa [prefixWord, tailWord_1697917, baseEnd_1697917] using wordTrace_append hprefix tailTrace_1697917
  have hstable : (prefixWord ++ tailWord_1697917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697917).length < 2 ^ (prefixWord ++ tailWord_1697917).sum := by decide
  have hdescent : baseEnd_1697917 < baseStart_1697917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697923 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 4]
def baseStart_1697923 : Nat := 118140960795 + 1697923 * 2 ^ 59
def prefixEnd_1697923 : Nat := 4983230072969 + 3 ^ 40 * 1697923 * 2
def baseEnd_1697923 : Nat := 193744580738681244923089

theorem tailTrace_1697923 : CollatzResearch.WordTrace tailWord_1697923 prefixEnd_1697923 193744580738681244923089 := by
  unfold tailWord_1697923
  simp only [CollatzResearch.WordTrace]
  refine ⟨61928339427722428006850423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41285559618481618671233615 61928339427722428006850423)
  ·
    refine ⟨92892509141583642010275635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61928339427722428006850423 92892509141583642010275635)
    ·
      refine ⟨139338763712375463015413453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92892509141583642010275635 139338763712375463015413453)
      ·
        refine ⟨52252036392140798630780045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139338763712375463015413453 52252036392140798630780045)
        ·
          refine ⟨19594513647052799486542517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52252036392140798630780045 19594513647052799486542517)
          ·
            refine ⟨1836985654411199951863361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19594513647052799486542517 1836985654411199951863361)
            ·
              refine ⟨1377739240808399963897521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836985654411199951863361 1377739240808399963897521)
              ·
                refine ⟨1033304430606299972923141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377739240808399963897521 1033304430606299972923141)
                ·
                  refine ⟨193744580738681244923089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033304430606299972923141 193744580738681244923089)
                  ·
                    rfl

theorem cell22_1697923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 4].length) (baseStart_1697923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697923 prefixEnd_1697923 := by exact prefixLift 1697923
  have htrace : WordTrace (prefixWord ++ tailWord_1697923) baseStart_1697923 baseEnd_1697923 := by
    simpa [prefixWord, tailWord_1697923, baseEnd_1697923] using wordTrace_append hprefix tailTrace_1697923
  have hstable : (prefixWord ++ tailWord_1697923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697923).length < 2 ^ (prefixWord ++ tailWord_1697923).sum := by decide
  have hdescent : baseEnd_1697923 < baseStart_1697923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697932 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1697932 : Nat := 118140960795 + 1697932 * 2 ^ 59
def prefixEnd_1697932 : Nat := 4983230072969 + 3 ^ 40 * 1697932 * 2
def baseEnd_1697932 : Nat := 581236823099970711294239

theorem tailTrace_1697932 : CollatzResearch.WordTrace tailWord_1697932 prefixEnd_1697932 581236823099970711294239 := by
  unfold tailWord_1697932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964333842344911271964025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41285778456459881695952033 30964333842344911271964025)
  ·
    refine ⟨23223250381758683453973019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30964333842344911271964025 23223250381758683453973019)
    ·
      refine ⟨34834875572638025180959529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23223250381758683453973019 34834875572638025180959529)
      ·
        refine ⟨26126156679478518885719647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34834875572638025180959529 26126156679478518885719647)
        ·
          refine ⟨39189235019217778328579471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126156679478518885719647 39189235019217778328579471)
          ·
            refine ⟨58783852528826667492869207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39189235019217778328579471 58783852528826667492869207)
            ·
              refine ⟨88175778793240001239303811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58783852528826667492869207 88175778793240001239303811)
              ·
                refine ⟨132263668189860001858955717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88175778793240001239303811 132263668189860001858955717)
                ·
                  refine ⟨24799437785598750348554197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132263668189860001858955717 24799437785598750348554197)
                  ·
                    refine ⟨581236823099970711294239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24799437785598750348554197 581236823099970711294239)
                    ·
                      rfl

theorem cell22_1697932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1697932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697932 prefixEnd_1697932 := by exact prefixLift 1697932
  have htrace : WordTrace (prefixWord ++ tailWord_1697932) baseStart_1697932 baseEnd_1697932 := by
    simpa [prefixWord, tailWord_1697932, baseEnd_1697932] using wordTrace_append hprefix tailTrace_1697932
  have hstable : (prefixWord ++ tailWord_1697932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697932).length < 2 ^ (prefixWord ++ tailWord_1697932).sum := by decide
  have hdescent : baseEnd_1697932 < baseStart_1697932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697947 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_1697947 : Nat := 118140960795 + 1697947 * 2 ^ 59
def prefixEnd_1697947 : Nat := 4983230072969 + 3 ^ 40 * 1697947 * 2
def baseEnd_1697947 : Nat := 581241957906515672169193

theorem tailTrace_1697947 : CollatzResearch.WordTrace tailWord_1697947 prefixEnd_1697947 581241957906515672169193 := by
  unfold tailWord_1697947
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929214779635480105724095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41286143186423653403816063 61929214779635480105724095)
  ·
    refine ⟨92893822169453220158586143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61929214779635480105724095 92893822169453220158586143)
    ·
      refine ⟨139340733254179830237879215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92893822169453220158586143 139340733254179830237879215)
      ·
        refine ⟨209011099881269745356818823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139340733254179830237879215 209011099881269745356818823)
        ·
          refine ⟨313516649821904618035228235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209011099881269745356818823 313516649821904618035228235)
          ·
            refine ⟨470274974732856927052842353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313516649821904618035228235 470274974732856927052842353)
            ·
              refine ⟨352706231049642695289631765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470274974732856927052842353 352706231049642695289631765)
              ·
                refine ⟨16533104580452001341701489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 352706231049642695289631765 16533104580452001341701489)
                ·
                  refine ⟨12399828435339001006276117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16533104580452001341701489 12399828435339001006276117)
                  ·
                    refine ⟨581241957906515672169193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12399828435339001006276117 581241957906515672169193)
                    ·
                      rfl

theorem cell22_1697947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_1697947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697947 prefixEnd_1697947 := by exact prefixLift 1697947
  have htrace : WordTrace (prefixWord ++ tailWord_1697947) baseStart_1697947 baseEnd_1697947 := by
    simpa [prefixWord, tailWord_1697947, baseEnd_1697947] using wordTrace_append hprefix tailTrace_1697947
  have hstable : (prefixWord ++ tailWord_1697947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697947).length < 2 ^ (prefixWord ++ tailWord_1697947).sum := by decide
  have hdescent : baseEnd_1697947 < baseStart_1697947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697951 : List Nat := [1, 1, 2, 6, 1, 2, 3, 6]
def baseStart_1697951 : Nat := 118140960795 + 1697951 * 2 ^ 59
def prefixEnd_1697951 : Nat := 4983230072969 + 3 ^ 40 * 1697951 * 2
def baseEnd_1697951 : Nat := 64582591909806777229909

theorem tailTrace_1697951 : CollatzResearch.WordTrace tailWord_1697951 prefixEnd_1697951 64582591909806777229909 := by
  unfold tailWord_1697951
  simp only [CollatzResearch.WordTrace]
  refine ⟨61929360671620988788869707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41286240447747325859246471 61929360671620988788869707)
  ·
    refine ⟨92894041007431483183304561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61929360671620988788869707 92894041007431483183304561)
    ·
      refine ⟨69670530755573612387478421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92894041007431483183304561 69670530755573612387478421)
      ·
        refine ⟨3265806129167513080663051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69670530755573612387478421 3265806129167513080663051)
        ·
          refine ⟨4898709193751269620994577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265806129167513080663051 4898709193751269620994577)
          ·
            refine ⟨3674031895313452215745933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898709193751269620994577 3674031895313452215745933)
            ·
              refine ⟨1377761960742544580904725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3674031895313452215745933 1377761960742544580904725)
              ·
                refine ⟨64582591909806777229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1377761960742544580904725 64582591909806777229909)
                ·
                  rfl

theorem cell22_1697951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 6].length) (baseStart_1697951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697951 prefixEnd_1697951 := by exact prefixLift 1697951
  have htrace : WordTrace (prefixWord ++ tailWord_1697951) baseStart_1697951 baseEnd_1697951 := by
    simpa [prefixWord, tailWord_1697951, baseEnd_1697951] using wordTrace_append hprefix tailTrace_1697951
  have hstable : (prefixWord ++ tailWord_1697951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697951).length < 2 ^ (prefixWord ++ tailWord_1697951).sum := by decide
  have hdescent : baseEnd_1697951 < baseStart_1697951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697972 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1697972 : Nat := 118140960795 + 1697972 * 2 ^ 59
def prefixEnd_1697972 : Nat := 4983230072969 + 3 ^ 40 * 1697972 * 2
def baseEnd_1697972 : Nat := 581250515917423940294117

theorem tailTrace_1697972 : CollatzResearch.WordTrace tailWord_1697972 prefixEnd_1697972 581250515917423940294117 := by
  unfold tailWord_1697972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30965063302272454687692085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41286751069696606250256113 30965063302272454687692085)
  ·
    refine ⟨2902974684588042626971133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30965063302272454687692085 2902974684588042626971133)
    ·
      refine ⟨1088615506720515985114175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2902974684588042626971133 1088615506720515985114175)
      ·
        refine ⟨1632923260080773977671263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088615506720515985114175 1632923260080773977671263)
        ·
          refine ⟨2449384890121160966506895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632923260080773977671263 2449384890121160966506895)
          ·
            refine ⟨3674077335181741449760343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449384890121160966506895 3674077335181741449760343)
            ·
              refine ⟨5511116002772612174640515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674077335181741449760343 5511116002772612174640515)
              ·
                refine ⟨8266674004158918261960773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511116002772612174640515 8266674004158918261960773)
                ·
                  refine ⟨1550001375779797174117645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8266674004158918261960773 1550001375779797174117645)
                  ·
                    refine ⟨581250515917423940294117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550001375779797174117645 581250515917423940294117)
                    ·
                      rfl

theorem cell22_1697972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1697972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697972 prefixEnd_1697972 := by exact prefixLift 1697972
  have htrace : WordTrace (prefixWord ++ tailWord_1697972) baseStart_1697972 baseEnd_1697972 := by
    simpa [prefixWord, tailWord_1697972, baseEnd_1697972] using wordTrace_append hprefix tailTrace_1697972
  have hstable : (prefixWord ++ tailWord_1697972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697972).length < 2 ^ (prefixWord ++ tailWord_1697972).sum := by decide
  have hdescent : baseEnd_1697972 < baseStart_1697972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697994 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1697994 : Nat := 118140960795 + 1697994 * 2 ^ 59
def prefixEnd_1697994 : Nat := 4983230072969 + 3 ^ 40 * 1697994 * 2
def baseEnd_1697994 : Nat := 581258046967023216244049

theorem tailTrace_1697994 : CollatzResearch.WordTrace tailWord_1697994 prefixEnd_1697994 581258046967023216244049 := by
  unfold tailWord_1697994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15482732252616301783171259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41287286006976804755123357 15482732252616301783171259)
  ·
    refine ⟨23224098378924452674756889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15482732252616301783171259 23224098378924452674756889)
    ·
      refine ⟨17418073784193339506067667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23224098378924452674756889 17418073784193339506067667)
      ·
        refine ⟨26127110676290009259101501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418073784193339506067667 26127110676290009259101501)
        ·
          refine ⟨9797666503608753472163063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26127110676290009259101501 9797666503608753472163063)
          ·
            refine ⟨14696499755413130208244595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797666503608753472163063 14696499755413130208244595)
            ·
              refine ⟨22044749633119695312366893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696499755413130208244595 22044749633119695312366893)
              ·
                refine ⟨8266781112419885742137585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22044749633119695312366893 8266781112419885742137585)
                ·
                  refine ⟨6200085834314914306603189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8266781112419885742137585 6200085834314914306603189)
                  ·
                    refine ⟨581258046967023216244049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6200085834314914306603189 581258046967023216244049)
                    ·
                      rfl

theorem cell22_1697994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1697994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1697994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1697994 prefixEnd_1697994 := by exact prefixLift 1697994
  have htrace : WordTrace (prefixWord ++ tailWord_1697994) baseStart_1697994 baseEnd_1697994 := by
    simpa [prefixWord, tailWord_1697994, baseEnd_1697994] using wordTrace_append hprefix tailTrace_1697994
  have hstable : (prefixWord ++ tailWord_1697994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697994).length < 2 ^ (prefixWord ++ tailWord_1697994).sum := by decide
  have hdescent : baseEnd_1697994 < baseStart_1697994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698009 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_1698009 : Nat := 118140960795 + 1698009 * 2 ^ 59
def prefixEnd_1698009 : Nat := 4983230072969 + 3 ^ 40 * 1698009 * 2
def baseEnd_1698009 : Nat := 581263181773568177119003

theorem tailTrace_1698009 : CollatzResearch.WordTrace tailWord_1698009 prefixEnd_1698009 581263181773568177119003 := by
  unfold tailWord_1698009
  simp only [CollatzResearch.WordTrace]
  refine ⟨61931476105410864694481081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41287650736940576462987387 61931476105410864694481081)
  ·
    refine ⟨46448607079058148520860811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61931476105410864694481081 46448607079058148520860811)
    ·
      refine ⟨69672910618587222781291217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46448607079058148520860811 69672910618587222781291217)
      ·
        refine ⟨52254682963940417085968413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69672910618587222781291217 52254682963940417085968413)
        ·
          refine ⟨19595506111477656407238155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52254682963940417085968413 19595506111477656407238155)
          ·
            refine ⟨29393259167216484610857233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19595506111477656407238155 29393259167216484610857233)
            ·
              refine ⟨22044944375412363458142925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29393259167216484610857233 22044944375412363458142925)
              ·
                refine ⟨8266854140779636296803597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22044944375412363458142925 8266854140779636296803597)
                ·
                  refine ⟨3100070302792363611301349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8266854140779636296803597 3100070302792363611301349)
                  ·
                    refine ⟨581263181773568177119003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100070302792363611301349 581263181773568177119003)
                    ·
                      rfl

theorem cell22_1698009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_1698009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698009 prefixEnd_1698009 := by exact prefixLift 1698009
  have htrace : WordTrace (prefixWord ++ tailWord_1698009) baseStart_1698009 baseEnd_1698009 := by
    simpa [prefixWord, tailWord_1698009, baseEnd_1698009] using wordTrace_append hprefix tailTrace_1698009
  have hstable : (prefixWord ++ tailWord_1698009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698009).length < 2 ^ (prefixWord ++ tailWord_1698009).sum := by decide
  have hdescent : baseEnd_1698009 < baseStart_1698009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698026 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1698026 : Nat := 118140960795 + 1698026 * 2 ^ 59
def prefixEnd_1698026 : Nat := 4983230072969 + 3 ^ 40 * 1698026 * 2
def baseEnd_1698026 : Nat := 581269001220985799443951

theorem tailTrace_1698026 : CollatzResearch.WordTrace tailWord_1698026 prefixEnd_1698026 581269001220985799443951 := by
  unfold tailWord_1698026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15483024036587319149462483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41288064097566184398566621 15483024036587319149462483)
  ·
    refine ⟨23224536054880978724193725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15483024036587319149462483 23224536054880978724193725)
    ·
      refine ⟨8709201020580367021572647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23224536054880978724193725 8709201020580367021572647)
      ·
        refine ⟨13063801530870550532358971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8709201020580367021572647 13063801530870550532358971)
        ·
          refine ⟨19595702296305825798538457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13063801530870550532358971 19595702296305825798538457)
          ·
            refine ⟨14696776722229369348903843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19595702296305825798538457 14696776722229369348903843)
            ·
              refine ⟨22045165083344054023355765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696776722229369348903843 22045165083344054023355765)
              ·
                refine ⟨2066734226563505064689603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22045165083344054023355765 2066734226563505064689603)
                ·
                  refine ⟨3100101339845257597034405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2066734226563505064689603 3100101339845257597034405)
                  ·
                    refine ⟨581269001220985799443951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100101339845257597034405 581269001220985799443951)
                    ·
                      rfl

theorem cell22_1698026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1698026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698026 prefixEnd_1698026 := by exact prefixLift 1698026
  have htrace : WordTrace (prefixWord ++ tailWord_1698026) baseStart_1698026 baseEnd_1698026 := by
    simpa [prefixWord, tailWord_1698026, baseEnd_1698026] using wordTrace_append hprefix tailTrace_1698026
  have hstable : (prefixWord ++ tailWord_1698026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698026).length < 2 ^ (prefixWord ++ tailWord_1698026).sum := by decide
  have hdescent : baseEnd_1698026 < baseStart_1698026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698069 : List Nat := [1, 3, 2, 1, 2, 1, 4, 8]
def baseStart_1698069 : Nat := 118140960795 + 1698069 * 2 ^ 59
def prefixEnd_1698069 : Nat := 4983230072969 + 3 ^ 40 * 1698069 * 2
def baseEnd_1698069 : Nat := 64587080111083113402091

theorem tailTrace_1698069 : CollatzResearch.WordTrace tailWord_1698069 prefixEnd_1698069 64587080111083113402091 := by
  unfold tailWord_1698069
  simp only [CollatzResearch.WordTrace]
  refine ⟨61933664485193494941665261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41289109656795663294443507 61933664485193494941665261)
  ·
    refine ⟨23225124181947560603124473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61933664485193494941665261 23225124181947560603124473)
    ·
      refine ⟨17418843136460670452343355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23225124181947560603124473 17418843136460670452343355)
      ·
        refine ⟨26128264704691005678515033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17418843136460670452343355 26128264704691005678515033)
        ·
          refine ⟨19596198528518254258886275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26128264704691005678515033 19596198528518254258886275)
          ·
            refine ⟨29394297792777381388329413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19596198528518254258886275 29394297792777381388329413)
            ·
              refine ⟨5511430836145759010311765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29394297792777381388329413 5511430836145759010311765)
              ·
                refine ⟨64587080111083113402091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5511430836145759010311765 64587080111083113402091)
                ·
                  rfl

theorem cell22_1698069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 8].length) (baseStart_1698069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698069 prefixEnd_1698069 := by exact prefixLift 1698069
  have htrace : WordTrace (prefixWord ++ tailWord_1698069) baseStart_1698069 baseEnd_1698069 := by
    simpa [prefixWord, tailWord_1698069, baseEnd_1698069] using wordTrace_append hprefix tailTrace_1698069
  have hstable : (prefixWord ++ tailWord_1698069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698069).length < 2 ^ (prefixWord ++ tailWord_1698069).sum := by decide
  have hdescent : baseEnd_1698069 < baseStart_1698069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698071 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1698071 : Nat := 118140960795 + 1698071 * 2 ^ 59
def prefixEnd_1698071 : Nat := 4983230072969 + 3 ^ 40 * 1698071 * 2
def baseEnd_1698071 : Nat := 581284405640620682068813

theorem tailTrace_1698071 : CollatzResearch.WordTrace tailWord_1698071 prefixEnd_1698071 581284405640620682068813 := by
  unfold tailWord_1698071
  simp only [CollatzResearch.WordTrace]
  refine ⟨61933737431186249283238067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41289158287457499522158711 61933737431186249283238067)
  ·
    refine ⟨92900606146779373924857101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61933737431186249283238067 92900606146779373924857101)
    ·
      refine ⟨34837727305042265221821413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92900606146779373924857101 34837727305042265221821413)
      ·
        refine ⟨6532073869695424729091515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34837727305042265221821413 6532073869695424729091515)
        ·
          refine ⟨9798110804543137093637273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532073869695424729091515 9798110804543137093637273)
          ·
            refine ⟨7348583103407352820227955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9798110804543137093637273 7348583103407352820227955)
            ·
              refine ⟨11022874655111029230341933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7348583103407352820227955 11022874655111029230341933)
              ·
                refine ⟨4133577995666635961378225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11022874655111029230341933 4133577995666635961378225)
                ·
                  refine ⟨3100183496749976971033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4133577995666635961378225 3100183496749976971033669)
                  ·
                    refine ⟨581284405640620682068813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100183496749976971033669 581284405640620682068813)
                    ·
                      rfl

theorem cell22_1698071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1698071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698071 prefixEnd_1698071 := by exact prefixLift 1698071
  have htrace : WordTrace (prefixWord ++ tailWord_1698071) baseStart_1698071 baseEnd_1698071 := by
    simpa [prefixWord, tailWord_1698071, baseEnd_1698071] using wordTrace_append hprefix tailTrace_1698071
  have hstable : (prefixWord ++ tailWord_1698071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698071).length < 2 ^ (prefixWord ++ tailWord_1698071).sum := by decide
  have hdescent : baseEnd_1698071 < baseStart_1698071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698099 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_1698099 : Nat := 118140960795 + 1698099 * 2 ^ 59
def prefixEnd_1698099 : Nat := 4983230072969 + 3 ^ 40 * 1698099 * 2
def baseEnd_1698099 : Nat := 581293990612837942368727

theorem tailTrace_1698099 : CollatzResearch.WordTrace tailWord_1698099 prefixEnd_1698099 581293990612837942368727 := by
  unfold tailWord_1698099
  simp only [CollatzResearch.WordTrace]
  refine ⟨61934758675084810065257351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41289839116723206710171567 61934758675084810065257351)
  ·
    refine ⟨92902138012627215097886027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61934758675084810065257351 92902138012627215097886027)
    ·
      refine ⟨139353207018940822646829041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92902138012627215097886027 139353207018940822646829041)
      ·
        refine ⟨104514905264205616985121781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139353207018940822646829041 104514905264205616985121781)
        ·
          refine ⟨9798272368519276592355167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104514905264205616985121781 9798272368519276592355167)
          ·
            refine ⟨14697408552778914888532751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798272368519276592355167 14697408552778914888532751)
            ·
              refine ⟨22046112829168372332799127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14697408552778914888532751 22046112829168372332799127)
              ·
                refine ⟨33069169243752558499198691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22046112829168372332799127 33069169243752558499198691)
                ·
                  refine ⟨49603753865628837748798037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33069169243752558499198691 49603753865628837748798037)
                  ·
                    refine ⟨581293990612837942368727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49603753865628837748798037 581293990612837942368727)
                    ·
                      rfl

theorem cell22_1698099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_1698099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698099 prefixEnd_1698099 := by exact prefixLift 1698099
  have htrace : WordTrace (prefixWord ++ tailWord_1698099) baseStart_1698099 baseEnd_1698099 := by
    simpa [prefixWord, tailWord_1698099, baseEnd_1698099] using wordTrace_append hprefix tailTrace_1698099
  have hstable : (prefixWord ++ tailWord_1698099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698099).length < 2 ^ (prefixWord ++ tailWord_1698099).sum := by decide
  have hdescent : baseEnd_1698099 < baseStart_1698099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698135 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 1, 3]
def baseStart_1698135 : Nat := 118140960795 + 1698135 * 2 ^ 59
def prefixEnd_1698135 : Nat := 4983230072969 + 3 ^ 40 * 1698135 * 2
def baseEnd_1698135 : Nat := 581306314148545848468617

theorem tailTrace_1698135 : CollatzResearch.WordTrace tailWord_1698135 prefixEnd_1698135 581306314148545848468617 := by
  unfold tailWord_1698135
  simp only [CollatzResearch.WordTrace]
  refine ⟨61936071702954388213567859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41290714468636258809045239 61936071702954388213567859)
  ·
    refine ⟨92904107554431582320351789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61936071702954388213567859 92904107554431582320351789)
    ·
      refine ⟨34839040332911843370131921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92904107554431582320351789 34839040332911843370131921)
      ·
        refine ⟨26129280249683882527598941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34839040332911843370131921 26129280249683882527598941)
        ·
          refine ⟨9798480093631455947849603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26129280249683882527598941 9798480093631455947849603)
          ·
            refine ⟨14697720140447183921774405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798480093631455947849603 14697720140447183921774405)
            ·
              refine ⟨2755822526333846985332701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14697720140447183921774405 2755822526333846985332701)
              ·
                refine ⟨1033433447375192619499763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755822526333846985332701 1033433447375192619499763)
                ·
                  refine ⟨1550150171062788929249645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033433447375192619499763 1550150171062788929249645)
                  ·
                    refine ⟨581306314148545848468617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550150171062788929249645 581306314148545848468617)
                    ·
                      rfl

theorem cell22_1698135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_1698135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698135 prefixEnd_1698135 := by exact prefixLift 1698135
  have htrace : WordTrace (prefixWord ++ tailWord_1698135) baseStart_1698135 baseEnd_1698135 := by
    simpa [prefixWord, tailWord_1698135, baseEnd_1698135] using wordTrace_append hprefix tailTrace_1698135
  have hstable : (prefixWord ++ tailWord_1698135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698135).length < 2 ^ (prefixWord ++ tailWord_1698135).sum := by decide
  have hdescent : baseEnd_1698135 < baseStart_1698135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698165 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 5]
def baseStart_1698165 : Nat := 118140960795 + 1698165 * 2 ^ 59
def prefixEnd_1698165 : Nat := 4983230072969 + 3 ^ 40 * 1698165 * 2
def baseEnd_1698165 : Nat := 193772194587211923406175

theorem tailTrace_1698165 : CollatzResearch.WordTrace tailWord_1698165 prefixEnd_1698165 193772194587211923406175 := by
  unfold tailWord_1698165
  simp only [CollatzResearch.WordTrace]
  refine ⟨61937165892845703337159949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41291443928563802224773299 61937165892845703337159949)
  ·
    refine ⟨23226437209817138751434981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61937165892845703337159949 23226437209817138751434981)
    ·
      refine ⟨4354956976840713515894059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23226437209817138751434981 4354956976840713515894059)
      ·
        refine ⟨6532435465261070273841089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354956976840713515894059 6532435465261070273841089)
        ·
          refine ⟨4899326598945802705380817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6532435465261070273841089 4899326598945802705380817)
          ·
            refine ⟨3674494949209352029035613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899326598945802705380817 3674494949209352029035613)
            ·
              refine ⟨1377935605953507010888355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3674494949209352029035613 1377935605953507010888355)
              ·
                refine ⟨2066903408930260516332533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377935605953507010888355 2066903408930260516332533)
                ·
                  refine ⟨193772194587211923406175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2066903408930260516332533 193772194587211923406175)
                  ·
                    rfl

theorem cell22_1698165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_1698165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698165 prefixEnd_1698165 := by exact prefixLift 1698165
  have htrace : WordTrace (prefixWord ++ tailWord_1698165) baseStart_1698165 baseEnd_1698165 := by
    simpa [prefixWord, tailWord_1698165, baseEnd_1698165] using wordTrace_append hprefix tailTrace_1698165
  have hstable : (prefixWord ++ tailWord_1698165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698165).length < 2 ^ (prefixWord ++ tailWord_1698165).sum := by decide
  have hdescent : baseEnd_1698165 < baseStart_1698165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698186 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1698186 : Nat := 118140960795 + 1698186 * 2 ^ 59
def prefixEnd_1698186 : Nat := 4983230072969 + 3 ^ 40 * 1698186 * 2
def baseEnd_1698186 : Nat := 581323772490798715443461

theorem tailTrace_1698186 : CollatzResearch.WordTrace tailWord_1698186 prefixEnd_1698186 581323772490798715443461 := by
  unfold tailWord_1698186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15484482956442405980918603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41291954550513082615782941 15484482956442405980918603)
  ·
    refine ⟨23226724434663608971377905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15484482956442405980918603 23226724434663608971377905)
    ·
      refine ⟨17420043325997706728533429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23226724434663608971377905 17420043325997706728533429)
      ·
        refine ⟨1633129061812285005800009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17420043325997706728533429 1633129061812285005800009)
        ·
          refine ⟨1224846796359213754350007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633129061812285005800009 1224846796359213754350007)
          ·
            refine ⟨1837270194538820631525011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224846796359213754350007 1837270194538820631525011)
            ·
              refine ⟨2755905291808230947287517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837270194538820631525011 2755905291808230947287517)
              ·
                refine ⟨1033464484428086605232819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755905291808230947287517 1033464484428086605232819)
                ·
                  refine ⟨1550196726642129907849229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033464484428086605232819 1550196726642129907849229)
                  ·
                    refine ⟨581323772490798715443461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550196726642129907849229 581323772490798715443461)
                    ·
                      rfl

theorem cell22_1698186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1698186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698186 prefixEnd_1698186 := by exact prefixLift 1698186
  have htrace : WordTrace (prefixWord ++ tailWord_1698186) baseStart_1698186 baseEnd_1698186 := by
    simpa [prefixWord, tailWord_1698186, baseEnd_1698186] using wordTrace_append hprefix tailTrace_1698186
  have hstable : (prefixWord ++ tailWord_1698186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698186).length < 2 ^ (prefixWord ++ tailWord_1698186).sum := by decide
  have hdescent : baseEnd_1698186 < baseStart_1698186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698208 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_1698208 : Nat := 118140960795 + 1698208 * 2 ^ 59
def prefixEnd_1698208 : Nat := 4983230072969 + 3 ^ 40 * 1698208 * 2
def baseEnd_1698208 : Nat := 581331303540397991393393

theorem tailTrace_1698208 : CollatzResearch.WordTrace tailWord_1698208 prefixEnd_1698208 581331303540397991393393 := by
  unfold tailWord_1698208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30969367115844960840487639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41292489487793281120650185 30969367115844960840487639)
  ·
    refine ⟨46454050673767441260731459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30969367115844960840487639 46454050673767441260731459)
    ·
      refine ⟨69681076010651161891097189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46454050673767441260731459 69681076010651161891097189)
      ·
        refine ⟨13065201751997092854580723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69681076010651161891097189 13065201751997092854580723)
        ·
          refine ⟨19597802627995639281871085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13065201751997092854580723 19597802627995639281871085)
          ·
            refine ⟨7349175985498364730701657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19597802627995639281871085 7349175985498364730701657)
            ·
              refine ⟨5511881989123773548026243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7349175985498364730701657 5511881989123773548026243)
              ·
                refine ⟨8267822983685660322039365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5511881989123773548026243 8267822983685660322039365)
                ·
                  refine ⟨1550216809441061310382381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8267822983685660322039365 1550216809441061310382381)
                  ·
                    refine ⟨581331303540397991393393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550216809441061310382381 581331303540397991393393)
                    ·
                      rfl

theorem cell22_1698208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_1698208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698208 prefixEnd_1698208 := by exact prefixLift 1698208
  have htrace : WordTrace (prefixWord ++ tailWord_1698208) baseStart_1698208 baseEnd_1698208 := by
    simpa [prefixWord, tailWord_1698208, baseEnd_1698208] using wordTrace_append hprefix tailTrace_1698208
  have hstable : (prefixWord ++ tailWord_1698208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698208).length < 2 ^ (prefixWord ++ tailWord_1698208).sum := by decide
  have hdescent : baseEnd_1698208 < baseStart_1698208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698225 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_1698225 : Nat := 118140960795 + 1698225 * 2 ^ 59
def prefixEnd_1698225 : Nat := 4983230072969 + 3 ^ 40 * 1698225 * 2
def baseEnd_1698225 : Nat := 581337122987815613718341

theorem tailTrace_1698225 : CollatzResearch.WordTrace tailWord_1698225 prefixEnd_1698225 581337122987815613718341 := by
  unfold tailWord_1698225
  simp only [CollatzResearch.WordTrace]
  refine ⟨61939354272628333584344129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41292902848418889056229419 61939354272628333584344129)
  ·
    refine ⟨46454515704471250188258097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61939354272628333584344129 46454515704471250188258097)
    ·
      refine ⟨34840886778353437641193573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46454515704471250188258097 34840886778353437641193573)
      ·
        refine ⟨6532666270941269557723795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34840886778353437641193573 6532666270941269557723795)
        ·
          refine ⟨9798999406411904336585693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532666270941269557723795 9798999406411904336585693)
          ·
            refine ⟨3674624777404464126219635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9798999406411904336585693 3674624777404464126219635)
            ·
              refine ⟨5511937166106696189329453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674624777404464126219635 5511937166106696189329453)
              ·
                refine ⟨2066976437290011070998545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511937166106696189329453 2066976437290011070998545)
                ·
                  refine ⟨1550232327967508303248909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2066976437290011070998545 1550232327967508303248909)
                  ·
                    refine ⟨581337122987815613718341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550232327967508303248909 581337122987815613718341)
                    ·
                      rfl

theorem cell22_1698225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_1698225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698225 prefixEnd_1698225 := by exact prefixLift 1698225
  have htrace : WordTrace (prefixWord ++ tailWord_1698225) baseStart_1698225 baseEnd_1698225 := by
    simpa [prefixWord, tailWord_1698225, baseEnd_1698225] using wordTrace_append hprefix tailTrace_1698225
  have hstable : (prefixWord ++ tailWord_1698225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698225).length < 2 ^ (prefixWord ++ tailWord_1698225).sum := by decide
  have hdescent : baseEnd_1698225 < baseStart_1698225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698317 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1698317 : Nat := 118140960795 + 1698317 * 2 ^ 59
def prefixEnd_1698317 : Nat := 4983230072969 + 3 ^ 40 * 1698317 * 2
def baseEnd_1698317 : Nat := 193789538822652680139353

theorem tailTrace_1698317 : CollatzResearch.WordTrace tailWord_1698317 prefixEnd_1698317 193789538822652680139353 := by
  unfold tailWord_1698317
  simp only [CollatzResearch.WordTrace]
  refine ⟨61942709788295033296693205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41295139858863355531128803 61942709788295033296693205)
  ·
    refine ⟨1451782260663164842891247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 61942709788295033296693205 1451782260663164842891247)
    ·
      refine ⟨2177673390994747264336871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451782260663164842891247 2177673390994747264336871)
      ·
        refine ⟨3266510086492120896505307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177673390994747264336871 3266510086492120896505307)
        ·
          refine ⟨4899765129738181344757961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266510086492120896505307 4899765129738181344757961)
          ·
            refine ⟨3674823847303636008568471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899765129738181344757961 3674823847303636008568471)
            ·
              refine ⟨5512235770955454012852707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674823847303636008568471 5512235770955454012852707)
              ·
                refine ⟨8268353656433181019279061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5512235770955454012852707 8268353656433181019279061)
                ·
                  refine ⟨193789538822652680139353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8268353656433181019279061 193789538822652680139353)
                  ·
                    rfl

theorem cell22_1698317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1698317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698317 prefixEnd_1698317 := by exact prefixLift 1698317
  have htrace : WordTrace (prefixWord ++ tailWord_1698317) baseStart_1698317 baseEnd_1698317 := by
    simpa [prefixWord, tailWord_1698317, baseEnd_1698317] using wordTrace_append hprefix tailTrace_1698317
  have hstable : (prefixWord ++ tailWord_1698317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698317).length < 2 ^ (prefixWord ++ tailWord_1698317).sum := by decide
  have hdescent : baseEnd_1698317 < baseStart_1698317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698328 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_1698328 : Nat := 118140960795 + 1698328 * 2 ^ 59
def prefixEnd_1698328 : Nat := 4983230072969 + 3 ^ 40 * 1698328 * 2
def baseEnd_1698328 : Nat := 193790793997585892797675

theorem tailTrace_1698328 : CollatzResearch.WordTrace tailWord_1698328 prefixEnd_1698328 193790793997585892797675 := by
  unfold tailWord_1698328
  simp only [CollatzResearch.WordTrace]
  refine ⟨30971555495627591087671819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41295407327503454783562425 30971555495627591087671819)
  ·
    refine ⟨46457333243441386631507729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30971555495627591087671819 46457333243441386631507729)
    ·
      refine ⟨34842999932581039973630797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46457333243441386631507729 34842999932581039973630797)
      ·
        refine ⟨13066124974717889990111549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34842999932581039973630797 13066124974717889990111549)
        ·
          refine ⟨4899796865519208746291831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13066124974717889990111549 4899796865519208746291831)
          ·
            refine ⟨7349695298278813119437747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899796865519208746291831 7349695298278813119437747)
            ·
              refine ⟨11024542947418219679156621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349695298278813119437747 11024542947418219679156621)
              ·
                refine ⟨4134203605281832379683733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11024542947418219679156621 4134203605281832379683733)
                ·
                  refine ⟨193790793997585892797675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4134203605281832379683733 193790793997585892797675)
                  ·
                    rfl

theorem cell22_1698328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_1698328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698328 prefixEnd_1698328 := by exact prefixLift 1698328
  have htrace : WordTrace (prefixWord ++ tailWord_1698328) baseStart_1698328 baseEnd_1698328 := by
    simpa [prefixWord, tailWord_1698328, baseEnd_1698328] using wordTrace_append hprefix tailTrace_1698328
  have hstable : (prefixWord ++ tailWord_1698328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698328).length < 2 ^ (prefixWord ++ tailWord_1698328).sum := by decide
  have hdescent : baseEnd_1698328 < baseStart_1698328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698362 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_1698362 : Nat := 118140960795 + 1698362 * 2 ^ 59
def prefixEnd_1698362 : Nat := 4983230072969 + 3 ^ 40 * 1698362 * 2
def baseEnd_1698362 : Nat := 193794673629197641014307

theorem tailTrace_1698362 : CollatzResearch.WordTrace tailWord_1698362 prefixEnd_1698362 193794673629197641014307 := by
  unfold tailWord_1698362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486087768283001495520335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41296234048754670654720893 15486087768283001495520335)
  ·
    refine ⟨23229131652424502243280503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15486087768283001495520335 23229131652424502243280503)
    ·
      refine ⟨34843697478636753364920755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23229131652424502243280503 34843697478636753364920755)
      ·
        refine ⟨52265546217955130047381133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34843697478636753364920755 52265546217955130047381133)
        ·
          refine ⟨19599579831733173767767925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52265546217955130047381133 19599579831733173767767925)
          ·
            refine ⟨1837460609224985040728243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19599579831733173767767925 1837460609224985040728243)
            ·
              refine ⟨2756190913837477561092365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837460609224985040728243 2756190913837477561092365)
              ·
                refine ⟨1033571592689054085409637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756190913837477561092365 1033571592689054085409637)
                ·
                  refine ⟨193794673629197641014307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033571592689054085409637 193794673629197641014307)
                  ·
                    rfl

theorem cell22_1698362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_1698362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698362 prefixEnd_1698362 := by exact prefixLift 1698362
  have htrace : WordTrace (prefixWord ++ tailWord_1698362) baseStart_1698362 baseEnd_1698362 := by
    simpa [prefixWord, tailWord_1698362, baseEnd_1698362] using wordTrace_append hprefix tailTrace_1698362
  have hstable : (prefixWord ++ tailWord_1698362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698362).length < 2 ^ (prefixWord ++ tailWord_1698362).sum := by decide
  have hdescent : baseEnd_1698362 < baseStart_1698362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698373 : List Nat := [1, 3, 1, 1, 1, 7, 8]
def baseStart_1698373 : Nat := 118140960795 + 1698373 * 2 ^ 59
def prefixEnd_1698373 : Nat := 4983230072969 + 3 ^ 40 * 1698373 * 2
def baseEnd_1698373 : Nat := 21532880978236761519181

theorem tailTrace_1698373 : CollatzResearch.WordTrace tailWord_1698373 prefixEnd_1698373 21532880978236761519181 := by
  unfold tailWord_1698373
  simp only [CollatzResearch.WordTrace]
  refine ⟨61944752276092154860731773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41296501517394769907154515 61944752276092154860731773)
  ·
    refine ⟨23229282103534558072774415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61944752276092154860731773 23229282103534558072774415)
    ·
      refine ⟨34843923155301837109161623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23229282103534558072774415 34843923155301837109161623)
      ·
        refine ⟨52265884732952755663742435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34843923155301837109161623 52265884732952755663742435)
        ·
          refine ⟨78398827099429133495613653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52265884732952755663742435 78398827099429133495613653)
          ·
            refine ⟨1837472510142870316303445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78398827099429133495613653 1837472510142870316303445)
            ·
              refine ⟨21532880978236761519181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1837472510142870316303445 21532880978236761519181)
              ·
                rfl

theorem cell22_1698373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 8].length) (baseStart_1698373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698373 prefixEnd_1698373 := by exact prefixLift 1698373
  have htrace : WordTrace (prefixWord ++ tailWord_1698373) baseStart_1698373 baseEnd_1698373 := by
    simpa [prefixWord, tailWord_1698373, baseEnd_1698373] using wordTrace_append hprefix tailTrace_1698373
  have hstable : (prefixWord ++ tailWord_1698373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698373).length < 2 ^ (prefixWord ++ tailWord_1698373).sum := by decide
  have hdescent : baseEnd_1698373 < baseStart_1698373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698375 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1698375 : Nat := 118140960795 + 1698375 * 2 ^ 59
def prefixEnd_1698375 : Nat := 4983230072969 + 3 ^ 40 * 1698375 * 2
def baseEnd_1698375 : Nat := 581388471053265222467881

theorem tailTrace_1698375 : CollatzResearch.WordTrace tailWord_1698375 prefixEnd_1698375 581388471053265222467881 := by
  unfold tailWord_1698375
  simp only [CollatzResearch.WordTrace]
  refine ⟨61944825222084909202304579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41296550148056606134869719 61944825222084909202304579)
  ·
    refine ⟨92917237833127363803456869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61944825222084909202304579 92917237833127363803456869)
    ·
      refine ⟨17421982093711380713148163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92917237833127363803456869 17421982093711380713148163)
      ·
        refine ⟨26132973140567071069722245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17421982093711380713148163 26132973140567071069722245)
        ·
          refine ⟨4899932463856325825572921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26132973140567071069722245 4899932463856325825572921)
          ·
            refine ⟨3674949347892244369179691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899932463856325825572921 3674949347892244369179691)
            ·
              refine ⟨5512424021838366553769537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674949347892244369179691 5512424021838366553769537)
              ·
                refine ⟨4134318016378774915327153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5512424021838366553769537 4134318016378774915327153)
                ·
                  refine ⟨3100738512284081186495365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4134318016378774915327153 3100738512284081186495365)
                  ·
                    refine ⟨581388471053265222467881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100738512284081186495365 581388471053265222467881)
                    ·
                      rfl

theorem cell22_1698375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1698375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698375 prefixEnd_1698375 := by exact prefixLift 1698375
  have htrace : WordTrace (prefixWord ++ tailWord_1698375) baseStart_1698375 baseEnd_1698375 := by
    simpa [prefixWord, tailWord_1698375, baseEnd_1698375] using wordTrace_append hprefix tailTrace_1698375
  have hstable : (prefixWord ++ tailWord_1698375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698375).length < 2 ^ (prefixWord ++ tailWord_1698375).sum := by decide
  have hdescent : baseEnd_1698375 < baseStart_1698375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698398 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1698398 : Nat := 118140960795 + 1698398 * 2 ^ 59
def prefixEnd_1698398 : Nat := 4983230072969 + 3 ^ 40 * 1698398 * 2
def baseEnd_1698398 : Nat := 581396344423300829142811

theorem tailTrace_1698398 : CollatzResearch.WordTrace tailWord_1698398 prefixEnd_1698398 581396344423300829142811 := by
  unfold tailWord_1698398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743208012625198016298981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41297109400667722753594565 7743208012625198016298981)
  ·
    refine ⟨1451851502367224628056059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7743208012625198016298981 1451851502367224628056059)
    ·
      refine ⟨2177777253550836942084089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451851502367224628056059 2177777253550836942084089)
      ·
        refine ⟨1633332940163127706563067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2177777253550836942084089 1633332940163127706563067)
        ·
          refine ⟨2449999410244691559844601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633332940163127706563067 2449999410244691559844601)
          ·
            refine ⟨1837499557683518669883451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2449999410244691559844601 1837499557683518669883451)
            ·
              refine ⟨2756249336525278004825177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837499557683518669883451 2756249336525278004825177)
              ·
                refine ⟨2067187002393958503618883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756249336525278004825177 2067187002393958503618883)
                ·
                  refine ⟨3100780503590937755428325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067187002393958503618883 3100780503590937755428325)
                  ·
                    refine ⟨581396344423300829142811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3100780503590937755428325 581396344423300829142811)
                    ·
                      rfl

theorem cell22_1698398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1698398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698398 prefixEnd_1698398 := by exact prefixLift 1698398
  have htrace : WordTrace (prefixWord ++ tailWord_1698398) baseStart_1698398 baseEnd_1698398 := by
    simpa [prefixWord, tailWord_1698398, baseEnd_1698398] using wordTrace_append hprefix tailTrace_1698398
  have hstable : (prefixWord ++ tailWord_1698398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698398).length < 2 ^ (prefixWord ++ tailWord_1698398).sum := by decide
  have hdescent : baseEnd_1698398 < baseStart_1698398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698450 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1698450 : Nat := 118140960795 + 1698450 * 2 ^ 59
def prefixEnd_1698450 : Nat := 4983230072969 + 3 ^ 40 * 1698450 * 2
def baseEnd_1698450 : Nat := 581414145085990026842651

theorem tailTrace_1698450 : CollatzResearch.WordTrace tailWord_1698450 prefixEnd_1698450 581414145085990026842651 := by
  unfold tailWord_1698450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486890174203299252821201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41298373797875464674189869 15486890174203299252821201)
  ·
    refine ⟨11615167630652474439615901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15486890174203299252821201 11615167630652474439615901)
    ·
      refine ⟨4355687861494677914855963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11615167630652474439615901 4355687861494677914855963)
      ·
        refine ⟨6533531792242016872283945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355687861494677914855963 6533531792242016872283945)
        ·
          refine ⟨4900148844181512654212959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6533531792242016872283945 4900148844181512654212959)
          ·
            refine ⟨7350223266272268981319439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900148844181512654212959 7350223266272268981319439)
            ·
              refine ⟨11025334899408403471979159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350223266272268981319439 11025334899408403471979159)
              ·
                refine ⟨16538002349112605207968739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025334899408403471979159 16538002349112605207968739)
                ·
                  refine ⟨24807003523668907811953109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16538002349112605207968739 24807003523668907811953109)
                  ·
                    refine ⟨581414145085990026842651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24807003523668907811953109 581414145085990026842651)
                    ·
                      rfl

theorem cell22_1698450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1698450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698450 prefixEnd_1698450 := by exact prefixLift 1698450
  have htrace : WordTrace (prefixWord ++ tailWord_1698450) baseStart_1698450 baseEnd_1698450 := by
    simpa [prefixWord, tailWord_1698450, baseEnd_1698450] using wordTrace_append hprefix tailTrace_1698450
  have hstable : (prefixWord ++ tailWord_1698450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698450).length < 2 ^ (prefixWord ++ tailWord_1698450).sum := by decide
  have hdescent : baseEnd_1698450 < baseStart_1698450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698452 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1698452 : Nat := 118140960795 + 1698452 * 2 ^ 59
def prefixEnd_1698452 : Nat := 4983230072969 + 3 ^ 40 * 1698452 * 2
def baseEnd_1698452 : Nat := 193804943242287562764215

theorem tailTrace_1698452 : CollatzResearch.WordTrace tailWord_1698452 prefixEnd_1698452 193804943242287562764215 := by
  unfold tailWord_1698452
  simp only [CollatzResearch.WordTrace]
  refine ⟨30973816821402975676428805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41298422428537300901905073 30973816821402975676428805)
  ·
    refine ⟨5807590654013057939330401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30973816821402975676428805 5807590654013057939330401)
    ·
      refine ⟨4355692990509793454497801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5807590654013057939330401 4355692990509793454497801)
      ·
        refine ⟨3266769742882345090873351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4355692990509793454497801 3266769742882345090873351)
        ·
          refine ⟨4900154614323517636310027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266769742882345090873351 4900154614323517636310027)
          ·
            refine ⟨7350231921485276454465041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900154614323517636310027 7350231921485276454465041)
            ·
              refine ⟨5512673941113957340848781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7350231921485276454465041 5512673941113957340848781)
              ·
                refine ⟨2067252727917734002818293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5512673941113957340848781 2067252727917734002818293)
                ·
                  refine ⟨193804943242287562764215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2067252727917734002818293 193804943242287562764215)
                  ·
                    rfl

theorem cell22_1698452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1698452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698452 prefixEnd_1698452 := by exact prefixLift 1698452
  have htrace : WordTrace (prefixWord ++ tailWord_1698452) baseStart_1698452 baseEnd_1698452 := by
    simpa [prefixWord, tailWord_1698452, baseEnd_1698452] using wordTrace_append hprefix tailTrace_1698452
  have hstable : (prefixWord ++ tailWord_1698452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698452).length < 2 ^ (prefixWord ++ tailWord_1698452).sum := by decide
  have hdescent : baseEnd_1698452 < baseStart_1698452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698486 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1698486 : Nat := 118140960795 + 1698486 * 2 ^ 59
def prefixEnd_1698486 : Nat := 4983230072969 + 3 ^ 40 * 1698486 * 2
def baseEnd_1698486 : Nat := 193808822873899310980847

theorem tailTrace_1698486 : CollatzResearch.WordTrace tailWord_1698486 prefixEnd_1698486 193808822873899310980847 := by
  unfold tailWord_1698486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871804607792673447474707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41299249149788516773063541 3871804607792673447474707)
  ·
    refine ⟨5807706911689010171212061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871804607792673447474707 5807706911689010171212061)
    ·
      refine ⟨2177890091883378814204523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5807706911689010171212061 2177890091883378814204523)
      ·
        refine ⟨3266835137825068221306785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177890091883378814204523 3266835137825068221306785)
        ·
          refine ⟨2450126353368801165980089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3266835137825068221306785 2450126353368801165980089)
          ·
            refine ⟨1837594765026600874485067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2450126353368801165980089 1837594765026600874485067)
            ·
              refine ⟨2756392147539901311727601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837594765026600874485067 2756392147539901311727601)
              ·
                refine ⟨2067294110654925983795701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756392147539901311727601 2067294110654925983795701)
                ·
                  refine ⟨193808822873899310980847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2067294110654925983795701 193808822873899310980847)
                  ·
                    rfl

theorem cell22_1698486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1698486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698486 prefixEnd_1698486 := by exact prefixLift 1698486
  have htrace : WordTrace (prefixWord ++ tailWord_1698486) baseStart_1698486 baseEnd_1698486 := by
    simpa [prefixWord, tailWord_1698486, baseEnd_1698486] using wordTrace_append hprefix tailTrace_1698486
  have hstable : (prefixWord ++ tailWord_1698486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698486).length < 2 ^ (prefixWord ++ tailWord_1698486).sum := by decide
  have hdescent : baseEnd_1698486 < baseStart_1698486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698510 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1698510 : Nat := 118140960795 + 1698510 * 2 ^ 59
def prefixEnd_1698510 : Nat := 4983230072969 + 3 ^ 40 * 1698510 * 2
def baseEnd_1698510 : Nat := 581434684312169870342467

theorem tailTrace_1698510 : CollatzResearch.WordTrace tailWord_1698510 prefixEnd_1698510 581434684312169870342467 := by
  unfold tailWord_1698510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7743718634574478407308623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41299832717730551505645989 7743718634574478407308623)
  ·
    refine ⟨11615577951861717610962935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7743718634574478407308623 11615577951861717610962935)
    ·
      refine ⟨17423366927792576416444403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615577951861717610962935 17423366927792576416444403)
      ·
        refine ⟨26135050391688864624666605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17423366927792576416444403 26135050391688864624666605)
        ·
          refine ⟨9800643896883324234249977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26135050391688864624666605 9800643896883324234249977)
          ·
            refine ⟨7350482922662493175687483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9800643896883324234249977 7350482922662493175687483)
            ·
              refine ⟨11025724383993739763531225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350482922662493175687483 11025724383993739763531225)
              ·
                refine ⟨8269293287995304822648419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11025724383993739763531225 8269293287995304822648419)
                ·
                  refine ⟨12403939931992957233972629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269293287995304822648419 12403939931992957233972629)
                  ·
                    refine ⟨581434684312169870342467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12403939931992957233972629 581434684312169870342467)
                    ·
                      rfl

theorem cell22_1698510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1698510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698510 prefixEnd_1698510 := by exact prefixLift 1698510
  have htrace : WordTrace (prefixWord ++ tailWord_1698510) baseStart_1698510 baseEnd_1698510 := by
    simpa [prefixWord, tailWord_1698510, baseEnd_1698510] using wordTrace_append hprefix tailTrace_1698510
  have hstable : (prefixWord ++ tailWord_1698510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698510).length < 2 ^ (prefixWord ++ tailWord_1698510).sum := by decide
  have hdescent : baseEnd_1698510 < baseStart_1698510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698548 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1698548 : Nat := 118140960795 + 1698548 * 2 ^ 59
def prefixEnd_1698548 : Nat := 4983230072969 + 3 ^ 40 * 1698548 * 2
def baseEnd_1698548 : Nat := 193815897496250145964117

theorem tailTrace_1698548 : CollatzResearch.WordTrace tailWord_1698548 prefixEnd_1698548 193815897496250145964117 := by
  unfold tailWord_1698548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975567525229079874176149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41300756700305439832234865 30975567525229079874176149)
  ·
    refine ⟨1451979727745113119102007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30975567525229079874176149 1451979727745113119102007)
    ·
      refine ⟨2177969591617669678653011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451979727745113119102007 2177969591617669678653011)
      ·
        refine ⟨3266954387426504517979517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177969591617669678653011 3266954387426504517979517)
        ·
          refine ⟨1225107895284939194242319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3266954387426504517979517 1225107895284939194242319)
          ·
            refine ⟨1837661842927408791363479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225107895284939194242319 1837661842927408791363479)
            ·
              refine ⟨2756492764391113187045219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837661842927408791363479 2756492764391113187045219)
              ·
                refine ⟨4134739146586669780567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756492764391113187045219 4134739146586669780567829)
                ·
                  refine ⟨193815897496250145964117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4134739146586669780567829 193815897496250145964117)
                  ·
                    rfl

theorem cell22_1698548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1698548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698548 prefixEnd_1698548 := by exact prefixLift 1698548
  have htrace : WordTrace (prefixWord ++ tailWord_1698548) baseStart_1698548 baseEnd_1698548 := by
    simpa [prefixWord, tailWord_1698548, baseEnd_1698548] using wordTrace_append hprefix tailTrace_1698548
  have hstable : (prefixWord ++ tailWord_1698548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698548).length < 2 ^ (prefixWord ++ tailWord_1698548).sum := by decide
  have hdescent : baseEnd_1698548 < baseStart_1698548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698615 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 6]
def baseStart_1698615 : Nat := 118140960795 + 1698615 * 2 ^ 59
def prefixEnd_1698615 : Nat := 4983230072969 + 3 ^ 40 * 1698615 * 2
def baseEnd_1698615 : Nat := 193823542652661532155715

theorem tailTrace_1698615 : CollatzResearch.WordTrace tailWord_1698615 prefixEnd_1698615 193823542652661532155715 := by
  unfold tailWord_1698615
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953578741215430191041299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41302385827476953460694199 61953578741215430191041299)
  ·
    refine ⟨92930368111823145286561949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61953578741215430191041299 92930368111823145286561949)
    ·
      refine ⟨34848888041933679482460731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92930368111823145286561949 34848888041933679482460731)
      ·
        refine ⟨52273332062900519223691097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34848888041933679482460731 52273332062900519223691097)
        ·
          refine ⟨39204999047175389417768323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52273332062900519223691097 39204999047175389417768323)
          ·
            refine ⟨58807498570763084126652485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39204999047175389417768323 58807498570763084126652485)
            ·
              refine ⟨11026405982018078273747341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58807498570763084126652485 11026405982018078273747341)
              ·
                refine ⟨4134902243256779352655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11026405982018078273747341 4134902243256779352655253)
                ·
                  refine ⟨193823542652661532155715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4134902243256779352655253 193823542652661532155715)
                  ·
                    rfl

theorem cell22_1698615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_1698615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698615 prefixEnd_1698615 := by exact prefixLift 1698615
  have htrace : WordTrace (prefixWord ++ tailWord_1698615) baseStart_1698615 baseEnd_1698615 := by
    simpa [prefixWord, tailWord_1698615, baseEnd_1698615] using wordTrace_append hprefix tailTrace_1698615
  have hstable : (prefixWord ++ tailWord_1698615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698615).length < 2 ^ (prefixWord ++ tailWord_1698615).sum := by decide
  have hdescent : baseEnd_1698615 < baseStart_1698615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698647 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1698647 : Nat := 118140960795 + 1698647 * 2 ^ 59
def prefixEnd_1698647 : Nat := 4983230072969 + 3 ^ 40 * 1698647 * 2
def baseEnd_1698647 : Nat := 581481582211947179667047

theorem tailTrace_1698647 : CollatzResearch.WordTrace tailWord_1698647 prefixEnd_1698647 581481582211947179667047 := by
  unfold tailWord_1698647
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954745877099499656206195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41303163918066333104137463 61954745877099499656206195)
  ·
    refine ⟨92932118815649249484309293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61954745877099499656206195 92932118815649249484309293)
    ·
      refine ⟨34849544555868468556615985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92932118815649249484309293 34849544555868468556615985)
      ·
        refine ⟨26137158416901351417461989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34849544555868468556615985 26137158416901351417461989)
        ·
          refine ⟨4900717203169003390774123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26137158416901351417461989 4900717203169003390774123)
          ·
            refine ⟨7351075804753505086161185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900717203169003390774123 7351075804753505086161185)
            ·
              refine ⟨5513306853565128814620889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351075804753505086161185 5513306853565128814620889)
              ·
                refine ⟨4134980140173846610965667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513306853565128814620889 4134980140173846610965667)
                ·
                  refine ⟨6202470210260769916448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134980140173846610965667 6202470210260769916448501)
                  ·
                    refine ⟨581481582211947179667047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6202470210260769916448501 581481582211947179667047)
                    ·
                      rfl

theorem cell22_1698647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1698647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698647 prefixEnd_1698647 := by exact prefixLift 1698647
  have htrace : WordTrace (prefixWord ++ tailWord_1698647) baseStart_1698647 baseEnd_1698647 := by
    simpa [prefixWord, tailWord_1698647, baseEnd_1698647] using wordTrace_append hprefix tailTrace_1698647
  have hstable : (prefixWord ++ tailWord_1698647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698647).length < 2 ^ (prefixWord ++ tailWord_1698647).sum := by decide
  have hdescent : baseEnd_1698647 < baseStart_1698647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698649 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 4]
def baseStart_1698649 : Nat := 118140960795 + 1698649 * 2 ^ 59
def prefixEnd_1698649 : Nat := 4983230072969 + 3 ^ 40 * 1698649 * 2
def baseEnd_1698649 : Nat := 193827422284273280372347

theorem tailTrace_1698649 : CollatzResearch.WordTrace tailWord_1698649 prefixEnd_1698649 193827422284273280372347 := by
  unfold tailWord_1698649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954818823092253997779001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41303212548728169331852667 61954818823092253997779001)
  ·
    refine ⟨46466114117319190498334251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61954818823092253997779001 46466114117319190498334251)
    ·
      refine ⟨69699171175978785747501377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46466114117319190498334251 69699171175978785747501377)
      ·
        refine ⟨52274378381984089310626033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69699171175978785747501377 52274378381984089310626033)
        ·
          refine ⟨39205783786488066982969525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52274378381984089310626033 39205783786488066982969525)
          ·
            refine ⟨3675542229983256279653393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39205783786488066982969525 3675542229983256279653393)
            ·
              refine ⟨2756656672487442209740045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675542229983256279653393 2756656672487442209740045)
              ·
                refine ⟨1033746252182790828652517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756656672487442209740045 1033746252182790828652517)
                ·
                  refine ⟨193827422284273280372347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033746252182790828652517 193827422284273280372347)
                  ·
                    rfl

theorem cell22_1698649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_1698649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698649 prefixEnd_1698649 := by exact prefixLift 1698649
  have htrace : WordTrace (prefixWord ++ tailWord_1698649) baseStart_1698649 baseEnd_1698649 := by
    simpa [prefixWord, tailWord_1698649, baseEnd_1698649] using wordTrace_append hprefix tailTrace_1698649
  have hstable : (prefixWord ++ tailWord_1698649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698649).length < 2 ^ (prefixWord ++ tailWord_1698649).sum := by decide
  have hdescent : baseEnd_1698649 < baseStart_1698649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698664 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1698664 : Nat := 118140960795 + 1698664 * 2 ^ 59
def prefixEnd_1698664 : Nat := 4983230072969 + 3 ^ 40 * 1698664 * 2
def baseEnd_1698664 : Nat := 581487401659364801991995

theorem tailTrace_1698664 : CollatzResearch.WordTrace tailWord_1698664 prefixEnd_1698664 581487401659364801991995 := by
  unfold tailWord_1698664
  simp only [CollatzResearch.WordTrace]
  refine ⟨30977682959018955779787523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41303577278691941039716697 30977682959018955779787523)
  ·
    refine ⟨46466524438528433669681285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30977682959018955779787523 46466524438528433669681285)
    ·
      refine ⟨8712473332224081313065241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46466524438528433669681285 8712473332224081313065241)
      ·
        refine ⟨6534354999168060984798931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8712473332224081313065241 6534354999168060984798931)
        ·
          refine ⟨9801532498752091477198397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534354999168060984798931 9801532498752091477198397)
          ·
            refine ⟨3675574687032034303949399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9801532498752091477198397 3675574687032034303949399)
            ·
              refine ⟨5513362030548051455924099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675574687032034303949399 5513362030548051455924099)
              ·
                refine ⟨8270043045822077183886149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513362030548051455924099 8270043045822077183886149)
                ·
                  refine ⟨1550633071091639471978653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8270043045822077183886149 1550633071091639471978653)
                  ·
                    refine ⟨581487401659364801991995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550633071091639471978653 581487401659364801991995)
                    ·
                      rfl

theorem cell22_1698664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1698664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698664 prefixEnd_1698664 := by exact prefixLift 1698664
  have htrace : WordTrace (prefixWord ++ tailWord_1698664) baseStart_1698664 baseEnd_1698664 := by
    simpa [prefixWord, tailWord_1698664, baseEnd_1698664] using wordTrace_append hprefix tailTrace_1698664
  have hstable : (prefixWord ++ tailWord_1698664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698664).length < 2 ^ (prefixWord ++ tailWord_1698664).sum := by decide
  have hdescent : baseEnd_1698664 < baseStart_1698664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698681 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_1698681 : Nat := 118140960795 + 1698681 * 2 ^ 59
def prefixEnd_1698681 : Nat := 4983230072969 + 3 ^ 40 * 1698681 * 2
def baseEnd_1698681 : Nat := 581493221106782424316943

theorem tailTrace_1698681 : CollatzResearch.WordTrace tailWord_1698681 prefixEnd_1698681 581493221106782424316943 := by
  unfold tailWord_1698681
  simp only [CollatzResearch.WordTrace]
  refine ⟨61955985958976323462943897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41303990639317548975295931 61955985958976323462943897)
  ·
    refine ⟨46466989469232242597207923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61955985958976323462943897 46466989469232242597207923)
    ·
      refine ⟨69700484203848363895811885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46466989469232242597207923 69700484203848363895811885)
      ·
        refine ⟨26137681576443136460929457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69700484203848363895811885 26137681576443136460929457)
        ·
          refine ⟨19603261182332352345697093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26137681576443136460929457 19603261182332352345697093)
          ·
            refine ⟨3675611471687316064818205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19603261182332352345697093 3675611471687316064818205)
            ·
              refine ⟨1378354301882743524306827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3675611471687316064818205 1378354301882743524306827)
              ·
                refine ⟨2067531452824115286460241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378354301882743524306827 2067531452824115286460241)
                ·
                  refine ⟨1550648589618086464845181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2067531452824115286460241 1550648589618086464845181)
                  ·
                    refine ⟨581493221106782424316943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550648589618086464845181 581493221106782424316943)
                    ·
                      rfl

theorem cell22_1698681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_1698681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698681 prefixEnd_1698681 := by exact prefixLift 1698681
  have htrace : WordTrace (prefixWord ++ tailWord_1698681) baseStart_1698681 baseEnd_1698681 := by
    simpa [prefixWord, tailWord_1698681, baseEnd_1698681] using wordTrace_append hprefix tailTrace_1698681
  have hstable : (prefixWord ++ tailWord_1698681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698681).length < 2 ^ (prefixWord ++ tailWord_1698681).sum := by decide
  have hdescent : baseEnd_1698681 < baseStart_1698681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698786 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1698786 : Nat := 118140960795 + 1698786 * 2 ^ 59
def prefixEnd_1698786 : Nat := 4983230072969 + 3 ^ 40 * 1698786 * 2
def baseEnd_1698786 : Nat := 581529164752597150441621

theorem tailTrace_1698786 : CollatzResearch.WordTrace tailWord_1698786 prefixEnd_1698786 581529164752597150441621 := by
  unfold tailWord_1698786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489953905898981598879053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41306543749063950930344141 15489953905898981598879053)
  ·
    refine ⟨5808732714712118099579645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15489953905898981598879053 5808732714712118099579645)
    ·
      refine ⟨2178274768017044287342367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5808732714712118099579645 2178274768017044287342367)
      ·
        refine ⟨3267412152025566431013551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178274768017044287342367 3267412152025566431013551)
        ·
          refine ⟨4901118228038349646520327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267412152025566431013551 4901118228038349646520327)
          ·
            refine ⟨7351677342057524469780491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901118228038349646520327 7351677342057524469780491)
            ·
              refine ⟨11027516013086286704670737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351677342057524469780491 11027516013086286704670737)
              ·
                refine ⟨8270637009814715028503053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11027516013086286704670737 8270637009814715028503053)
                ·
                  refine ⟨3101488878680518135688645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8270637009814715028503053 3101488878680518135688645)
                  ·
                    refine ⟨581529164752597150441621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101488878680518135688645 581529164752597150441621)
                    ·
                      rfl

theorem cell22_1698786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1698786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698786 prefixEnd_1698786 := by exact prefixLift 1698786
  have htrace : WordTrace (prefixWord ++ tailWord_1698786) baseStart_1698786 baseEnd_1698786 := by
    simpa [prefixWord, tailWord_1698786, baseEnd_1698786] using wordTrace_append hprefix tailTrace_1698786
  have hstable : (prefixWord ++ tailWord_1698786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698786).length < 2 ^ (prefixWord ++ tailWord_1698786).sum := by decide
  have hdescent : baseEnd_1698786 < baseStart_1698786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698799 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 1, 5]
def baseStart_1698799 : Nat := 118140960795 + 1698799 * 2 ^ 59
def prefixEnd_1698799 : Nat := 4983230072969 + 3 ^ 40 * 1698799 * 2
def baseEnd_1698799 : Nat := 581533614918269449866581

theorem tailTrace_1698799 : CollatzResearch.WordTrace tailWord_1698799 prefixEnd_1698799 581533614918269449866581 := by
  unfold tailWord_1698799
  simp only [CollatzResearch.WordTrace]
  refine ⟨61960289772548829615739451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41306859848365886410492967 61960289772548829615739451)
  ·
    refine ⟨92940434658823244423609177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61960289772548829615739451 92940434658823244423609177)
    ·
      refine ⟨69705325994117433317706883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92940434658823244423609177 69705325994117433317706883)
      ·
        refine ⟨104557988991176149976560325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69705325994117433317706883 104557988991176149976560325)
        ·
          refine ⟨19604622935845528120605061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104557988991176149976560325 19604622935845528120605061)
          ·
            refine ⟨3675866800471036522613449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19604622935845528120605061 3675866800471036522613449)
            ·
              refine ⟨2756900100353277391960087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675866800471036522613449 2756900100353277391960087)
              ·
                refine ⟨4135350150529916087940131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756900100353277391960087 4135350150529916087940131)
                ·
                  refine ⟨6203025225794874131910197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135350150529916087940131 6203025225794874131910197)
                  ·
                    refine ⟨581533614918269449866581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6203025225794874131910197 581533614918269449866581)
                    ·
                      rfl

theorem cell22_1698799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_1698799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698799 prefixEnd_1698799 := by exact prefixLift 1698799
  have htrace : WordTrace (prefixWord ++ tailWord_1698799) baseStart_1698799 baseEnd_1698799 := by
    simpa [prefixWord, tailWord_1698799, baseEnd_1698799] using wordTrace_append hprefix tailTrace_1698799
  have hstable : (prefixWord ++ tailWord_1698799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698799).length < 2 ^ (prefixWord ++ tailWord_1698799).sum := by decide
  have hdescent : baseEnd_1698799 < baseStart_1698799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698904 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_1698904 : Nat := 118140960795 + 1698904 * 2 ^ 59
def prefixEnd_1698904 : Nat := 4983230072969 + 3 ^ 40 * 1698904 * 2
def baseEnd_1698904 : Nat := 581569558564084175991259

theorem tailTrace_1698904 : CollatzResearch.WordTrace tailWord_1698904 prefixEnd_1698904 581569558564084175991259 := by
  unfold tailWord_1698904
  simp only [CollatzResearch.WordTrace]
  refine ⟨30982059718584216274155883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41309412958112288365541177 30982059718584216274155883)
  ·
    refine ⟨46473089577876324411233825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30982059718584216274155883 46473089577876324411233825)
    ·
      refine ⟨34854817183407243308425369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46473089577876324411233825 34854817183407243308425369)
      ·
        refine ⟨26141112887555432481319027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34854817183407243308425369 26141112887555432481319027)
        ·
          refine ⟨39211669331333148721978541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26141112887555432481319027 39211669331333148721978541)
          ·
            refine ⟨14704375999249930770741953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39211669331333148721978541 14704375999249930770741953)
            ·
              refine ⟨11028281999437448078056465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14704375999249930770741953 11028281999437448078056465)
              ·
                refine ⟨8271211499578086058542349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028281999437448078056465 8271211499578086058542349)
                ·
                  refine ⟨3101704312341782271953381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8271211499578086058542349 3101704312341782271953381)
                  ·
                    refine ⟨581569558564084175991259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101704312341782271953381 581569558564084175991259)
                    ·
                      rfl

theorem cell22_1698904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_1698904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698904 prefixEnd_1698904 := by exact prefixLift 1698904
  have htrace : WordTrace (prefixWord ++ tailWord_1698904) baseStart_1698904 baseEnd_1698904 := by
    simpa [prefixWord, tailWord_1698904, baseEnd_1698904] using wordTrace_append hprefix tailTrace_1698904
  have hstable : (prefixWord ++ tailWord_1698904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698904).length < 2 ^ (prefixWord ++ tailWord_1698904).sum := by decide
  have hdescent : baseEnd_1698904 < baseStart_1698904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698921 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_1698921 : Nat := 118140960795 + 1698921 * 2 ^ 59
def prefixEnd_1698921 : Nat := 4983230072969 + 3 ^ 40 * 1698921 * 2
def baseEnd_1698921 : Nat := 581575378011501798316207

theorem tailTrace_1698921 : CollatzResearch.WordTrace tailWord_1698921 prefixEnd_1698921 581575378011501798316207 := by
  unfold tailWord_1698921
  simp only [CollatzResearch.WordTrace]
  refine ⟨61964739478106844451680617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41309826318737896301120411 61964739478106844451680617)
  ·
    refine ⟨46473554608580133338760463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61964739478106844451680617 46473554608580133338760463)
    ·
      refine ⟨69710331912870200008140695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46473554608580133338760463 69710331912870200008140695)
      ·
        refine ⟨104565497869305300012211043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69710331912870200008140695 104565497869305300012211043)
        ·
          refine ⟨156848246803957950018316565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104565497869305300012211043 156848246803957950018316565)
          ·
            refine ⟨7352261568935528907108589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156848246803957950018316565 7352261568935528907108589)
            ·
              refine ⟨2757098088350823340165721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352261568935528907108589 2757098088350823340165721)
              ·
                refine ⟨2067823566263117505124291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757098088350823340165721 2067823566263117505124291)
                ·
                  refine ⟨3101735349394676257686437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2067823566263117505124291 3101735349394676257686437)
                  ·
                    refine ⟨581575378011501798316207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101735349394676257686437 581575378011501798316207)
                    ·
                      rfl

theorem cell22_1698921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_1698921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698921 prefixEnd_1698921 := by exact prefixLift 1698921
  have htrace : WordTrace (prefixWord ++ tailWord_1698921) baseStart_1698921 baseEnd_1698921 := by
    simpa [prefixWord, tailWord_1698921, baseEnd_1698921] using wordTrace_append hprefix tailTrace_1698921
  have hstable : (prefixWord ++ tailWord_1698921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698921).length < 2 ^ (prefixWord ++ tailWord_1698921).sum := by decide
  have hdescent : baseEnd_1698921 < baseStart_1698921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698942 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1698942 : Nat := 118140960795 + 1698942 * 2 ^ 59
def prefixEnd_1698942 : Nat := 4983230072969 + 3 ^ 40 * 1698942 * 2
def baseEnd_1698942 : Nat := 193860855580221581180381

theorem tailTrace_1698942 : CollatzResearch.WordTrace tailWord_1698942 prefixEnd_1698942 193860855580221581180381 := by
  unfold tailWord_1698942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745688176378845629774385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41310336940687176692130053 7745688176378845629774385)
  ·
    refine ⟨5809266132284134222330789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7745688176378845629774385 5809266132284134222330789)
    ·
      refine ⟨1089237399803275166687023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5809266132284134222330789 1089237399803275166687023)
      ·
        refine ⟨1633856099704912750030535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089237399803275166687023 1633856099704912750030535)
        ·
          refine ⟨2450784149557369125045803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633856099704912750030535 2450784149557369125045803)
          ·
            refine ⟨3676176224336053687568705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450784149557369125045803 3676176224336053687568705)
            ·
              refine ⟨2757132168252040265676529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676176224336053687568705 2757132168252040265676529)
              ·
                refine ⟨2067849126189030199257397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757132168252040265676529 2067849126189030199257397)
                ·
                  refine ⟨193860855580221581180381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2067849126189030199257397 193860855580221581180381)
                  ·
                    rfl

theorem cell22_1698942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1698942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698942 prefixEnd_1698942 := by exact prefixLift 1698942
  have htrace : WordTrace (prefixWord ++ tailWord_1698942) baseStart_1698942 baseEnd_1698942 := by
    simpa [prefixWord, tailWord_1698942, baseEnd_1698942] using wordTrace_append hprefix tailTrace_1698942
  have hstable : (prefixWord ++ tailWord_1698942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698942).length < 2 ^ (prefixWord ++ tailWord_1698942).sum := by decide
  have hdescent : baseEnd_1698942 < baseStart_1698942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698953 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 4]
def baseStart_1698953 : Nat := 118140960795 + 1698953 * 2 ^ 59
def prefixEnd_1698953 : Nat := 4983230072969 + 3 ^ 40 * 1698953 * 2
def baseEnd_1698953 : Nat := 193862110755154793838703

theorem tailTrace_1698953 : CollatzResearch.WordTrace tailWord_1698953 prefixEnd_1698953 193862110755154793838703 := by
  unfold tailWord_1698953
  simp only [CollatzResearch.WordTrace]
  refine ⟨61965906613990913916845513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41310604409327275944563675 61965906613990913916845513)
  ·
    refine ⟨46474429960493185437634135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61965906613990913916845513 46474429960493185437634135)
    ·
      refine ⟨69711644940739778156451203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46474429960493185437634135 69711644940739778156451203)
      ·
        refine ⟨104567467411109667234676805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69711644940739778156451203 104567467411109667234676805)
        ·
          refine ⟨19606400139583062606501901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104567467411109667234676805 19606400139583062606501901)
          ·
            refine ⟨7352400052343648477438213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19606400139583062606501901 7352400052343648477438213)
            ·
              refine ⟨1378575009814434089519665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7352400052343648477438213 1378575009814434089519665)
              ·
                refine ⟨1033931257360825567139749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378575009814434089519665 1033931257360825567139749)
                ·
                  refine ⟨193862110755154793838703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1033931257360825567139749 193862110755154793838703)
                  ·
                    rfl

theorem cell22_1698953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_1698953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698953 prefixEnd_1698953 := by exact prefixLift 1698953
  have htrace : WordTrace (prefixWord ++ tailWord_1698953) baseStart_1698953 baseEnd_1698953 := by
    simpa [prefixWord, tailWord_1698953, baseEnd_1698953] using wordTrace_append hprefix tailTrace_1698953
  have hstable : (prefixWord ++ tailWord_1698953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698953).length < 2 ^ (prefixWord ++ tailWord_1698953).sum := by decide
  have hdescent : baseEnd_1698953 < baseStart_1698953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698968 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_1698968 : Nat := 118140960795 + 1698968 * 2 ^ 59
def prefixEnd_1698968 : Nat := 4983230072969 + 3 ^ 40 * 1698968 * 2
def baseEnd_1698968 : Nat := 581591467072009342391063

theorem tailTrace_1698968 : CollatzResearch.WordTrace tailWord_1698968 prefixEnd_1698968 581591467072009342391063 := by
  unfold tailWord_1698968
  simp only [CollatzResearch.WordTrace]
  refine ⟨30983226854468285739320779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41310969139291047652427705 30983226854468285739320779)
  ·
    refine ⟨46474840281702428608981169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30983226854468285739320779 46474840281702428608981169)
    ·
      refine ⟨34856130211276821456735877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46474840281702428608981169 34856130211276821456735877)
      ·
        refine ⟨6535524414614404023137977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34856130211276821456735877 6535524414614404023137977)
        ·
          refine ⟨4901643310960803017353483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535524414614404023137977 4901643310960803017353483)
          ·
            refine ⟨7352464966441204526030225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901643310960803017353483 7352464966441204526030225)
            ·
              refine ⟨5514348724830903394522669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7352464966441204526030225 5514348724830903394522669)
              ·
                refine ⟨2067880771811588772946001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5514348724830903394522669 2067880771811588772946001)
                ·
                  refine ⟨1550910578858691579709501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2067880771811588772946001 1550910578858691579709501)
                  ·
                    refine ⟨581591467072009342391063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1550910578858691579709501 581591467072009342391063)
                    ·
                      rfl

theorem cell22_1698968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_1698968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698968 prefixEnd_1698968 := by exact prefixLift 1698968
  have htrace : WordTrace (prefixWord ++ tailWord_1698968) baseStart_1698968 baseEnd_1698968 := by
    simpa [prefixWord, tailWord_1698968, baseEnd_1698968] using wordTrace_append hprefix tailTrace_1698968
  have hstable : (prefixWord ++ tailWord_1698968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698968).length < 2 ^ (prefixWord ++ tailWord_1698968).sum := by decide
  have hdescent : baseEnd_1698968 < baseStart_1698968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698981 : List Nat := [1, 3, 1, 2, 1, 5, 3, 6]
def baseStart_1698981 : Nat := 118140960795 + 1698981 * 2 ^ 59
def prefixEnd_1698981 : Nat := 4983230072969 + 3 ^ 40 * 1698981 * 2
def baseEnd_1698981 : Nat := 64621768581964626868447

theorem tailTrace_1698981 : CollatzResearch.WordTrace tailWord_1698981 prefixEnd_1698981 64621768581964626868447 := by
  unfold tailWord_1698981
  simp only [CollatzResearch.WordTrace]
  refine ⟨61966927857889474698864797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41311285238592983132576531 61966927857889474698864797)
  ·
    refine ⟨23237597946708553012074299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61966927857889474698864797 23237597946708553012074299)
    ·
      refine ⟨34856396920062829518111449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237597946708553012074299 34856396920062829518111449)
      ·
        refine ⟨26142297690047122138583587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34856396920062829518111449 26142297690047122138583587)
        ·
          refine ⟨39213446535070683207875381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26142297690047122138583587 39213446535070683207875381)
          ·
            refine ⟨3676260612662876550738317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39213446535070683207875381 3676260612662876550738317)
            ·
              refine ⟨1378597729748578706526869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3676260612662876550738317 1378597729748578706526869)
              ·
                refine ⟨64621768581964626868447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1378597729748578706526869 64621768581964626868447)
                ·
                  rfl

theorem cell22_1698981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 6].length) (baseStart_1698981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698981 prefixEnd_1698981 := by exact prefixLift 1698981
  have htrace : WordTrace (prefixWord ++ tailWord_1698981) baseStart_1698981 baseEnd_1698981 := by
    simpa [prefixWord, tailWord_1698981, baseEnd_1698981] using wordTrace_append hprefix tailTrace_1698981
  have hstable : (prefixWord ++ tailWord_1698981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698981).length < 2 ^ (prefixWord ++ tailWord_1698981).sum := by decide
  have hdescent : baseEnd_1698981 < baseStart_1698981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698983 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1698983 : Nat := 118140960795 + 1698983 * 2 ^ 59
def prefixEnd_1698983 : Nat := 4983230072969 + 3 ^ 40 * 1698983 * 2
def baseEnd_1698983 : Nat := 581596601878554303266017

theorem tailTrace_1698983 : CollatzResearch.WordTrace tailWord_1698983 prefixEnd_1698983 581596601878554303266017 := by
  unfold tailWord_1698983
  simp only [CollatzResearch.WordTrace]
  refine ⟨61967000803882229040437603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41311333869254819360291735 61967000803882229040437603)
  ·
    refine ⟨92950501205823343560656405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61967000803882229040437603 92950501205823343560656405)
    ·
      refine ⟨4357054744022969229405769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92950501205823343560656405 4357054744022969229405769)
      ·
        refine ⟨3267791058017226922054327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4357054744022969229405769 3267791058017226922054327)
        ·
          refine ⟨4901686587025840383081491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267791058017226922054327 4901686587025840383081491)
          ·
            refine ⟨7352529880538760574622237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901686587025840383081491 7352529880538760574622237)
            ·
              refine ⟨2757198705202035215483339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352529880538760574622237 2757198705202035215483339)
              ·
                refine ⟨4135798057803052823225009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757198705202035215483339 4135798057803052823225009)
                ·
                  refine ⟨3101848543352289617418757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4135798057803052823225009 3101848543352289617418757)
                  ·
                    refine ⟨581596601878554303266017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3101848543352289617418757 581596601878554303266017)
                    ·
                      rfl

theorem cell22_1698983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1698983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1698983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1698983 prefixEnd_1698983 := by exact prefixLift 1698983
  have htrace : WordTrace (prefixWord ++ tailWord_1698983) baseStart_1698983 baseEnd_1698983 := by
    simpa [prefixWord, tailWord_1698983, baseEnd_1698983] using wordTrace_append hprefix tailTrace_1698983
  have hstable : (prefixWord ++ tailWord_1698983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698983).length < 2 ^ (prefixWord ++ tailWord_1698983).sum := by decide
  have hdescent : baseEnd_1698983 < baseStart_1698983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699071 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 6]
def baseStart_1699071 : Nat := 118140960795 + 1699071 * 2 ^ 59
def prefixEnd_1699071 : Nat := 4983230072969 + 3 ^ 40 * 1699071 * 2
def baseEnd_1699071 : Nat := 193875575358983802355249

theorem tailTrace_1699071 : CollatzResearch.WordTrace tailWord_1699071 prefixEnd_1699071 193875575358983802355249 := by
  unfold tailWord_1699071
  simp only [CollatzResearch.WordTrace]
  refine ⟨61970210427563420069641067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41313473618375613379760711 61970210427563420069641067)
  ·
    refine ⟨92955315641345130104461601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61970210427563420069641067 92955315641345130104461601)
    ·
      refine ⟨69716486731008847578346201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92955315641345130104461601 69716486731008847578346201)
      ·
        refine ⟨52287365048256635683759651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69716486731008847578346201 52287365048256635683759651)
        ·
          refine ⟨78431047572384953525639477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52287365048256635683759651 78431047572384953525639477)
          ·
            refine ⟨7352910709911089393028701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78431047572384953525639477 7352910709911089393028701)
            ·
              refine ⟨2757341516216658522385763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352910709911089393028701 2757341516216658522385763)
              ·
                refine ⟨4136012274324987783578645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757341516216658522385763 4136012274324987783578645)
                ·
                  refine ⟨193875575358983802355249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4136012274324987783578645 193875575358983802355249)
                  ·
                    rfl

theorem cell22_1699071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 6].length) (baseStart_1699071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699071 prefixEnd_1699071 := by exact prefixLift 1699071
  have htrace : WordTrace (prefixWord ++ tailWord_1699071) baseStart_1699071 baseEnd_1699071 := by
    simpa [prefixWord, tailWord_1699071, baseEnd_1699071] using wordTrace_append hprefix tailTrace_1699071
  have hstable : (prefixWord ++ tailWord_1699071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699071).length < 2 ^ (prefixWord ++ tailWord_1699071).sum := by decide
  have hdescent : baseEnd_1699071 < baseStart_1699071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699103 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 1, 5]
def baseStart_1699103 : Nat := 118140960795 + 1699103 * 2 ^ 59
def prefixEnd_1699103 : Nat := 4983230072969 + 3 ^ 40 * 1699103 * 2
def baseEnd_1699103 : Nat := 581637680330913990265649

theorem tailTrace_1699103 : CollatzResearch.WordTrace tailWord_1699103 prefixEnd_1699103 581637680330913990265649 := by
  unfold tailWord_1699103
  simp only [CollatzResearch.WordTrace]
  refine ⟨61971377563447489534805963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41314251708964993023203975 61971377563447489534805963)
  ·
    refine ⟨92957066345171234302208945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61971377563447489534805963 92957066345171234302208945)
    ·
      refine ⟨69717799758878425726656709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92957066345171234302208945 69717799758878425726656709)
      ·
        refine ⟨13072087454789704823748133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69717799758878425726656709 13072087454789704823748133)
        ·
          refine ⟨2451016397773069654452775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13072087454789704823748133 2451016397773069654452775)
          ·
            refine ⟨3676524596659604481679163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451016397773069654452775 3676524596659604481679163)
            ·
              refine ⟨5514786894989406722518745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3676524596659604481679163 5514786894989406722518745)
              ·
                refine ⟨4136090171242055041889059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514786894989406722518745 4136090171242055041889059)
                ·
                  refine ⟨6204135256863082562833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136090171242055041889059 6204135256863082562833589)
                  ·
                    refine ⟨581637680330913990265649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6204135256863082562833589 581637680330913990265649)
                    ·
                      rfl

theorem cell22_1699103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_1699103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699103 prefixEnd_1699103 := by exact prefixLift 1699103
  have htrace : WordTrace (prefixWord ++ tailWord_1699103) baseStart_1699103 baseEnd_1699103 := by
    simpa [prefixWord, tailWord_1699103, baseEnd_1699103] using wordTrace_append hprefix tailTrace_1699103
  have hstable : (prefixWord ++ tailWord_1699103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699103).length < 2 ^ (prefixWord ++ tailWord_1699103).sum := by decide
  have hdescent : baseEnd_1699103 < baseStart_1699103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699122 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_1699122 : Nat := 118140960795 + 1699122 * 2 ^ 59
def prefixEnd_1699122 : Nat := 4983230072969 + 3 ^ 40 * 1699122 * 2
def baseEnd_1699122 : Nat := 193881394806401424680197

theorem tailTrace_1699122 : CollatzResearch.WordTrace tailWord_1699122 prefixEnd_1699122 193881394806401424680197 := by
  unfold tailWord_1699122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493017637594663944936905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41314713700252437186498413 15493017637594663944936905)
  ·
    refine ⟨11619763228195997958702679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15493017637594663944936905 11619763228195997958702679)
    ·
      refine ⟨17429644842293996938054019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11619763228195997958702679 17429644842293996938054019)
      ·
        refine ⟨26144467263440995407081029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17429644842293996938054019 26144467263440995407081029)
        ·
          refine ⟨4902087611895186638827693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26144467263440995407081029 4902087611895186638827693)
          ·
            refine ⟨1838282854460694989560385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4902087611895186638827693 1838282854460694989560385)
            ·
              refine ⟨1378712140845521242170289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838282854460694989560385 1378712140845521242170289)
              ·
                refine ⟨1034034105634140931627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378712140845521242170289 1034034105634140931627717)
                ·
                  refine ⟨193881394806401424680197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034034105634140931627717 193881394806401424680197)
                  ·
                    rfl

theorem cell22_1699122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_1699122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699122 prefixEnd_1699122 := by exact prefixLift 1699122
  have htrace : WordTrace (prefixWord ++ tailWord_1699122) baseStart_1699122 baseEnd_1699122 := by
    simpa [prefixWord, tailWord_1699122, baseEnd_1699122] using wordTrace_append hprefix tailTrace_1699122
  have hstable : (prefixWord ++ tailWord_1699122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699122).length < 2 ^ (prefixWord ++ tailWord_1699122).sum := by decide
  have hdescent : baseEnd_1699122 < baseStart_1699122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699148 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_1699148 : Nat := 118140960795 + 1699148 * 2 ^ 59
def prefixEnd_1699148 : Nat := 4983230072969 + 3 ^ 40 * 1699148 * 2
def baseEnd_1699148 : Nat := 581653084750548872890511

theorem tailTrace_1699148 : CollatzResearch.WordTrace tailWord_1699148 prefixEnd_1699148 581653084750548872890511 := by
  unfold tailWord_1699148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30986509424142231110097049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41315345898856308146796065 30986509424142231110097049)
  ·
    refine ⟨23239882068106673332572787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30986509424142231110097049 23239882068106673332572787)
    ·
      refine ⟨34859823102160009998859181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23239882068106673332572787 34859823102160009998859181)
      ·
        refine ⟨13072433663310003749572193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34859823102160009998859181 13072433663310003749572193)
        ·
          refine ⟨9804325247482502812179145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13072433663310003749572193 9804325247482502812179145)
          ·
            refine ⟨7353243935611877109134359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9804325247482502812179145 7353243935611877109134359)
            ·
              refine ⟨11029865903417815663701539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353243935611877109134359 11029865903417815663701539)
              ·
                refine ⟨16544798855126723495552309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11029865903417815663701539 16544798855126723495552309)
                ·
                  refine ⟨1551074892668130327708029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16544798855126723495552309 1551074892668130327708029)
                  ·
                    refine ⟨581653084750548872890511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551074892668130327708029 581653084750548872890511)
                    ·
                      rfl

theorem cell22_1699148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_1699148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699148 prefixEnd_1699148 := by exact prefixLift 1699148
  have htrace : WordTrace (prefixWord ++ tailWord_1699148) baseStart_1699148 baseEnd_1699148 := by
    simpa [prefixWord, tailWord_1699148, baseEnd_1699148] using wordTrace_append hprefix tailTrace_1699148
  have hstable : (prefixWord ++ tailWord_1699148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699148).length < 2 ^ (prefixWord ++ tailWord_1699148).sum := by decide
  have hdescent : baseEnd_1699148 < baseStart_1699148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699158 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1699158 : Nat := 118140960795 + 1699158 * 2 ^ 59
def prefixEnd_1699158 : Nat := 4983230072969 + 3 ^ 40 * 1699158 * 2
def baseEnd_1699158 : Nat := 581656507954912180140481

theorem tailTrace_1699158 : CollatzResearch.WordTrace tailWord_1699158 prefixEnd_1699158 581656507954912180140481 := by
  unfold tailWord_1699158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873336473640514620503633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41315589052165489285372085 3873336473640514620503633)
  ·
    refine ⟨2905002355230385965377725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3873336473640514620503633 2905002355230385965377725)
    ·
      refine ⟨1089375883211394737016647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2905002355230385965377725 1089375883211394737016647)
      ·
        refine ⟨1634063824817092105524971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089375883211394737016647 1634063824817092105524971)
        ·
          refine ⟨2451095737225638158287457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634063824817092105524971 2451095737225638158287457)
          ·
            refine ⟨1838321802919228618715593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451095737225638158287457 1838321802919228618715593)
            ·
              refine ⟨1378741352189421464036695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838321802919228618715593 1378741352189421464036695)
              ·
                refine ⟨2068112028284132196055043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378741352189421464036695 2068112028284132196055043)
                ·
                  refine ⟨3102168042426198294082565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068112028284132196055043 3102168042426198294082565)
                  ·
                    refine ⟨581656507954912180140481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3102168042426198294082565 581656507954912180140481)
                    ·
                      rfl

theorem cell22_1699158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1699158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699158 prefixEnd_1699158 := by exact prefixLift 1699158
  have htrace : WordTrace (prefixWord ++ tailWord_1699158) baseStart_1699158 baseEnd_1699158 := by
    simpa [prefixWord, tailWord_1699158, baseEnd_1699158] using wordTrace_append hprefix tailTrace_1699158
  have hstable : (prefixWord ++ tailWord_1699158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699158).length < 2 ^ (prefixWord ++ tailWord_1699158).sum := by decide
  have hdescent : baseEnd_1699158 < baseStart_1699158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699255 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 2, 3]
def baseStart_1699255 : Nat := 118140960795 + 1699255 * 2 ^ 59
def prefixEnd_1699255 : Nat := 4983230072969 + 3 ^ 40 * 1699255 * 2
def baseEnd_1699255 : Nat := 581689713037236260465183

theorem tailTrace_1699255 : CollatzResearch.WordTrace tailWord_1699255 prefixEnd_1699255 581689713037236260465183 := by
  unfold tailWord_1699255
  simp only [CollatzResearch.WordTrace]
  refine ⟨61976921458896819494339219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41317947639264546329559479 61976921458896819494339219)
  ·
    refine ⟨92965382188345229241508829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61976921458896819494339219 92965382188345229241508829)
    ·
      refine ⟨34862018320629460965565811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92965382188345229241508829 34862018320629460965565811)
      ·
        refine ⟨52293027480944191448348717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34862018320629460965565811 52293027480944191448348717)
        ·
          refine ⟨19609885305354071793130769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52293027480944191448348717 19609885305354071793130769)
          ·
            refine ⟨14707413979015553844848077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19609885305354071793130769 14707413979015553844848077)
            ·
              refine ⟨5515280242130832691818029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14707413979015553844848077 5515280242130832691818029)
              ·
                refine ⟨2068230090799062259431761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5515280242130832691818029 2068230090799062259431761)
                ·
                  refine ⟨1551172568099296694573821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2068230090799062259431761 1551172568099296694573821)
                  ·
                    refine ⟨581689713037236260465183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551172568099296694573821 581689713037236260465183)
                    ·
                      rfl

theorem cell22_1699255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_1699255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699255 prefixEnd_1699255 := by exact prefixLift 1699255
  have htrace : WordTrace (prefixWord ++ tailWord_1699255) baseStart_1699255 baseEnd_1699255 := by
    simpa [prefixWord, tailWord_1699255, baseEnd_1699255] using wordTrace_append hprefix tailTrace_1699255
  have hstable : (prefixWord ++ tailWord_1699255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699255).length < 2 ^ (prefixWord ++ tailWord_1699255).sum := by decide
  have hdescent : baseEnd_1699255 < baseStart_1699255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699317 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1699317 : Nat := 118140960795 + 1699317 * 2 ^ 59
def prefixEnd_1699317 : Nat := 4983230072969 + 3 ^ 40 * 1699317 * 2
def baseEnd_1699317 : Nat := 581710936904288765414993

theorem tailTrace_1699317 : CollatzResearch.WordTrace tailWord_1699317 prefixEnd_1699317 581710936904288765414993 := by
  unfold tailWord_1699317
  simp only [CollatzResearch.WordTrace]
  refine ⟨61979182784672204083096205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41319455189781469388730803 61979182784672204083096205)
  ·
    refine ⟨23242193544252076531161077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61979182784672204083096205 23242193544252076531161077)
    ·
      refine ⟨2178955644773632174796351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23242193544252076531161077 2178955644773632174796351)
      ·
        refine ⟨3268433467160448262194527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178955644773632174796351 3268433467160448262194527)
        ·
          refine ⟨4902650200740672393291791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268433467160448262194527 4902650200740672393291791)
          ·
            refine ⟨7353975301111008589937687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902650200740672393291791 7353975301111008589937687)
            ·
              refine ⟨11030962951666512884906531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353975301111008589937687 11030962951666512884906531)
              ·
                refine ⟨16546444427499769327359797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11030962951666512884906531 16546444427499769327359797)
                ·
                  refine ⟨1551229165078103374439981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16546444427499769327359797 1551229165078103374439981)
                  ·
                    refine ⟨581710936904288765414993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551229165078103374439981 581710936904288765414993)
                    ·
                      rfl

theorem cell22_1699317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1699317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699317 prefixEnd_1699317 := by exact prefixLift 1699317
  have htrace : WordTrace (prefixWord ++ tailWord_1699317) baseStart_1699317 baseEnd_1699317 := by
    simpa [prefixWord, tailWord_1699317, baseEnd_1699317] using wordTrace_append hprefix tailTrace_1699317
  have hstable : (prefixWord ++ tailWord_1699317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699317).length < 2 ^ (prefixWord ++ tailWord_1699317).sum := by decide
  have hdescent : baseEnd_1699317 < baseStart_1699317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699420 : List Nat := [2, 2, 4, 1, 2, 1, 1, 9]
def baseStart_1699420 : Nat := 118140960795 + 1699420 * 2 ^ 59
def prefixEnd_1699420 : Nat := 4983230072969 + 3 ^ 40 * 1699420 * 2
def baseEnd_1699420 : Nat := 64638466212136758898853

theorem tailTrace_1699420 : CollatzResearch.WordTrace tailWord_1699420 prefixEnd_1699420 64638466212136758898853 := by
  unfold tailWord_1699420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991469751649526337047857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41321959668866035116063809 30991469751649526337047857)
  ·
    refine ⟨23243602313737144752785893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30991469751649526337047857 23243602313737144752785893)
    ·
      refine ⟨4358175433825714641147355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23243602313737144752785893 4358175433825714641147355)
      ·
        refine ⟨6537263150738571961721033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358175433825714641147355 6537263150738571961721033)
        ·
          refine ⟨4902947363053928971290775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6537263150738571961721033 4902947363053928971290775)
          ·
            refine ⟨7354421044580893456936163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902947363053928971290775 7354421044580893456936163)
            ·
              refine ⟨11031631566871340185404245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354421044580893456936163 11031631566871340185404245)
              ·
                refine ⟨64638466212136758898853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11031631566871340185404245 64638466212136758898853)
                ·
                  rfl

theorem cell22_1699420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_1699420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699420 prefixEnd_1699420 := by exact prefixLift 1699420
  have htrace : WordTrace (prefixWord ++ tailWord_1699420) baseStart_1699420 baseEnd_1699420 := by
    simpa [prefixWord, tailWord_1699420, baseEnd_1699420] using wordTrace_append hprefix tailTrace_1699420
  have hstable : (prefixWord ++ tailWord_1699420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699420).length < 2 ^ (prefixWord ++ tailWord_1699420).sum := by decide
  have hdescent : baseEnd_1699420 < baseStart_1699420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699465 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 5]
def baseStart_1699465 : Nat := 118140960795 + 1699465 * 2 ^ 59
def prefixEnd_1699465 : Nat := 4983230072969 + 3 ^ 40 * 1699465 * 2
def baseEnd_1699465 : Nat := 193920533442955237571513

theorem tailTrace_1699465 : CollatzResearch.WordTrace tailWord_1699465 prefixEnd_1699465 193920533442955237571513 := by
  unfold tailWord_1699465
  simp only [CollatzResearch.WordTrace]
  refine ⟨61984580788136025359483849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41323053858757350239655899 61984580788136025359483849)
  ·
    refine ⟨46488435591102019019612887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61984580788136025359483849 46488435591102019019612887)
    ·
      refine ⟨69732653386653028529419331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46488435591102019019612887 69732653386653028529419331)
      ·
        refine ⟨104598980079979542794128997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69732653386653028529419331 104598980079979542794128997)
        ·
          refine ⟨19612308764996164273899187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104598980079979542794128997 19612308764996164273899187)
          ·
            refine ⟨29418463147494246410848781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19612308764996164273899187 29418463147494246410848781)
            ·
              refine ⟨11031923680310342404068293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29418463147494246410848781 11031923680310342404068293)
              ·
                refine ⟨2068485690058189200762805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11031923680310342404068293 2068485690058189200762805)
                ·
                  refine ⟨193920533442955237571513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068485690058189200762805 193920533442955237571513)
                  ·
                    rfl

theorem cell22_1699465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_1699465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699465 prefixEnd_1699465 := by exact prefixLift 1699465
  have htrace : WordTrace (prefixWord ++ tailWord_1699465) baseStart_1699465 baseEnd_1699465 := by
    simpa [prefixWord, tailWord_1699465, baseEnd_1699465] using wordTrace_append hprefix tailTrace_1699465
  have hstable : (prefixWord ++ tailWord_1699465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699465).length < 2 ^ (prefixWord ++ tailWord_1699465).sum := by decide
  have hdescent : baseEnd_1699465 < baseStart_1699465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699480 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1699480 : Nat := 118140960795 + 1699480 * 2 ^ 59
def prefixEnd_1699480 : Nat := 4983230072969 + 3 ^ 40 * 1699480 * 2
def baseEnd_1699480 : Nat := 581766735135410673589493

theorem tailTrace_1699480 : CollatzResearch.WordTrace tailWord_1699480 prefixEnd_1699480 581766735135410673589493 := by
  unfold tailWord_1699480
  simp only [CollatzResearch.WordTrace]
  refine ⟨30992563941540841460639947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41323418588721121947519929 30992563941540841460639947)
  ·
    refine ⟨46488845912311262190959921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30992563941540841460639947 46488845912311262190959921)
    ·
      refine ⟨34866634434233446643219941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46488845912311262190959921 34866634434233446643219941)
      ·
        refine ⟨6537493956418771245603739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34866634434233446643219941 6537493956418771245603739)
        ·
          refine ⟨9806240934628156868405609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537493956418771245603739 9806240934628156868405609)
          ·
            refine ⟨7354680700971117651304207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9806240934628156868405609 7354680700971117651304207)
            ·
              refine ⟨11032021051456676476956311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354680700971117651304207 11032021051456676476956311)
              ·
                refine ⟨16548031577185014715434467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11032021051456676476956311 16548031577185014715434467)
                ·
                  refine ⟨24822047365777522073151701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16548031577185014715434467 24822047365777522073151701)
                  ·
                    refine ⟨581766735135410673589493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24822047365777522073151701 581766735135410673589493)
                    ·
                      rfl

theorem cell22_1699480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1699480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699480 prefixEnd_1699480 := by exact prefixLift 1699480
  have htrace : WordTrace (prefixWord ++ tailWord_1699480) baseStart_1699480 baseEnd_1699480 := by
    simpa [prefixWord, tailWord_1699480, baseEnd_1699480] using wordTrace_append hprefix tailTrace_1699480
  have hstable : (prefixWord ++ tailWord_1699480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699480).length < 2 ^ (prefixWord ++ tailWord_1699480).sum := by decide
  have hdescent : baseEnd_1699480 < baseStart_1699480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699527 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 4]
def baseStart_1699527 : Nat := 118140960795 + 1699527 * 2 ^ 59
def prefixEnd_1699527 : Nat := 4983230072969 + 3 ^ 40 * 1699527 * 2
def baseEnd_1699527 : Nat := 193927608065306072554783

theorem tailTrace_1699527 : CollatzResearch.WordTrace tailWord_1699527 prefixEnd_1699527 193927608065306072554783 := by
  unfold tailWord_1699527
  simp only [CollatzResearch.WordTrace]
  refine ⟨61986842113911409948240835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41324561409274273298827223 61986842113911409948240835)
  ·
    refine ⟨92980263170867114922361253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61986842113911409948240835 92980263170867114922361253)
    ·
      refine ⟨17433799344537584047942735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92980263170867114922361253 17433799344537584047942735)
      ·
        refine ⟨26150699016806376071914103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433799344537584047942735 26150699016806376071914103)
        ·
          refine ⟨39226048525209564107871155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26150699016806376071914103 39226048525209564107871155)
          ·
            refine ⟨58839072787814346161806733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39226048525209564107871155 58839072787814346161806733)
            ·
              refine ⟨22064652295430379810677525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58839072787814346161806733 22064652295430379810677525)
              ·
                refine ⟨1034280576348299053625509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22064652295430379810677525 1034280576348299053625509)
                ·
                  refine ⟨193927608065306072554783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034280576348299053625509 193927608065306072554783)
                  ·
                    rfl

theorem cell22_1699527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 4].length) (baseStart_1699527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699527 prefixEnd_1699527 := by exact prefixLift 1699527
  have htrace : WordTrace (prefixWord ++ tailWord_1699527) baseStart_1699527 baseEnd_1699527 := by
    simpa [prefixWord, tailWord_1699527, baseEnd_1699527] using wordTrace_append hprefix tailTrace_1699527
  have hstable : (prefixWord ++ tailWord_1699527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699527).length < 2 ^ (prefixWord ++ tailWord_1699527).sum := by decide
  have hdescent : baseEnd_1699527 < baseStart_1699527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699557 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_1699557 : Nat := 118140960795 + 1699557 * 2 ^ 59
def prefixEnd_1699557 : Nat := 4983230072969 + 3 ^ 40 * 1699557 * 2
def baseEnd_1699557 : Nat := 581793093809008139414257

theorem tailTrace_1699557 : CollatzResearch.WordTrace tailWord_1699557 prefixEnd_1699557 581793093809008139414257 := by
  unfold tailWord_1699557
  simp only [CollatzResearch.WordTrace]
  refine ⟨61987936303802725071832925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41325290869201816714555283 61987936303802725071832925)
  ·
    refine ⟨23245476113926021901937347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61987936303802725071832925 23245476113926021901937347)
    ·
      refine ⟨34868214170889032852906021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23245476113926021901937347 34868214170889032852906021)
      ·
        refine ⟨6537790157041693659919879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34868214170889032852906021 6537790157041693659919879)
        ·
          refine ⟨9806685235562540489879819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537790157041693659919879 9806685235562540489879819)
          ·
            refine ⟨14710027853343810734819729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806685235562540489879819 14710027853343810734819729)
            ·
              refine ⟨11032520890007858051114797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14710027853343810734819729 11032520890007858051114797)
              ·
                refine ⟨4137195333752946769168049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11032520890007858051114797 4137195333752946769168049)
                ·
                  refine ⟨3102896500314710076876037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137195333752946769168049 3102896500314710076876037)
                  ·
                    refine ⟨581793093809008139414257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3102896500314710076876037 581793093809008139414257)
                    ·
                      rfl

theorem cell22_1699557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_1699557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699557 prefixEnd_1699557 := by exact prefixLift 1699557
  have htrace : WordTrace (prefixWord ++ tailWord_1699557) baseStart_1699557 baseEnd_1699557 := by
    simpa [prefixWord, tailWord_1699557, baseEnd_1699557] using wordTrace_append hprefix tailTrace_1699557
  have hstable : (prefixWord ++ tailWord_1699557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699557).length < 2 ^ (prefixWord ++ tailWord_1699557).sum := by decide
  have hdescent : baseEnd_1699557 < baseStart_1699557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699574 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1699574 : Nat := 118140960795 + 1699574 * 2 ^ 59
def prefixEnd_1699574 : Nat := 4983230072969 + 3 ^ 40 * 1699574 * 2
def baseEnd_1699574 : Nat := 581798913256425761739205

theorem tailTrace_1699574 : CollatzResearch.WordTrace tailWord_1699574 prefixEnd_1699574 581798913256425761739205 := by
  unfold tailWord_1699574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874284771546321060950111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41325704229827424650134517 3874284771546321060950111)
  ·
    refine ⟨5811427157319481591425167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874284771546321060950111 5811427157319481591425167)
    ·
      refine ⟨8717140735979222387137751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811427157319481591425167 8717140735979222387137751)
      ·
        refine ⟨13075711103968833580706627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717140735979222387137751 13075711103968833580706627)
        ·
          refine ⟨19613566655953250371059941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075711103968833580706627 19613566655953250371059941)
          ·
            refine ⟨3677543747991234444573739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19613566655953250371059941 3677543747991234444573739)
            ·
              refine ⟨5516315621986851666860609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677543747991234444573739 5516315621986851666860609)
              ·
                refine ⟨4137236716490138750145457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516315621986851666860609 4137236716490138750145457)
                ·
                  refine ⟨3102927537367604062609093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4137236716490138750145457 3102927537367604062609093)
                  ·
                    refine ⟨581798913256425761739205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3102927537367604062609093 581798913256425761739205)
                    ·
                      rfl

theorem cell22_1699574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1699574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699574 prefixEnd_1699574 := by exact prefixLift 1699574
  have htrace : WordTrace (prefixWord ++ tailWord_1699574) baseStart_1699574 baseEnd_1699574 := by
    simpa [prefixWord, tailWord_1699574, baseEnd_1699574] using wordTrace_append hprefix tailTrace_1699574
  have hstable : (prefixWord ++ tailWord_1699574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699574).length < 2 ^ (prefixWord ++ tailWord_1699574).sum := by decide
  have hdescent : baseEnd_1699574 < baseStart_1699574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699597 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1699597 : Nat := 118140960795 + 1699597 * 2 ^ 59
def prefixEnd_1699597 : Nat := 4983230072969 + 3 ^ 40 * 1699597 * 2
def baseEnd_1699597 : Nat := 581806786626461368414135

theorem tailTrace_1699597 : CollatzResearch.WordTrace tailWord_1699597 prefixEnd_1699597 581806786626461368414135 := by
  unfold tailWord_1699597
  simp only [CollatzResearch.WordTrace]
  refine ⟨61989395223657811903289045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41326263482438541268859363 61989395223657811903289045)
  ·
    refine ⟨1452876450554479966483337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 61989395223657811903289045 1452876450554479966483337)
    ·
      refine ⟨1089657337915859974862503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1452876450554479966483337 1089657337915859974862503)
      ·
        refine ⟨1634486006873789962293755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089657337915859974862503 1634486006873789962293755)
        ·
          refine ⟨2451729010310684943440633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634486006873789962293755 2451729010310684943440633)
          ·
            refine ⟨1838796757733013707580475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2451729010310684943440633 1838796757733013707580475)
            ·
              refine ⟨2758195136599520561370713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838796757733013707580475 2758195136599520561370713)
              ·
                refine ⟨2068646352449640421028035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758195136599520561370713 2068646352449640421028035)
                ·
                  refine ⟨3102969528674460631542053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068646352449640421028035 3102969528674460631542053)
                  ·
                    refine ⟨581806786626461368414135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3102969528674460631542053 581806786626461368414135)
                    ·
                      rfl

theorem cell22_1699597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1699597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699597 prefixEnd_1699597 := by exact prefixLift 1699597
  have htrace : WordTrace (prefixWord ++ tailWord_1699597) baseStart_1699597 baseEnd_1699597 := by
    simpa [prefixWord, tailWord_1699597, baseEnd_1699597] using wordTrace_append hprefix tailTrace_1699597
  have hstable : (prefixWord ++ tailWord_1699597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699597).length < 2 ^ (prefixWord ++ tailWord_1699597).sum := by decide
  have hdescent : baseEnd_1699597 < baseStart_1699597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699634 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_1699634 : Nat := 118140960795 + 1699634 * 2 ^ 59
def prefixEnd_1699634 : Nat := 4983230072969 + 3 ^ 40 * 1699634 * 2
def baseEnd_1699634 : Nat := 193939817494201868413007

theorem tailTrace_1699634 : CollatzResearch.WordTrace tailWord_1699634 prefixEnd_1699634 193939817494201868413007 := by
  unfold tailWord_1699634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497686181130941805596489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41327163149682511481590637 15497686181130941805596489)
  ·
    refine ⟨11623264635848206354197367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15497686181130941805596489 11623264635848206354197367)
    ·
      refine ⟨17434896953772309531296051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11623264635848206354197367 17434896953772309531296051)
      ·
        refine ⟨26152345430658464296944077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17434896953772309531296051 26152345430658464296944077)
        ·
          refine ⟨9807129536496924111354029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26152345430658464296944077 9807129536496924111354029)
          ·
            refine ⟨3677673576186346541757761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9807129536496924111354029 3677673576186346541757761)
            ·
              refine ⟨2758255182139759906318321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3677673576186346541757761 2758255182139759906318321)
              ·
                refine ⟨2068691386604819929738741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758255182139759906318321 2068691386604819929738741)
                ·
                  refine ⟨193939817494201868413007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068691386604819929738741 193939817494201868413007)
                  ·
                    rfl

theorem cell22_1699634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_1699634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699634 prefixEnd_1699634 := by exact prefixLift 1699634
  have htrace : WordTrace (prefixWord ++ tailWord_1699634) baseStart_1699634 baseEnd_1699634 := by
    simpa [prefixWord, tailWord_1699634, baseEnd_1699634] using wordTrace_append hprefix tailTrace_1699634
  have hstable : (prefixWord ++ tailWord_1699634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699634).length < 2 ^ (prefixWord ++ tailWord_1699634).sum := by decide
  have hdescent : baseEnd_1699634 < baseStart_1699634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699679 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 4]
def baseStart_1699679 : Nat := 118140960795 + 1699679 * 2 ^ 59
def prefixEnd_1699679 : Nat := 4983230072969 + 3 ^ 40 * 1699679 * 2
def baseEnd_1699679 : Nat := 193944952300746829287961

theorem tailTrace_1699679 : CollatzResearch.WordTrace tailWord_1699679 prefixEnd_1699679 193944952300746829287961 := by
  unfold tailWord_1699679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61992386009360739907774091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41328257339573826605182727 61992386009360739907774091)
  ·
    refine ⟨92988579014041109861661137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61992386009360739907774091 92988579014041109861661137)
    ·
      refine ⟨69741434260530832396245853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92988579014041109861661137 69741434260530832396245853)
      ·
        refine ⟨26153037847699062148592195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69741434260530832396245853 26153037847699062148592195)
        ·
          refine ⟨39229556771548593222888293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26153037847699062148592195 39229556771548593222888293)
          ·
            refine ⟨7355541894665361229291555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39229556771548593222888293 7355541894665361229291555)
            ·
              refine ⟨11033312841998041843937333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355541894665361229291555 11033312841998041843937333)
              ·
                refine ⟨1034373078937316422869125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11033312841998041843937333 1034373078937316422869125)
                ·
                  refine ⟨193944952300746829287961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034373078937316422869125 193944952300746829287961)
                  ·
                    rfl

theorem cell22_1699679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 4].length) (baseStart_1699679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699679 prefixEnd_1699679 := by exact prefixLift 1699679
  have htrace : WordTrace (prefixWord ++ tailWord_1699679) baseStart_1699679 baseEnd_1699679 := by
    simpa [prefixWord, tailWord_1699679, baseEnd_1699679] using wordTrace_append hprefix tailTrace_1699679
  have hstable : (prefixWord ++ tailWord_1699679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699679).length < 2 ^ (prefixWord ++ tailWord_1699679).sum := by decide
  have hdescent : baseEnd_1699679 < baseStart_1699679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699767 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1699767 : Nat := 118140960795 + 1699767 * 2 ^ 59
def prefixEnd_1699767 : Nat := 4983230072969 + 3 ^ 40 * 1699767 * 2
def baseEnd_1699767 : Nat := 581864981100637591663613

theorem tailTrace_1699767 : CollatzResearch.WordTrace tailWord_1699767 prefixEnd_1699767 581864981100637591663613 := by
  unfold tailWord_1699767
  simp only [CollatzResearch.WordTrace]
  refine ⟨61995595633041930936977555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41330397088694620624651703 61995595633041930936977555)
  ·
    refine ⟨92993393449562896405466333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61995595633041930936977555 92993393449562896405466333)
    ·
      refine ⟨34872522543586086152049875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92993393449562896405466333 34872522543586086152049875)
      ·
        refine ⟨52308783815379129228074813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34872522543586086152049875 52308783815379129228074813)
        ·
          refine ⟨19615793930767173460528055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52308783815379129228074813 19615793930767173460528055)
          ·
            refine ⟨29423690896150760190792083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19615793930767173460528055 29423690896150760190792083)
            ·
              refine ⟨44135536344226140286188125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29423690896150760190792083 44135536344226140286188125)
              ·
                refine ⟨16550826129084802607320547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44135536344226140286188125 16550826129084802607320547)
                ·
                  refine ⟨24826239193627203910980821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16550826129084802607320547 24826239193627203910980821)
                  ·
                    refine ⟨581864981100637591663613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24826239193627203910980821 581864981100637591663613)
                    ·
                      rfl

theorem cell22_1699767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1699767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699767 prefixEnd_1699767 := by exact prefixLift 1699767
  have htrace : WordTrace (prefixWord ++ tailWord_1699767) baseStart_1699767 baseEnd_1699767 := by
    simpa [prefixWord, tailWord_1699767, baseEnd_1699767] using wordTrace_append hprefix tailTrace_1699767
  have hstable : (prefixWord ++ tailWord_1699767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699767).length < 2 ^ (prefixWord ++ tailWord_1699767).sum := by decide
  have hdescent : baseEnd_1699767 < baseStart_1699767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699769 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 5]
def baseStart_1699769 : Nat := 118140960795 + 1699769 * 2 ^ 59
def prefixEnd_1699769 : Nat := 4983230072969 + 3 ^ 40 * 1699769 * 2
def baseEnd_1699769 : Nat := 193955221913836751037869

theorem tailTrace_1699769 : CollatzResearch.WordTrace tailWord_1699769 prefixEnd_1699769 193955221913836751037869 := by
  unfold tailWord_1699769
  simp only [CollatzResearch.WordTrace]
  refine ⟨61995668579034685278550361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41330445719356456852366907 61995668579034685278550361)
  ·
    refine ⟨46496751434276013958912771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61995668579034685278550361 46496751434276013958912771)
    ·
      refine ⟨69745127151414020938369157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46496751434276013958912771 69745127151414020938369157)
      ·
        refine ⟨13077211340890128925944217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69745127151414020938369157 13077211340890128925944217)
        ·
          refine ⟨9807908505667596694458163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13077211340890128925944217 9807908505667596694458163)
          ·
            refine ⟨14711862758501395041687245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9807908505667596694458163 14711862758501395041687245)
            ·
              refine ⟨5516948534438023140632717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14711862758501395041687245 5516948534438023140632717)
              ·
                refine ⟨2068855700414258677737269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5516948534438023140632717 2068855700414258677737269)
                ·
                  refine ⟨193955221913836751037869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068855700414258677737269 193955221913836751037869)
                  ·
                    rfl

theorem cell22_1699769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_1699769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699769 prefixEnd_1699769 := by exact prefixLift 1699769
  have htrace : WordTrace (prefixWord ++ tailWord_1699769) baseStart_1699769 baseEnd_1699769 := by
    simpa [prefixWord, tailWord_1699769, baseEnd_1699769] using wordTrace_append hprefix tailTrace_1699769
  have hstable : (prefixWord ++ tailWord_1699769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699769).length < 2 ^ (prefixWord ++ tailWord_1699769).sum := by decide
  have hdescent : baseEnd_1699769 < baseStart_1699769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699850 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_1699850 : Nat := 118140960795 + 1699850 * 2 ^ 59
def prefixEnd_1699850 : Nat := 4983230072969 + 3 ^ 40 * 1699850 * 2
def baseEnd_1699850 : Nat := 581893393696853041838359

theorem tailTrace_1699850 : CollatzResearch.WordTrace tailWord_1699850 prefixEnd_1699850 581893393696853041838359 := by
  unfold tailWord_1699850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15499655722935309028062251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41332415261160824074832669 15499655722935309028062251)
  ·
    refine ⟨23249483584402963542093377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15499655722935309028062251 23249483584402963542093377)
    ·
      refine ⟨17437112688302222656570033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23249483584402963542093377 17437112688302222656570033)
      ·
        refine ⟨13077834516226666992427525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17437112688302222656570033 13077834516226666992427525)
        ·
          refine ⟨2452093971792500061080161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13077834516226666992427525 2452093971792500061080161)
          ·
            refine ⟨1839070478844375045810121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452093971792500061080161 1839070478844375045810121)
            ·
              refine ⟨1379302859133281284357591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839070478844375045810121 1379302859133281284357591)
              ·
                refine ⟨2068954288699921926536387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379302859133281284357591 2068954288699921926536387)
                ·
                  refine ⟨3103431433049882889804581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068954288699921926536387 3103431433049882889804581)
                  ·
                    refine ⟨581893393696853041838359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103431433049882889804581 581893393696853041838359)
                    ·
                      rfl

theorem cell22_1699850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_1699850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699850 prefixEnd_1699850 := by exact prefixLift 1699850
  have htrace : WordTrace (prefixWord ++ tailWord_1699850) baseStart_1699850 baseEnd_1699850 := by
    simpa [prefixWord, tailWord_1699850, baseEnd_1699850] using wordTrace_append hprefix tailTrace_1699850
  have hstable : (prefixWord ++ tailWord_1699850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699850).length < 2 ^ (prefixWord ++ tailWord_1699850).sum := by decide
  have hdescent : baseEnd_1699850 < baseStart_1699850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699863 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 4, 3]
def baseStart_1699863 : Nat := 118140960795 + 1699863 * 2 ^ 59
def prefixEnd_1699863 : Nat := 4983230072969 + 3 ^ 40 * 1699863 * 2
def baseEnd_1699863 : Nat := 581897843862525341263319

theorem tailTrace_1699863 : CollatzResearch.WordTrace tailWord_1699863 prefixEnd_1699863 581897843862525341263319 := by
  unfold tailWord_1699863
  simp only [CollatzResearch.WordTrace]
  refine ⟨61999097040694139332472243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41332731360462759554981495 61999097040694139332472243)
  ·
    refine ⟨92998645561041208998708365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61999097040694139332472243 92998645561041208998708365)
    ·
      refine ⟨34874492085390453374515637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92998645561041208998708365 34874492085390453374515637)
      ·
        refine ⟨3269483633005355003860841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34874492085390453374515637 3269483633005355003860841)
        ·
          refine ⟨2452112724754016252895631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269483633005355003860841 2452112724754016252895631)
          ·
            refine ⟨3678169087131024379343447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452112724754016252895631 3678169087131024379343447)
            ·
              refine ⟨5517253630696536569015171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678169087131024379343447 5517253630696536569015171)
              ·
                refine ⟨8275880446044804853522757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517253630696536569015171 8275880446044804853522757)
                ·
                  refine ⟨1551727583633400910035517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8275880446044804853522757 1551727583633400910035517)
                  ·
                    refine ⟨581897843862525341263319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551727583633400910035517 581897843862525341263319)
                    ·
                      rfl

theorem cell22_1699863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_1699863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699863 prefixEnd_1699863 := by exact prefixLift 1699863
  have htrace : WordTrace (prefixWord ++ tailWord_1699863) baseStart_1699863 baseEnd_1699863 := by
    simpa [prefixWord, tailWord_1699863, baseEnd_1699863] using wordTrace_append hprefix tailTrace_1699863
  have hstable : (prefixWord ++ tailWord_1699863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699863).length < 2 ^ (prefixWord ++ tailWord_1699863).sum := by decide
  have hdescent : baseEnd_1699863 < baseStart_1699863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699880 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1699880 : Nat := 118140960795 + 1699880 * 2 ^ 59
def prefixEnd_1699880 : Nat := 4983230072969 + 3 ^ 40 * 1699880 * 2
def baseEnd_1699880 : Nat := 581903663309942963588267

theorem tailTrace_1699880 : CollatzResearch.WordTrace tailWord_1699880 prefixEnd_1699880 581903663309942963588267 := by
  unfold tailWord_1699880
  simp only [CollatzResearch.WordTrace]
  refine ⟨30999858540816275617920547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41333144721088367490560729 30999858540816275617920547)
  ·
    refine ⟨46499787811224413426880821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30999858540816275617920547 46499787811224413426880821)
    ·
      refine ⟨4359355107302288758770077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46499787811224413426880821 4359355107302288758770077)
      ·
        refine ⟨1634758165238358284538779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4359355107302288758770077 1634758165238358284538779)
        ·
          refine ⟨2452137247857537426808169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634758165238358284538779 2452137247857537426808169)
          ·
            refine ⟨1839102935893153070106127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452137247857537426808169 1839102935893153070106127)
            ·
              refine ⟨2758654403839729605159191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839102935893153070106127 2758654403839729605159191)
              ·
                refine ⟨4137981605759594407738787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758654403839729605159191 4137981605759594407738787)
                ·
                  refine ⟨6206972408639391611608181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137981605759594407738787 6206972408639391611608181)
                  ·
                    refine ⟨581903663309942963588267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6206972408639391611608181 581903663309942963588267)
                    ·
                      rfl

theorem cell22_1699880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1699880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699880 prefixEnd_1699880 := by exact prefixLift 1699880
  have htrace : WordTrace (prefixWord ++ tailWord_1699880) baseStart_1699880 baseEnd_1699880 := by
    simpa [prefixWord, tailWord_1699880, baseEnd_1699880] using wordTrace_append hprefix tailTrace_1699880
  have hstable : (prefixWord ++ tailWord_1699880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699880).length < 2 ^ (prefixWord ++ tailWord_1699880).sum := by decide
  have hdescent : baseEnd_1699880 < baseStart_1699880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699891 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 3, 3]
def baseStart_1699891 : Nat := 118140960795 + 1699891 * 2 ^ 59
def prefixEnd_1699891 : Nat := 4983230072969 + 3 ^ 40 * 1699891 * 2
def baseEnd_1699891 : Nat := 581907428834742601563233

theorem tailTrace_1699891 : CollatzResearch.WordTrace tailWord_1699891 prefixEnd_1699891 581907428834742601563233 := by
  unfold tailWord_1699891
  simp only [CollatzResearch.WordTrace]
  refine ⟨62000118284592700114491527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41333412189728466742994351 62000118284592700114491527)
  ·
    refine ⟨93000177426889050171737291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62000118284592700114491527 93000177426889050171737291)
    ·
      refine ⟨139500266140333575257605937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93000177426889050171737291 139500266140333575257605937)
      ·
        refine ⟨104625199605250181443204453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139500266140333575257605937 104625199605250181443204453)
        ·
          refine ⟨19617224925984409020600835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104625199605250181443204453 19617224925984409020600835)
          ·
            refine ⟨29425837388976613530901253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617224925984409020600835 29425837388976613530901253)
            ·
              refine ⟨5517344510433115037043985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29425837388976613530901253 5517344510433115037043985)
              ·
                refine ⟨4138008382824836277782989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517344510433115037043985 4138008382824836277782989)
                ·
                  refine ⟨1551753143559313604168621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4138008382824836277782989 1551753143559313604168621)
                  ·
                    refine ⟨581907428834742601563233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551753143559313604168621 581907428834742601563233)
                    ·
                      rfl

theorem cell22_1699891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3].length) (baseStart_1699891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699891 prefixEnd_1699891 := by exact prefixLift 1699891
  have htrace : WordTrace (prefixWord ++ tailWord_1699891) baseStart_1699891 baseEnd_1699891 := by
    simpa [prefixWord, tailWord_1699891, baseEnd_1699891] using wordTrace_append hprefix tailTrace_1699891
  have hstable : (prefixWord ++ tailWord_1699891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699891).length < 2 ^ (prefixWord ++ tailWord_1699891).sum := by decide
  have hdescent : baseEnd_1699891 < baseStart_1699891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699904 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_1699904 : Nat := 118140960795 + 1699904 * 2 ^ 59
def prefixEnd_1699904 : Nat := 4983230072969 + 3 ^ 40 * 1699904 * 2
def baseEnd_1699904 : Nat := 193970626333471633662731

theorem tailTrace_1699904 : CollatzResearch.WordTrace tailWord_1699904 prefixEnd_1699904 193970626333471633662731 := by
  unfold tailWord_1699904
  simp only [CollatzResearch.WordTrace]
  refine ⟨31000296216772801667357383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41333728289030402223143177 31000296216772801667357383)
  ·
    refine ⟨46500444325159202501036075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31000296216772801667357383 46500444325159202501036075)
    ·
      refine ⟨69750666487738803751554113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46500444325159202501036075 69750666487738803751554113)
      ·
        refine ⟨52312999865804102813665585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69750666487738803751554113 52312999865804102813665585)
        ·
          refine ⟨39234749899353077110249189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52312999865804102813665585 39234749899353077110249189)
          ·
            refine ⟨7356515606128701958171723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39234749899353077110249189 7356515606128701958171723)
            ·
              refine ⟨11034773409193052937257585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356515606128701958171723 11034773409193052937257585)
              ·
                refine ⟨8276080056894789702943189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11034773409193052937257585 8276080056894789702943189)
                ·
                  refine ⟨193970626333471633662731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8276080056894789702943189 193970626333471633662731)
                  ·
                    rfl

theorem cell22_1699904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_1699904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699904 prefixEnd_1699904 := by exact prefixLift 1699904
  have htrace : WordTrace (prefixWord ++ tailWord_1699904) baseStart_1699904 baseEnd_1699904 := by
    simpa [prefixWord, tailWord_1699904, baseEnd_1699904] using wordTrace_append hprefix tailTrace_1699904
  have hstable : (prefixWord ++ tailWord_1699904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699904).length < 2 ^ (prefixWord ++ tailWord_1699904).sum := by decide
  have hdescent : baseEnd_1699904 < baseStart_1699904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699951 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_1699951 : Nat := 118140960795 + 1699951 * 2 ^ 59
def prefixEnd_1699951 : Nat := 4983230072969 + 3 ^ 40 * 1699951 * 2
def baseEnd_1699951 : Nat := 581927968060922445063049

theorem tailTrace_1699951 : CollatzResearch.WordTrace tailWord_1699951 prefixEnd_1699951 581927968060922445063049 := by
  unfold tailWord_1699951
  simp only [CollatzResearch.WordTrace]
  refine ⟨62002306664375330361675707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41334871109583553574450471 62002306664375330361675707)
  ·
    refine ⟨93003459996562995542513561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62002306664375330361675707 93003459996562995542513561)
    ·
      refine ⟨69752594997422246656885171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93003459996562995542513561 69752594997422246656885171)
      ·
        refine ⟨104628892496133369985327757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69752594997422246656885171 104628892496133369985327757)
        ·
          refine ⟨39235834686050013744497909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104628892496133369985327757 39235834686050013744497909)
          ·
            refine ⟨3678359501817188788546679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39235834686050013744497909 3678359501817188788546679)
            ·
              refine ⟨5517539252725783182820019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678359501817188788546679 5517539252725783182820019)
              ·
                refine ⟨8276308879088674774230029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517539252725783182820019 8276308879088674774230029)
                ·
                  refine ⟨3103615829658253040336261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8276308879088674774230029 3103615829658253040336261)
                  ·
                    refine ⟨581927968060922445063049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103615829658253040336261 581927968060922445063049)
                    ·
                      rfl

theorem cell22_1699951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_1699951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699951 prefixEnd_1699951 := by exact prefixLift 1699951
  have htrace : WordTrace (prefixWord ++ tailWord_1699951) baseStart_1699951 baseEnd_1699951 := by
    simpa [prefixWord, tailWord_1699951, baseEnd_1699951] using wordTrace_append hprefix tailTrace_1699951
  have hstable : (prefixWord ++ tailWord_1699951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699951).length < 2 ^ (prefixWord ++ tailWord_1699951).sum := by decide
  have hdescent : baseEnd_1699951 < baseStart_1699951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699979 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_1699979 : Nat := 118140960795 + 1699979 * 2 ^ 59
def prefixEnd_1699979 : Nat := 4983230072969 + 3 ^ 40 * 1699979 * 2
def baseEnd_1699979 : Nat := 581937553033139705362963

theorem tailTrace_1699979 : CollatzResearch.WordTrace tailWord_1699979 prefixEnd_1699979 581937553033139705362963 := by
  unfold tailWord_1699979
  simp only [CollatzResearch.WordTrace]
  refine ⟨62003327908273891143694991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41335551938849260762463327 62003327908273891143694991)
  ·
    refine ⟨93004991862410836715542487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62003327908273891143694991 93004991862410836715542487)
    ·
      refine ⟨139507487793616255073313731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93004991862410836715542487 139507487793616255073313731)
      ·
        refine ⟨209261231690424382609970597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139507487793616255073313731 209261231690424382609970597)
        ·
          refine ⟨39236480941954571739369487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209261231690424382609970597 39236480941954571739369487)
          ·
            refine ⟨58854721412931857609054231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39236480941954571739369487 58854721412931857609054231)
            ·
              refine ⟨88282082119397786413581347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58854721412931857609054231 88282082119397786413581347)
              ·
                refine ⟨132423123179096679620372021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88282082119397786413581347 132423123179096679620372021)
                ·
                  refine ⟨12414667798040313714409877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132423123179096679620372021 12414667798040313714409877)
                  ·
                    refine ⟨581937553033139705362963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12414667798040313714409877 581937553033139705362963)
                    ·
                      rfl

theorem cell22_1699979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_1699979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699979 prefixEnd_1699979 := by exact prefixLift 1699979
  have htrace : WordTrace (prefixWord ++ tailWord_1699979) baseStart_1699979 baseEnd_1699979 := by
    simpa [prefixWord, tailWord_1699979, baseEnd_1699979] using wordTrace_append hprefix tailTrace_1699979
  have hstable : (prefixWord ++ tailWord_1699979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699979).length < 2 ^ (prefixWord ++ tailWord_1699979).sum := by decide
  have hdescent : baseEnd_1699979 < baseStart_1699979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699996 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1699996 : Nat := 118140960795 + 1699996 * 2 ^ 59
def prefixEnd_1699996 : Nat := 4983230072969 + 3 ^ 40 * 1699996 * 2
def baseEnd_1699996 : Nat := 581943372480557327687911

theorem tailTrace_1699996 : CollatzResearch.WordTrace tailWord_1699996 prefixEnd_1699996 581943372480557327687911 := by
  unfold tailWord_1699996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001973974606151523531921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41335965299474868698042561 31001973974606151523531921)
  ·
    refine ⟨23251480480954613642648941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31001973974606151523531921 23251480480954613642648941)
    ·
      refine ⟨8719305180357980115993353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23251480480954613642648941 8719305180357980115993353)
      ·
        refine ⟨6539478885268485086995015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8719305180357980115993353 6539478885268485086995015)
        ·
          refine ⟨9809218327902727630492523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539478885268485086995015 9809218327902727630492523)
          ·
            refine ⟨14713827491854091445738785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9809218327902727630492523 14713827491854091445738785)
            ·
              refine ⟨11035370618890568584304089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14713827491854091445738785 11035370618890568584304089)
              ·
                refine ⟨8276527964167926438228067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11035370618890568584304089 8276527964167926438228067)
                ·
                  refine ⟨12414791946251889657342101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276527964167926438228067 12414791946251889657342101)
                  ·
                    refine ⟨581943372480557327687911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12414791946251889657342101 581943372480557327687911)
                    ·
                      rfl

theorem cell22_1699996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1699996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1699996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1699996 prefixEnd_1699996 := by exact prefixLift 1699996
  have htrace : WordTrace (prefixWord ++ tailWord_1699996) baseStart_1699996 baseEnd_1699996 := by
    simpa [prefixWord, tailWord_1699996, baseEnd_1699996] using wordTrace_append hprefix tailTrace_1699996
  have hstable : (prefixWord ++ tailWord_1699996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699996).length < 2 ^ (prefixWord ++ tailWord_1699996).sum := by decide
  have hdescent : baseEnd_1699996 < baseStart_1699996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700013 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1700013 : Nat := 118140960795 + 1700013 * 2 ^ 59
def prefixEnd_1700013 : Nat := 4983230072969 + 3 ^ 40 * 1700013 * 2
def baseEnd_1700013 : Nat := 581949191927974950012859

theorem tailTrace_1700013 : CollatzResearch.WordTrace tailWord_1700013 prefixEnd_1700013 581949191927974950012859 := by
  unfold tailWord_1700013
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004567990150714950432693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41336378660100476633621795 62004567990150714950432693)
  ·
    refine ⟨5812928249076629526603065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62004567990150714950432693 5812928249076629526603065)
    ·
      refine ⟨4359696186807472144952299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5812928249076629526603065 4359696186807472144952299)
      ·
        refine ⟨6539544280211208217428449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359696186807472144952299 6539544280211208217428449)
        ·
          refine ⟨4904658210158406163071337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539544280211208217428449 4904658210158406163071337)
          ·
            refine ⟨3678493657618804622303503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904658210158406163071337 3678493657618804622303503)
            ·
              refine ⟨5517740486428206933455255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678493657618804622303503 5517740486428206933455255)
              ·
                refine ⟨8276610729642310400182883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517740486428206933455255 8276610729642310400182883)
                ·
                  refine ⟨12414916094463465600274325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276610729642310400182883 12414916094463465600274325)
                  ·
                    refine ⟨581949191927974950012859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12414916094463465600274325 581949191927974950012859)
                    ·
                      rfl

theorem cell22_1700013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1700013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700013 prefixEnd_1700013 := by exact prefixLift 1700013
  have htrace : WordTrace (prefixWord ++ tailWord_1700013) baseStart_1700013 baseEnd_1700013 := by
    simpa [prefixWord, tailWord_1700013, baseEnd_1700013] using wordTrace_append hprefix tailTrace_1700013
  have hstable : (prefixWord ++ tailWord_1700013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700013).length < 2 ^ (prefixWord ++ tailWord_1700013).sum := by decide
  have hdescent : baseEnd_1700013 < baseStart_1700013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700043 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 3, 3]
def baseStart_1700043 : Nat := 118140960795 + 1700043 * 2 ^ 59
def prefixEnd_1700043 : Nat := 4983230072969 + 3 ^ 40 * 1700043 * 2
def baseEnd_1700043 : Nat := 581959461541064871762767

theorem tailTrace_1700043 : CollatzResearch.WordTrace tailWord_1700043 prefixEnd_1700043 581959461541064871762767 := by
  unfold tailWord_1700043
  simp only [CollatzResearch.WordTrace]
  refine ⟨62005662180042030074024783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41337108120028020049349855 62005662180042030074024783)
  ·
    refine ⟨93008493270063045111037175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62005662180042030074024783 93008493270063045111037175)
    ·
      refine ⟨139512739905094567666555763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93008493270063045111037175 139512739905094567666555763)
      ·
        refine ⟨209269109857641851499833645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139512739905094567666555763 209269109857641851499833645)
        ·
          refine ⟨78475916196615694312437617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209269109857641851499833645 78475916196615694312437617)
          ·
            refine ⟨58856937147461770734328213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78475916196615694312437617 58856937147461770734328213)
            ·
              refine ⟨2758918928787270503171635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58856937147461770734328213 2758918928787270503171635)
              ·
                refine ⟨4138378393180905754757453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758918928787270503171635 4138378393180905754757453)
                ·
                  refine ⟨1551891897442839658034045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4138378393180905754757453 1551891897442839658034045)
                  ·
                    refine ⟨581959461541064871762767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551891897442839658034045 581959461541064871762767)
                    ·
                      rfl

theorem cell22_1700043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 3].length) (baseStart_1700043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700043 prefixEnd_1700043 := by exact prefixLift 1700043
  have htrace : WordTrace (prefixWord ++ tailWord_1700043) baseStart_1700043 baseEnd_1700043 := by
    simpa [prefixWord, tailWord_1700043, baseEnd_1700043] using wordTrace_append hprefix tailTrace_1700043
  have hstable : (prefixWord ++ tailWord_1700043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700043).length < 2 ^ (prefixWord ++ tailWord_1700043).sum := by decide
  have hdescent : baseEnd_1700043 < baseStart_1700043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700094 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1700094 : Nat := 118140960795 + 1700094 * 2 ^ 59
def prefixEnd_1700094 : Nat := 4983230072969 + 3 ^ 40 * 1700094 * 2
def baseEnd_1700094 : Nat := 581976919883317738737611

theorem tailTrace_1700094 : CollatzResearch.WordTrace tailWord_1700094 prefixEnd_1700094 581976919883317738737611 := by
  unfold tailWord_1700094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750940287857158223016417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41338348201904843856087557 7750940287857158223016417)
  ·
    refine ⟨5813205215892868667262313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7750940287857158223016417 5813205215892868667262313)
    ·
      refine ⟨4359903911919651500446735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5813205215892868667262313 4359903911919651500446735)
      ·
        refine ⟨6539855867879477250670103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359903911919651500446735 6539855867879477250670103)
        ·
          refine ⟨9809783801819215876005155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539855867879477250670103 9809783801819215876005155)
          ·
            refine ⟨14714675702728823814007733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9809783801819215876005155 14714675702728823814007733)
            ·
              refine ⟨1379500847130827232563225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14714675702728823814007733 1379500847130827232563225)
              ·
                refine ⟨1034625635348120424422419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379500847130827232563225 1034625635348120424422419)
                ·
                  refine ⟨1551938453022180636633629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034625635348120424422419 1551938453022180636633629)
                  ·
                    refine ⟨581976919883317738737611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1551938453022180636633629 581976919883317738737611)
                    ·
                      rfl

theorem cell22_1700094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1700094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700094 prefixEnd_1700094 := by exact prefixLift 1700094
  have htrace : WordTrace (prefixWord ++ tailWord_1700094) baseStart_1700094 baseEnd_1700094 := by
    simpa [prefixWord, tailWord_1700094, baseEnd_1700094] using wordTrace_append hprefix tailTrace_1700094
  have hstable : (prefixWord ++ tailWord_1700094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700094).length < 2 ^ (prefixWord ++ tailWord_1700094).sum := by decide
  have hdescent : baseEnd_1700094 < baseStart_1700094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700101 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1700101 : Nat := 118140960795 + 1700101 * 2 ^ 59
def prefixEnd_1700101 : Nat := 4983230072969 + 3 ^ 40 * 1700101 * 2
def baseEnd_1700101 : Nat := 193993105375457351270863

theorem tailTrace_1700101 : CollatzResearch.WordTrace tailWord_1700101 prefixEnd_1700101 193993105375457351270863 := by
  unfold tailWord_1700101
  simp only [CollatzResearch.WordTrace]
  refine ⟨62007777613831905979636157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41338518409221270653090771 62007777613831905979636157)
  ·
    refine ⟨23252916605186964742363559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62007777613831905979636157 23252916605186964742363559)
    ·
      refine ⟨34879374907780447113545339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23252916605186964742363559 34879374907780447113545339)
      ·
        refine ⟨52319062361670670670318009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34879374907780447113545339 52319062361670670670318009)
        ·
          refine ⟨39239296771253003002738507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52319062361670670670318009 39239296771253003002738507)
          ·
            refine ⟨58858945156879504504107761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39239296771253003002738507 58858945156879504504107761)
            ·
              refine ⟨44144208867659628378080821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58858945156879504504107761 44144208867659628378080821)
              ·
                refine ⟨4138519581343090160445077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44144208867659628378080821 4138519581343090160445077)
                ·
                  refine ⟨193993105375457351270863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4138519581343090160445077 193993105375457351270863)
                  ·
                    rfl

theorem cell22_1700101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1700101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700101 prefixEnd_1700101 := by exact prefixLift 1700101
  have htrace : WordTrace (prefixWord ++ tailWord_1700101) baseStart_1700101 baseEnd_1700101 := by
    simpa [prefixWord, tailWord_1700101, baseEnd_1700101] using wordTrace_append hprefix tailTrace_1700101
  have hstable : (prefixWord ++ tailWord_1700101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700101).length < 2 ^ (prefixWord ++ tailWord_1700101).sum := by decide
  have hdescent : baseEnd_1700101 < baseStart_1700101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700146 : List Nat := [3, 2, 1, 1, 15]
def baseStart_1700146 : Nat := 118140960795 + 1700146 * 2 ^ 59
def prefixEnd_1700146 : Nat := 4983230072969 + 3 ^ 40 * 1700146 * 2
def baseEnd_1700146 : Nat := 2395040002246942125257

theorem tailTrace_1700146 : CollatzResearch.WordTrace tailWord_1700146 prefixEnd_1700146 2395040002246942125257 := by
  unfold tailWord_1700146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15502354724667219666256073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41339612599112585776682861 15502354724667219666256073)
  ·
    refine ⟨11626766043500414749692055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15502354724667219666256073 11626766043500414749692055)
    ·
      refine ⟨17440149065250622124538083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626766043500414749692055 17440149065250622124538083)
      ·
        refine ⟨26160223597875933186807125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17440149065250622124538083 26160223597875933186807125)
        ·
          refine ⟨2395040002246942125257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 26160223597875933186807125 2395040002246942125257)
          ·
            rfl

theorem cell22_1700146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 15].length) (baseStart_1700146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700146 prefixEnd_1700146 := by exact prefixLift 1700146
  have htrace : WordTrace (prefixWord ++ tailWord_1700146) baseStart_1700146 baseEnd_1700146 := by
    simpa [prefixWord, tailWord_1700146, baseEnd_1700146] using wordTrace_append hprefix tailTrace_1700146
  have hstable : (prefixWord ++ tailWord_1700146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700146).length < 2 ^ (prefixWord ++ tailWord_1700146).sum := by decide
  have hdescent : baseEnd_1700146 < baseStart_1700146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700180 : List Nat := [2, 4, 1, 1, 2, 3, 3, 6]
def baseStart_1700180 : Nat := 118140960795 + 1700180 * 2 ^ 59
def prefixEnd_1700180 : Nat := 4983230072969 + 3 ^ 40 * 1700180 * 2
def baseEnd_1700180 : Nat := 64667373271204686787483

theorem tailTrace_1700180 : CollatzResearch.WordTrace tailWord_1700180 prefixEnd_1700180 64667373271204686787483 := by
  unfold tailWord_1700180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31005329490272851235880997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41340439320363801647841329 31005329490272851235880997)
  ·
    refine ⟨5813499279426159606727687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31005329490272851235880997 5813499279426159606727687)
    ·
      refine ⟨8720248919139239410091531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813499279426159606727687 8720248919139239410091531)
      ·
        refine ⟨13080373378708859115137297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720248919139239410091531 13080373378708859115137297)
        ·
          refine ⟨9810280034031644336352973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13080373378708859115137297 9810280034031644336352973)
          ·
            refine ⟨3678855012761866626132365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9810280034031644336352973 3678855012761866626132365)
            ·
              refine ⟨1379570629785699984799637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3678855012761866626132365 1379570629785699984799637)
              ·
                refine ⟨64667373271204686787483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1379570629785699984799637 64667373271204686787483)
                ·
                  rfl

theorem cell22_1700180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_1700180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700180 prefixEnd_1700180 := by exact prefixLift 1700180
  have htrace : WordTrace (prefixWord ++ tailWord_1700180) baseStart_1700180 baseEnd_1700180 := by
    simpa [prefixWord, tailWord_1700180, baseEnd_1700180] using wordTrace_append hprefix tailTrace_1700180
  have hstable : (prefixWord ++ tailWord_1700180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700180).length < 2 ^ (prefixWord ++ tailWord_1700180).sum := by decide
  have hdescent : baseEnd_1700180 < baseStart_1700180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700208 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_1700208 : Nat := 118140960795 + 1700208 * 2 ^ 59
def prefixEnd_1700208 : Nat := 4983230072969 + 3 ^ 40 * 1700208 * 2
def baseEnd_1700208 : Nat := 194005314804353147129087

theorem tailTrace_1700208 : CollatzResearch.WordTrace tailWord_1700208 prefixEnd_1700208 194005314804353147129087 := by
  unfold tailWord_1700208
  simp only [CollatzResearch.WordTrace]
  refine ⟨31005840112222131626890639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41341120149629508835854185 31005840112222131626890639)
  ·
    refine ⟨46508760168333197440335959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31005840112222131626890639 46508760168333197440335959)
    ·
      refine ⟨69763140252499796160503939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46508760168333197440335959 69763140252499796160503939)
      ·
        refine ⟨104644710378749694240755909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69763140252499796160503939 104644710378749694240755909)
        ·
          refine ⟨19620883196015567670141733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104644710378749694240755909 19620883196015567670141733)
          ·
            refine ⟨3678915599252918938151575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19620883196015567670141733 3678915599252918938151575)
            ·
              refine ⟨5518373398879378407227363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678915599252918938151575 5518373398879378407227363)
              ·
                refine ⟨8277560098319067610841045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518373398879378407227363 8277560098319067610841045)
                ·
                  refine ⟨194005314804353147129087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8277560098319067610841045 194005314804353147129087)
                  ·
                    rfl

theorem cell22_1700208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_1700208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700208 prefixEnd_1700208 := by exact prefixLift 1700208
  have htrace : WordTrace (prefixWord ++ tailWord_1700208) baseStart_1700208 baseEnd_1700208 := by
    simpa [prefixWord, tailWord_1700208, baseEnd_1700208] using wordTrace_append hprefix tailTrace_1700208
  have hstable : (prefixWord ++ tailWord_1700208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700208).length < 2 ^ (prefixWord ++ tailWord_1700208).sum := by decide
  have hdescent : baseEnd_1700208 < baseStart_1700208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700255 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 1, 4]
def baseStart_1700255 : Nat := 118140960795 + 1700255 * 2 ^ 59
def prefixEnd_1700255 : Nat := 4983230072969 + 3 ^ 40 * 1700255 * 2
def baseEnd_1700255 : Nat := 582032033473566985462117

theorem tailTrace_1700255 : CollatzResearch.WordTrace tailWord_1700255 prefixEnd_1700255 582032033473566985462117 := by
  unfold tailWord_1700255
  simp only [CollatzResearch.WordTrace]
  refine ⟨62013394455273990280742219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41342262970182660187161479 62013394455273990280742219)
  ·
    refine ⟨93020091682910985421113329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62013394455273990280742219 93020091682910985421113329)
    ·
      refine ⟨69765068762183239065834997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93020091682910985421113329 69765068762183239065834997)
      ·
        refine ⟨6540475196454678662422031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69765068762183239065834997 6540475196454678662422031)
        ·
          refine ⟨9810712794682017993633047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540475196454678662422031 9810712794682017993633047)
          ·
            refine ⟨14716069192023026990449571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810712794682017993633047 14716069192023026990449571)
            ·
              refine ⟨22074103788034540485674357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716069192023026990449571 22074103788034540485674357)
              ·
                refine ⟨2069447230128238170531971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22074103788034540485674357 2069447230128238170531971)
                ·
                  refine ⟨3104170845192357255797957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069447230128238170531971 3104170845192357255797957)
                  ·
                    refine ⟨582032033473566985462117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104170845192357255797957 582032033473566985462117)
                    ·
                      rfl

theorem cell22_1700255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_1700255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700255 prefixEnd_1700255 := by exact prefixLift 1700255
  have htrace : WordTrace (prefixWord ++ tailWord_1700255) baseStart_1700255 baseEnd_1700255 := by
    simpa [prefixWord, tailWord_1700255, baseEnd_1700255] using wordTrace_append hprefix tailTrace_1700255
  have hstable : (prefixWord ++ tailWord_1700255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700255).length < 2 ^ (prefixWord ++ tailWord_1700255).sum := by decide
  have hdescent : baseEnd_1700255 < baseStart_1700255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700298 : List Nat := [3, 1, 2, 1, 2, 2, 1, 10]
def baseStart_1700298 : Nat := 118140960795 + 1700298 * 2 ^ 59
def prefixEnd_1700298 : Nat := 4983230072969 + 3 ^ 40 * 1700298 * 2
def baseEnd_1700298 : Nat := 64671861472481022959665

theorem tailTrace_1700298 : CollatzResearch.WordTrace tailWord_1700298 prefixEnd_1700298 64671861472481022959665 := by
  unfold tailWord_1700298
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503740698529552156139387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41343308529412139083038365 15503740698529552156139387)
  ·
    refine ⟨23255611047794328234209081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503740698529552156139387 23255611047794328234209081)
    ·
      refine ⟨17441708285845746175656811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23255611047794328234209081 17441708285845746175656811)
      ·
        refine ⟨26162562428768619263485217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441708285845746175656811 26162562428768619263485217)
        ·
          refine ⟨19621921821576464447613913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26162562428768619263485217 19621921821576464447613913)
          ·
            refine ⟨14716441366182348335710435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19621921821576464447613913 14716441366182348335710435)
            ·
              refine ⟨22074662049273522503565653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14716441366182348335710435 22074662049273522503565653)
              ·
                refine ⟨64671861472481022959665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22074662049273522503565653 64671861472481022959665)
                ·
                  rfl

theorem cell22_1700298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_1700298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700298 prefixEnd_1700298 := by exact prefixLift 1700298
  have htrace : WordTrace (prefixWord ++ tailWord_1700298) baseStart_1700298 baseEnd_1700298 := by
    simpa [prefixWord, tailWord_1700298, baseEnd_1700298] using wordTrace_append hprefix tailTrace_1700298
  have hstable : (prefixWord ++ tailWord_1700298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700298).length < 2 ^ (prefixWord ++ tailWord_1700298).sum := by decide
  have hdescent : baseEnd_1700298 < baseStart_1700298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700306 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1700306 : Nat := 118140960795 + 1700306 * 2 ^ 59
def prefixEnd_1700306 : Nat := 4983230072969 + 3 ^ 40 * 1700306 * 2
def baseEnd_1700306 : Nat := 582049491815819852436961

theorem tailTrace_1700306 : CollatzResearch.WordTrace tailWord_1700306 prefixEnd_1700306 582049491815819852436961 := by
  unfold tailWord_1700306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503813644522306497712193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41343503052059483993899181 15503813644522306497712193)
  ·
    refine ⟨11627860233391729873284145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15503813644522306497712193 11627860233391729873284145)
    ·
      refine ⟨8720895175043797404963109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11627860233391729873284145 8720895175043797404963109)
      ·
        refine ⟨1635167845320712013430583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8720895175043797404963109 1635167845320712013430583)
        ·
          refine ⟨2452751767981068020145875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635167845320712013430583 2452751767981068020145875)
          ·
            refine ⟨3679127651971602030218813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452751767981068020145875 3679127651971602030218813)
            ·
              refine ⟨1379672869489350761332055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3679127651971602030218813 1379672869489350761332055)
              ·
                refine ⟨2069509304234026141998083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379672869489350761332055 2069509304234026141998083)
                ·
                  refine ⟨3104263956351039212997125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069509304234026141998083 3104263956351039212997125)
                  ·
                    refine ⟨582049491815819852436961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104263956351039212997125 582049491815819852436961)
                    ·
                      rfl

theorem cell22_1700306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1700306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700306 prefixEnd_1700306 := by exact prefixLift 1700306
  have htrace : WordTrace (prefixWord ++ tailWord_1700306) baseStart_1700306 baseEnd_1700306 := by
    simpa [prefixWord, tailWord_1700306, baseEnd_1700306] using wordTrace_append hprefix tailTrace_1700306
  have hstable : (prefixWord ++ tailWord_1700306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700306).length < 2 ^ (prefixWord ++ tailWord_1700306).sum := by decide
  have hdescent : baseEnd_1700306 < baseStart_1700306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700364 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_1700364 : Nat := 118140960795 + 1700364 * 2 ^ 59
def prefixEnd_1700364 : Nat := 4983230072969 + 3 ^ 40 * 1700364 * 2
def baseEnd_1700364 : Nat := 582069346401127034486783

theorem tailTrace_1700364 : CollatzResearch.WordTrace tailWord_1700364 prefixEnd_1700364 582069346401127034486783 := by
  unfold tailWord_1700364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31008685005939550948230073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41344913341252734597640097 31008685005939550948230073)
  ·
    refine ⟨23256513754454663211172555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31008685005939550948230073 23256513754454663211172555)
    ·
      refine ⟨34884770631681994816758833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23256513754454663211172555 34884770631681994816758833)
      ·
        refine ⟨26163577973761496112569125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34884770631681994816758833 26163577973761496112569125)
        ·
          refine ⟨4905670870080280521106711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26163577973761496112569125 4905670870080280521106711)
          ·
            refine ⟨7358506305120420781660067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905670870080280521106711 7358506305120420781660067)
            ·
              refine ⟨11037759457680631172490101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358506305120420781660067 11037759457680631172490101)
              ·
                refine ⟨1034789949157559172420947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11037759457680631172490101 1034789949157559172420947)
                ·
                  refine ⟨1552184923736338758631421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034789949157559172420947 1552184923736338758631421)
                  ·
                    refine ⟨582069346401127034486783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552184923736338758631421 582069346401127034486783)
                    ·
                      rfl

theorem cell22_1700364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_1700364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700364 prefixEnd_1700364 := by exact prefixLift 1700364
  have htrace : WordTrace (prefixWord ++ tailWord_1700364) baseStart_1700364 baseEnd_1700364 := by
    simpa [prefixWord, tailWord_1700364, baseEnd_1700364] using wordTrace_append hprefix tailTrace_1700364
  have hstable : (prefixWord ++ tailWord_1700364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700364).length < 2 ^ (prefixWord ++ tailWord_1700364).sum := by decide
  have hdescent : baseEnd_1700364 < baseStart_1700364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700392 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1700392 : Nat := 118140960795 + 1700392 * 2 ^ 59
def prefixEnd_1700392 : Nat := 4983230072969 + 3 ^ 40 * 1700392 * 2
def baseEnd_1700392 : Nat := 582078931373344294786697

theorem tailTrace_1700392 : CollatzResearch.WordTrace tailWord_1700392 prefixEnd_1700392 582078931373344294786697 := by
  unfold tailWord_1700392
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009195627888831339239715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41345594170518441785652953 31009195627888831339239715)
  ·
    refine ⟨46513793441833247008859573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31009195627888831339239715 46513793441833247008859573)
    ·
      refine ⟨4360668135171866907080585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46513793441833247008859573 4360668135171866907080585)
      ·
        refine ⟨3270501101378900180310439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4360668135171866907080585 3270501101378900180310439)
        ·
          refine ⟨4905751652068350270465659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270501101378900180310439 4905751652068350270465659)
          ·
            refine ⟨7358627478102525405698489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905751652068350270465659 7358627478102525405698489)
            ·
              refine ⟨5518970608576894054273867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7358627478102525405698489 5518970608576894054273867)
              ·
                refine ⟨8278455912865341081410801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518970608576894054273867 8278455912865341081410801)
                ·
                  refine ⟨6208841934649005811058101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8278455912865341081410801 6208841934649005811058101)
                  ·
                    refine ⟨582078931373344294786697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6208841934649005811058101 582078931373344294786697)
                    ·
                      rfl

theorem cell22_1700392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1700392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700392 prefixEnd_1700392 := by exact prefixLift 1700392
  have htrace : WordTrace (prefixWord ++ tailWord_1700392) baseStart_1700392 baseEnd_1700392 := by
    simpa [prefixWord, tailWord_1700392, baseEnd_1700392] using wordTrace_append hprefix tailTrace_1700392
  have hstable : (prefixWord ++ tailWord_1700392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700392).length < 2 ^ (prefixWord ++ tailWord_1700392).sum := by decide
  have hdescent : baseEnd_1700392 < baseStart_1700392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700394 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_1700394 : Nat := 118140960795 + 1700394 * 2 ^ 59
def prefixEnd_1700394 : Nat := 4983230072969 + 3 ^ 40 * 1700394 * 2
def baseEnd_1700394 : Nat := 194026538671405652078897

theorem tailTrace_1700394 : CollatzResearch.WordTrace tailWord_1700394 prefixEnd_1700394 194026538671405652078897 := by
  unfold tailWord_1700394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15504616050442604255013059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41345642801180278013368157 15504616050442604255013059)
  ·
    refine ⟨23256924075663906382519589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15504616050442604255013059 23256924075663906382519589)
    ·
      refine ⟨4360673264186982446722423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23256924075663906382519589 4360673264186982446722423)
      ·
        refine ⟨6541009896280473670083635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360673264186982446722423 6541009896280473670083635)
        ·
          refine ⟨9811514844420710505125453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541009896280473670083635 9811514844420710505125453)
          ·
            refine ⟨3679318066657766439422045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9811514844420710505125453 3679318066657766439422045)
            ·
              refine ⟨1379744274996662414783267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3679318066657766439422045 1379744274996662414783267)
              ·
                refine ⟨2069616412494993622174901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379744274996662414783267 2069616412494993622174901)
                ·
                  refine ⟨194026538671405652078897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2069616412494993622174901 194026538671405652078897)
                  ·
                    rfl

theorem cell22_1700394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_1700394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700394 prefixEnd_1700394 := by exact prefixLift 1700394
  have htrace : WordTrace (prefixWord ++ tailWord_1700394) baseStart_1700394 baseEnd_1700394 := by
    simpa [prefixWord, tailWord_1700394, baseEnd_1700394] using wordTrace_append hprefix tailTrace_1700394
  have hstable : (prefixWord ++ tailWord_1700394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700394).length < 2 ^ (prefixWord ++ tailWord_1700394).sum := by decide
  have hdescent : baseEnd_1700394 < baseStart_1700394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700405 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 6]
def baseStart_1700405 : Nat := 118140960795 + 1700405 * 2 ^ 59
def prefixEnd_1700405 : Nat := 4983230072969 + 3 ^ 40 * 1700405 * 2
def baseEnd_1700405 : Nat := 194027793846338864737219

theorem tailTrace_1700405 : CollatzResearch.WordTrace tailWord_1700405 prefixEnd_1700405 194027793846338864737219 := by
  unfold tailWord_1700405
  simp only [CollatzResearch.WordTrace]
  refine ⟨62018865404730565898702669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41345910269820377265801779 62018865404730565898702669)
  ·
    refine ⟨23257074526773962212013501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62018865404730565898702669 23257074526773962212013501)
    ·
      refine ⟨8721402947540235829505063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23257074526773962212013501 8721402947540235829505063)
      ·
        refine ⟨13082104421310353744257595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721402947540235829505063 13082104421310353744257595)
        ·
          refine ⟨19623156631965530616386393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082104421310353744257595 19623156631965530616386393)
          ·
            refine ⟨14717367473974147962289795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19623156631965530616386393 14717367473974147962289795)
            ·
              refine ⟨22076051210961221943434693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14717367473974147962289795 22076051210961221943434693)
              ·
                refine ⟨4139259602055229114394005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22076051210961221943434693 4139259602055229114394005)
                ·
                  refine ⟨194027793846338864737219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4139259602055229114394005 194027793846338864737219)
                  ·
                    rfl

theorem cell22_1700405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_1700405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700405 prefixEnd_1700405 := by exact prefixLift 1700405
  have htrace : WordTrace (prefixWord ++ tailWord_1700405) baseStart_1700405 baseEnd_1700405 := by
    simpa [prefixWord, tailWord_1700405, baseEnd_1700405] using wordTrace_append hprefix tailTrace_1700405
  have hstable : (prefixWord ++ tailWord_1700405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700405).length < 2 ^ (prefixWord ++ tailWord_1700405).sum := by decide
  have hdescent : baseEnd_1700405 < baseStart_1700405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700407 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1700407 : Nat := 118140960795 + 1700407 * 2 ^ 59
def prefixEnd_1700407 : Nat := 4983230072969 + 3 ^ 40 * 1700407 * 2
def baseEnd_1700407 : Nat := 582084066179889255661651

theorem tailTrace_1700407 : CollatzResearch.WordTrace tailWord_1700407 prefixEnd_1700407 582084066179889255661651 := by
  unfold tailWord_1700407
  simp only [CollatzResearch.WordTrace]
  refine ⟨62018938350723320240275475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41345958900482213493516983 62018938350723320240275475)
  ·
    refine ⟨93028407526084980360413213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62018938350723320240275475 93028407526084980360413213)
    ·
      refine ⟨34885652822281867635154955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93028407526084980360413213 34885652822281867635154955)
      ·
        refine ⟨52328479233422801452732433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34885652822281867635154955 52328479233422801452732433)
        ·
          refine ⟨39246359425067101089549325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52328479233422801452732433 39246359425067101089549325)
          ·
            refine ⟨14717384784400162908580997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39246359425067101089549325 14717384784400162908580997)
            ·
              refine ⟨2759509647075030545358937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14717384784400162908580997 2759509647075030545358937)
              ·
                refine ⟨2069632235306272909019203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759509647075030545358937 2069632235306272909019203)
                ·
                  refine ⟨3104448352959409363528805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069632235306272909019203 3104448352959409363528805)
                  ·
                    refine ⟨582084066179889255661651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104448352959409363528805 582084066179889255661651)
                    ·
                      rfl

theorem cell22_1700407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1700407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700407 prefixEnd_1700407 := by exact prefixLift 1700407
  have htrace : WordTrace (prefixWord ++ tailWord_1700407) baseStart_1700407 baseEnd_1700407 := by
    simpa [prefixWord, tailWord_1700407, baseEnd_1700407] using wordTrace_append hprefix tailTrace_1700407
  have hstable : (prefixWord ++ tailWord_1700407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700407).length < 2 ^ (prefixWord ++ tailWord_1700407).sum := by decide
  have hdescent : baseEnd_1700407 < baseStart_1700407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700437 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1700437 : Nat := 118140960795 + 1700437 * 2 ^ 59
def prefixEnd_1700437 : Nat := 4983230072969 + 3 ^ 40 * 1700437 * 2
def baseEnd_1700437 : Nat := 582094335792979177411559

theorem tailTrace_1700437 : CollatzResearch.WordTrace tailWord_1700437 prefixEnd_1700437 582094335792979177411559 := by
  unfold tailWord_1700437
  simp only [CollatzResearch.WordTrace]
  refine ⟨62020032540614635363867565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41346688360409756909245043 62020032540614635363867565)
  ·
    refine ⟨23257512202730488261450337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62020032540614635363867565 23257512202730488261450337)
    ·
      refine ⟨17443134152047866196087753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23257512202730488261450337 17443134152047866196087753)
      ·
        refine ⟨13082350614035899647065815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17443134152047866196087753 13082350614035899647065815)
        ·
          refine ⟨19623525921053849470598723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082350614035899647065815 19623525921053849470598723)
          ·
            refine ⟨29435288881580774205898085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19623525921053849470598723 29435288881580774205898085)
            ·
              refine ⟨5519116665296395163605891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29435288881580774205898085 5519116665296395163605891)
              ·
                refine ⟨8278674997944592745408837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519116665296395163605891 8278674997944592745408837)
                ·
                  refine ⟨1552251562114611139764157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8278674997944592745408837 1552251562114611139764157)
                  ·
                    refine ⟨582094335792979177411559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552251562114611139764157 582094335792979177411559)
                    ·
                      rfl

theorem cell22_1700437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1700437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700437 prefixEnd_1700437 := by exact prefixLift 1700437
  have htrace : WordTrace (prefixWord ++ tailWord_1700437) baseStart_1700437 baseEnd_1700437 := by
    simpa [prefixWord, tailWord_1700437, baseEnd_1700437] using wordTrace_append hprefix tailTrace_1700437
  have hstable : (prefixWord ++ tailWord_1700437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700437).length < 2 ^ (prefixWord ++ tailWord_1700437).sum := by decide
  have hdescent : baseEnd_1700437 < baseStart_1700437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700439 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 4]
def baseStart_1700439 : Nat := 118140960795 + 1700439 * 2 ^ 59
def prefixEnd_1700439 : Nat := 4983230072969 + 3 ^ 40 * 1700439 * 2
def baseEnd_1700439 : Nat := 194031673477950612953851

theorem tailTrace_1700439 : CollatzResearch.WordTrace tailWord_1700439 prefixEnd_1700439 194031673477950612953851 := by
  unfold tailWord_1700439
  simp only [CollatzResearch.WordTrace]
  refine ⟨62020105486607389705440371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41346736991071593136960247 62020105486607389705440371)
  ·
    refine ⟨93030158229911084558160557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62020105486607389705440371 93030158229911084558160557)
    ·
      refine ⟨34886309336216656709310209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93030158229911084558160557 34886309336216656709310209)
      ·
        refine ⟨26164732002162492531982657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34886309336216656709310209 26164732002162492531982657)
        ·
          refine ⟨19623549001621869398986993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26164732002162492531982657 19623549001621869398986993)
          ·
            refine ⟨14717661751216402049240245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19623549001621869398986993 14717661751216402049240245)
            ·
              refine ⟨1379780789176537692116273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14717661751216402049240245 1379780789176537692116273)
              ·
                refine ⟨1034835591882403269087205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379780789176537692116273 1034835591882403269087205)
                ·
                  refine ⟨194031673477950612953851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034835591882403269087205 194031673477950612953851)
                  ·
                    rfl

theorem cell22_1700439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 4].length) (baseStart_1700439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700439 prefixEnd_1700439 := by exact prefixLift 1700439
  have htrace : WordTrace (prefixWord ++ tailWord_1700439) baseStart_1700439 baseEnd_1700439 := by
    simpa [prefixWord, tailWord_1700439, baseEnd_1700439] using wordTrace_append hprefix tailTrace_1700439
  have hstable : (prefixWord ++ tailWord_1700439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700439).length < 2 ^ (prefixWord ++ tailWord_1700439).sum := by decide
  have hdescent : baseEnd_1700439 < baseStart_1700439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700499 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 1, 3]
def baseStart_1700499 : Nat := 118140960795 + 1700499 * 2 ^ 59
def prefixEnd_1700499 : Nat := 4983230072969 + 3 ^ 40 * 1700499 * 2
def baseEnd_1700499 : Nat := 582115559660031682361369

theorem tailTrace_1700499 : CollatzResearch.WordTrace tailWord_1700499 prefixEnd_1700499 582115559660031682361369 := by
  unfold tailWord_1700499
  simp only [CollatzResearch.WordTrace]
  refine ⟨62022293866390019952624551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41348195910926679968416367 62022293866390019952624551)
  ·
    refine ⟨93033440799585029928936827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62022293866390019952624551 93033440799585029928936827)
    ·
      refine ⟨139550161199377544893405241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93033440799585029928936827 139550161199377544893405241)
      ·
        refine ⟨104662620899533158670053931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139550161199377544893405241 104662620899533158670053931)
        ·
          refine ⟨156993931349299738005080897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104662620899533158670053931 156993931349299738005080897)
          ·
            refine ⟨117745448511974803503810673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156993931349299738005080897 117745448511974803503810673)
            ·
              refine ⟨88309086383981102627858005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117745448511974803503810673 88309086383981102627858005)
              ·
                refine ⟨1034872106062278546420211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 88309086383981102627858005 1034872106062278546420211)
                ·
                  refine ⟨1552308159093417819630317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034872106062278546420211 1552308159093417819630317)
                  ·
                    refine ⟨582115559660031682361369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552308159093417819630317 582115559660031682361369)
                    ·
                      rfl

theorem cell22_1700499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 1, 3].length) (baseStart_1700499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700499 prefixEnd_1700499 := by exact prefixLift 1700499
  have htrace : WordTrace (prefixWord ++ tailWord_1700499) baseStart_1700499 baseEnd_1700499 := by
    simpa [prefixWord, tailWord_1700499, baseEnd_1700499] using wordTrace_append hprefix tailTrace_1700499
  have hstable : (prefixWord ++ tailWord_1700499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700499).length < 2 ^ (prefixWord ++ tailWord_1700499).sum := by decide
  have hdescent : baseEnd_1700499 < baseStart_1700499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700533 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1700533 : Nat := 118140960795 + 1700533 * 2 ^ 59
def prefixEnd_1700533 : Nat := 4983230072969 + 3 ^ 40 * 1700533 * 2
def baseEnd_1700533 : Nat := 582127198554866927011265

theorem tailTrace_1700533 : CollatzResearch.WordTrace tailWord_1700533 prefixEnd_1700533 582127198554866927011265 := by
  unfold tailWord_1700533
  simp only [CollatzResearch.WordTrace]
  refine ⟨62023533948266843759362253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41349022632177895839574835 62023533948266843759362253)
  ·
    refine ⟨23258825230600066409760845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62023533948266843759362253 23258825230600066409760845)
    ·
      refine ⟨8722059461475024903660317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23258825230600066409760845 8722059461475024903660317)
      ·
        refine ⟨3270772298053134338872619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8722059461475024903660317 3270772298053134338872619)
        ·
          refine ⟨4906158447079701508308929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270772298053134338872619 4906158447079701508308929)
          ·
            refine ⟨3679618835309776131231697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906158447079701508308929 3679618835309776131231697)
            ·
              refine ⟨2759714126482332098423773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3679618835309776131231697 2759714126482332098423773)
              ·
                refine ⟨1034892797430874536908915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759714126482332098423773 1034892797430874536908915)
                ·
                  refine ⟨1552339196146311805363373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1034892797430874536908915 1552339196146311805363373)
                  ·
                    refine ⟨582127198554866927011265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552339196146311805363373 582127198554866927011265)
                    ·
                      rfl

theorem cell22_1700533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1700533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700533 prefixEnd_1700533 := by exact prefixLift 1700533
  have htrace : WordTrace (prefixWord ++ tailWord_1700533) baseStart_1700533 baseEnd_1700533 := by
    simpa [prefixWord, tailWord_1700533, baseEnd_1700533] using wordTrace_append hprefix tailTrace_1700533
  have hstable : (prefixWord ++ tailWord_1700533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700533).length < 2 ^ (prefixWord ++ tailWord_1700533).sum := by decide
  have hdescent : baseEnd_1700533 < baseStart_1700533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700550 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1700550 : Nat := 118140960795 + 1700550 * 2 ^ 59
def prefixEnd_1700550 : Nat := 4983230072969 + 3 ^ 40 * 1700550 * 2
def baseEnd_1700550 : Nat := 582133018002284549336213

theorem tailTrace_1700550 : CollatzResearch.WordTrace tailWord_1700550 prefixEnd_1700550 582133018002284549336213 := by
  unfold tailWord_1700550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938254812162664239460347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41349435992803503775154069 1938254812162664239460347)
  ·
    refine ⟨2907382218243996359190521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938254812162664239460347 2907382218243996359190521)
    ·
      refine ⟨2180536663682997269392891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2907382218243996359190521 2180536663682997269392891)
      ·
        refine ⟨3270804995524495904089337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180536663682997269392891 3270804995524495904089337)
        ·
          refine ⟨2453103746643371928067003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270804995524495904089337 2453103746643371928067003)
          ·
            refine ⟨3679655619965057892100505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453103746643371928067003 3679655619965057892100505)
            ·
              refine ⟨2759741714973793419075379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3679655619965057892100505 2759741714973793419075379)
              ·
                refine ⟨4139612572460690128613069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759741714973793419075379 4139612572460690128613069)
                ·
                  refine ⟨1552354714672758798229901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4139612572460690128613069 1552354714672758798229901)
                  ·
                    refine ⟨582133018002284549336213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552354714672758798229901 582133018002284549336213)
                    ·
                      rfl

theorem cell22_1700550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1700550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700550 prefixEnd_1700550 := by exact prefixLift 1700550
  have htrace : WordTrace (prefixWord ++ tailWord_1700550) baseStart_1700550 baseEnd_1700550 := by
    simpa [prefixWord, tailWord_1700550, baseEnd_1700550] using wordTrace_append hprefix tailTrace_1700550
  have hstable : (prefixWord ++ tailWord_1700550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700550).length < 2 ^ (prefixWord ++ tailWord_1700550).sum := by decide
  have hdescent : baseEnd_1700550 < baseStart_1700550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700555 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_1700555 : Nat := 118140960795 + 1700555 * 2 ^ 59
def prefixEnd_1700555 : Nat := 4983230072969 + 3 ^ 40 * 1700555 * 2
def baseEnd_1700555 : Nat := 582134729604466202961197

theorem tailTrace_1700555 : CollatzResearch.WordTrace tailWord_1700555 prefixEnd_1700555 582134729604466202961197 := by
  unfold tailWord_1700555
  simp only [CollatzResearch.WordTrace]
  refine ⟨62024336354187141516663119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41349557569458094344442079 62024336354187141516663119)
  ·
    refine ⟨93036504531280712274994679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62024336354187141516663119 93036504531280712274994679)
    ·
      refine ⟨139554756796921068412492019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93036504531280712274994679 139554756796921068412492019)
      ·
        refine ⟨209332135195381602618738029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139554756796921068412492019 209332135195381602618738029)
        ·
          refine ⟨78499550698268100982026761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209332135195381602618738029 78499550698268100982026761)
          ·
            refine ⟨58874663023701075736520071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78499550698268100982026761 58874663023701075736520071)
            ·
              refine ⟨88311994535551613604780107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58874663023701075736520071 88311994535551613604780107)
              ·
                refine ⟨132467991803327420407170161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88311994535551613604780107 132467991803327420407170161)
                ·
                  refine ⟨99350993852495565305377621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132467991803327420407170161 99350993852495565305377621)
                  ·
                    refine ⟨582134729604466202961197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99350993852495565305377621 582134729604466202961197)
                    ·
                      rfl

theorem cell22_1700555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_1700555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700555 prefixEnd_1700555 := by exact prefixLift 1700555
  have htrace : WordTrace (prefixWord ++ tailWord_1700555) baseStart_1700555 baseEnd_1700555 := by
    simpa [prefixWord, tailWord_1700555, baseEnd_1700555] using wordTrace_append hprefix tailTrace_1700555
  have hstable : (prefixWord ++ tailWord_1700555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700555).length < 2 ^ (prefixWord ++ tailWord_1700555).sum := by decide
  have hdescent : baseEnd_1700555 < baseStart_1700555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700587 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_1700587 : Nat := 118140960795 + 1700587 * 2 ^ 59
def prefixEnd_1700587 : Nat := 4983230072969 + 3 ^ 40 * 1700587 * 2
def baseEnd_1700587 : Nat := 582145683858428786161099

theorem tailTrace_1700587 : CollatzResearch.WordTrace tailWord_1700587 prefixEnd_1700587 582145683858428786161099 := by
  unfold tailWord_1700587
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025503490071210981828015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41350335660047473987885343 62025503490071210981828015)
  ·
    refine ⟨93038255235106816472742023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62025503490071210981828015 93038255235106816472742023)
    ·
      refine ⟨139557382852660224709113035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93038255235106816472742023 139557382852660224709113035)
      ·
        refine ⟨209336074278990337063669553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139557382852660224709113035 209336074278990337063669553)
        ·
          refine ⟨157002055709242752797752165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209336074278990337063669553 157002055709242752797752165)
          ·
            refine ⟨29437885445483016149578531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157002055709242752797752165 29437885445483016149578531)
            ·
              refine ⟨44156828168224524224367797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29437885445483016149578531 44156828168224524224367797)
              ·
                refine ⟨4139702640771049146034481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44156828168224524224367797 4139702640771049146034481)
                ·
                  refine ⟨3104776980578286859525861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139702640771049146034481 3104776980578286859525861)
                  ·
                    refine ⟨582145683858428786161099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104776980578286859525861 582145683858428786161099)
                    ·
                      rfl

theorem cell22_1700587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_1700587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700587 prefixEnd_1700587 := by exact prefixLift 1700587
  have htrace : WordTrace (prefixWord ++ tailWord_1700587) baseStart_1700587 baseEnd_1700587 := by
    simpa [prefixWord, tailWord_1700587, baseEnd_1700587] using wordTrace_append hprefix tailTrace_1700587
  have hstable : (prefixWord ++ tailWord_1700587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700587).length < 2 ^ (prefixWord ++ tailWord_1700587).sum := by decide
  have hdescent : baseEnd_1700587 < baseStart_1700587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700589 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1700589 : Nat := 118140960795 + 1700589 * 2 ^ 59
def prefixEnd_1700589 : Nat := 4983230072969 + 3 ^ 40 * 1700589 * 2
def baseEnd_1700589 : Nat := 582146368499301447611093

theorem tailTrace_1700589 : CollatzResearch.WordTrace tailWord_1700589 prefixEnd_1700589 582146368499301447611093 := by
  unfold tailWord_1700589
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025576436063965323400821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41350384290709310215600547 62025576436063965323400821)
  ·
    refine ⟨5814897790880996749068827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62025576436063965323400821 5814897790880996749068827)
    ·
      refine ⟨8722346686321495123603241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814897790880996749068827 8722346686321495123603241)
      ·
        refine ⟨6541760014741121342702431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8722346686321495123603241 6541760014741121342702431)
        ·
          refine ⟨9812640022111682014053647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541760014741121342702431 9812640022111682014053647)
          ·
            refine ⟨14718960033167523021080471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812640022111682014053647 14718960033167523021080471)
            ·
              refine ⟨22078440049751284531620707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718960033167523021080471 22078440049751284531620707)
              ·
                refine ⟨33117660074626926797431061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22078440049751284531620707 33117660074626926797431061)
                ·
                  refine ⟨1552390315998137193629581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33117660074626926797431061 1552390315998137193629581)
                  ·
                    refine ⟨582146368499301447611093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552390315998137193629581 582146368499301447611093)
                    ·
                      rfl

theorem cell22_1700589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1700589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700589 prefixEnd_1700589 := by exact prefixLift 1700589
  have htrace : WordTrace (prefixWord ++ tailWord_1700589) baseStart_1700589 baseEnd_1700589 := by
    simpa [prefixWord, tailWord_1700589, baseEnd_1700589] using wordTrace_append hprefix tailTrace_1700589
  have hstable : (prefixWord ++ tailWord_1700589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700589).length < 2 ^ (prefixWord ++ tailWord_1700589).sum := by decide
  have hdescent : baseEnd_1700589 < baseStart_1700589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700591 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 4]
def baseStart_1700591 : Nat := 118140960795 + 1700591 * 2 ^ 59
def prefixEnd_1700591 : Nat := 4983230072969 + 3 ^ 40 * 1700591 * 2
def baseEnd_1700591 : Nat := 194049017713391369687029

theorem tailTrace_1700591 : CollatzResearch.WordTrace tailWord_1700591 prefixEnd_1700591 194049017713391369687029 := by
  unfold tailWord_1700591
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025649382056719664973627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41350432921371146443315751 62025649382056719664973627)
  ·
    refine ⟨93038474073085079497460441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62025649382056719664973627 93038474073085079497460441)
    ·
      refine ⟨69778855554813809623095331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93038474073085079497460441 69778855554813809623095331)
      ·
        refine ⟨104668283332220714434642997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69778855554813809623095331 104668283332220714434642997)
        ·
          refine ⟨9812651562395691978247781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104668283332220714434642997 9812651562395691978247781)
          ·
            refine ⟨1839872167949192245921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9812651562395691978247781 1839872167949192245921459)
            ·
              refine ⟨2759808251923788368882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839872167949192245921459 2759808251923788368882189)
              ·
                refine ⟨1034928094471420638330821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759808251923788368882189 1034928094471420638330821)
                ·
                  refine ⟨194049017713391369687029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1034928094471420638330821 194049017713391369687029)
                  ·
                    rfl

theorem cell22_1700591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 4].length) (baseStart_1700591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700591 prefixEnd_1700591 := by exact prefixLift 1700591
  have htrace : WordTrace (prefixWord ++ tailWord_1700591) baseStart_1700591 baseEnd_1700591 := by
    simpa [prefixWord, tailWord_1700591, baseEnd_1700591] using wordTrace_append hprefix tailTrace_1700591
  have hstable : (prefixWord ++ tailWord_1700591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700591).length < 2 ^ (prefixWord ++ tailWord_1700591).sum := by decide
  have hdescent : baseEnd_1700591 < baseStart_1700591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700604 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1700604 : Nat := 118140960795 + 1700604 * 2 ^ 59
def prefixEnd_1700604 : Nat := 4983230072969 + 3 ^ 40 * 1700604 * 2
def baseEnd_1700604 : Nat := 582151503305846408486047

theorem tailTrace_1700604 : CollatzResearch.WordTrace tailWord_1700604 prefixEnd_1700604 582151503305846408486047 := by
  unfold tailWord_1700604
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013061765504811442598433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41350749020673081923464577 31013061765504811442598433)
  ·
    refine ⟨23259796324128608581948825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31013061765504811442598433 23259796324128608581948825)
    ·
      refine ⟨17444847243096456436461619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23259796324128608581948825 17444847243096456436461619)
      ·
        refine ⟨26167270864644684654692429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17444847243096456436461619 26167270864644684654692429)
        ·
          refine ⟨9812726574241756745509661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26167270864644684654692429 9812726574241756745509661)
          ·
            refine ⟨3679772465340658779566123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9812726574241756745509661 3679772465340658779566123)
            ·
              refine ⟨5519658698010988169349185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679772465340658779566123 5519658698010988169349185)
              ·
                refine ⟨4139744023508241127011889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519658698010988169349185 4139744023508241127011889)
                ·
                  refine ⟨3104808017631180845258917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139744023508241127011889 3104808017631180845258917)
                  ·
                    refine ⟨582151503305846408486047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104808017631180845258917 582151503305846408486047)
                    ·
                      rfl

theorem cell22_1700604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1700604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700604 prefixEnd_1700604 := by exact prefixLift 1700604
  have htrace : WordTrace (prefixWord ++ tailWord_1700604) baseStart_1700604 baseEnd_1700604 := by
    simpa [prefixWord, tailWord_1700604, baseEnd_1700604] using wordTrace_append hprefix tailTrace_1700604
  have hstable : (prefixWord ++ tailWord_1700604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700604).length < 2 ^ (prefixWord ++ tailWord_1700604).sum := by decide
  have hdescent : baseEnd_1700604 < baseStart_1700604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700606 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1700606 : Nat := 118140960795 + 1700606 * 2 ^ 59
def prefixEnd_1700606 : Nat := 4983230072969 + 3 ^ 40 * 1700606 * 2
def baseEnd_1700606 : Nat := 582152187946719069936041

theorem tailTrace_1700606 : CollatzResearch.WordTrace tailWord_1700606 prefixEnd_1700606 582152187946719069936041 := by
  unfold tailWord_1700606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753274559625297153346209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41350797651334918151179781 7753274559625297153346209)
  ·
    refine ⟨5814955919718972865009657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7753274559625297153346209 5814955919718972865009657)
    ·
      refine ⟨4361216939789229648757243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5814955919718972865009657 4361216939789229648757243)
      ·
        refine ⟨6541825409683844473135865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361216939789229648757243 6541825409683844473135865)
        ·
          refine ⟨4906369057262883354851899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6541825409683844473135865 4906369057262883354851899)
          ·
            refine ⟨7359553585894325032277849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4906369057262883354851899 7359553585894325032277849)
            ·
              refine ⟨5519665189420743774208387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359553585894325032277849 5519665189420743774208387)
              ·
                refine ⟨8279497784131115661312581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519665189420743774208387 8279497784131115661312581)
                ·
                  refine ⟨1552405834524584186496109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8279497784131115661312581 1552405834524584186496109)
                  ·
                    refine ⟨582152187946719069936041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552405834524584186496109 582152187946719069936041)
                    ·
                      rfl

theorem cell22_1700606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1700606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700606 prefixEnd_1700606 := by exact prefixLift 1700606
  have htrace : WordTrace (prefixWord ++ tailWord_1700606) baseStart_1700606 baseEnd_1700606 := by
    simpa [prefixWord, tailWord_1700606, baseEnd_1700606] using wordTrace_append hprefix tailTrace_1700606
  have hstable : (prefixWord ++ tailWord_1700606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700606).length < 2 ^ (prefixWord ++ tailWord_1700606).sum := by decide
  have hdescent : baseEnd_1700606 < baseStart_1700606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700634 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1700634 : Nat := 118140960795 + 1700634 * 2 ^ 59
def prefixEnd_1700634 : Nat := 4983230072969 + 3 ^ 40 * 1700634 * 2
def baseEnd_1700634 : Nat := 582161772918936330235955

theorem tailTrace_1700634 : CollatzResearch.WordTrace tailWord_1700634 prefixEnd_1700634 582161772918936330235955 := by
  unfold tailWord_1700634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506804430225234502197239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41351478480600625339192637 15506804430225234502197239)
  ·
    refine ⟨23260206645337851753295859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15506804430225234502197239 23260206645337851753295859)
    ·
      refine ⟨34890309968006777629943789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23260206645337851753295859 34890309968006777629943789)
      ·
        refine ⟨13083866238002541611228921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34890309968006777629943789 13083866238002541611228921)
        ·
          refine ⟨9812899678501906208421691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13083866238002541611228921 9812899678501906208421691)
          ·
            refine ⟨14719349517752859312632537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812899678501906208421691 14719349517752859312632537)
            ·
              refine ⟨11039512138314644484474403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14719349517752859312632537 11039512138314644484474403)
              ·
                refine ⟨16559268207471966726711605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11039512138314644484474403 16559268207471966726711605)
                ·
                  refine ⟨1552431394450496880629213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16559268207471966726711605 1552431394450496880629213)
                  ·
                    refine ⟨582161772918936330235955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552431394450496880629213 582161772918936330235955)
                    ·
                      rfl

theorem cell22_1700634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1700634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700634 prefixEnd_1700634 := by exact prefixLift 1700634
  have htrace : WordTrace (prefixWord ++ tailWord_1700634) baseStart_1700634 baseEnd_1700634 := by
    simpa [prefixWord, tailWord_1700634, baseEnd_1700634] using wordTrace_append hprefix tailTrace_1700634
  have hstable : (prefixWord ++ tailWord_1700634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700634).length < 2 ^ (prefixWord ++ tailWord_1700634).sum := by decide
  have hdescent : baseEnd_1700634 < baseStart_1700634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700664 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_1700664 : Nat := 118140960795 + 1700664 * 2 ^ 59
def prefixEnd_1700664 : Nat := 4983230072969 + 3 ^ 40 * 1700664 * 2
def baseEnd_1700664 : Nat := 194057347510675417328621

theorem tailTrace_1700664 : CollatzResearch.WordTrace tailWord_1700664 prefixEnd_1700664 194057347510675417328621 := by
  unfold tailWord_1700664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014155955396126566190523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41352207940528168754920697 31014155955396126566190523)
  ·
    refine ⟨46521233933094189849285785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31014155955396126566190523 46521233933094189849285785)
    ·
      refine ⟨34890925449820642386964339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46521233933094189849285785 34890925449820642386964339)
      ·
        refine ⟨52336388174730963580446509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34890925449820642386964339 52336388174730963580446509)
        ·
          refine ⟨19626145565524111342667441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52336388174730963580446509 19626145565524111342667441)
          ·
            refine ⟨14719609174143083507000581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19626145565524111342667441 14719609174143083507000581)
            ·
              refine ⟨2759926720151828157562609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14719609174143083507000581 2759926720151828157562609)
              ·
                refine ⟨2069945040113871118171957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759926720151828157562609 2069945040113871118171957)
                ·
                  refine ⟨194057347510675417328621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2069945040113871118171957 194057347510675417328621)
                  ·
                    rfl

theorem cell22_1700664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_1700664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700664 prefixEnd_1700664 := by exact prefixLift 1700664
  have htrace : WordTrace (prefixWord ++ tailWord_1700664) baseStart_1700664 baseEnd_1700664 := by
    simpa [prefixWord, tailWord_1700664, baseEnd_1700664] using wordTrace_append hprefix tailTrace_1700664
  have hstable : (prefixWord ++ tailWord_1700664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700664).length < 2 ^ (prefixWord ++ tailWord_1700664).sum := by decide
  have hdescent : baseEnd_1700664 < baseStart_1700664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700711 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1700711 : Nat := 118140960795 + 1700711 * 2 ^ 59
def prefixEnd_1700711 : Nat := 4983230072969 + 3 ^ 40 * 1700711 * 2
def baseEnd_1700711 : Nat := 582188131592533796060719

theorem tailTrace_1700711 : CollatzResearch.WordTrace tailWord_1700711 prefixEnd_1700711 582188131592533796060719 := by
  unfold tailWord_1700711
  simp only [CollatzResearch.WordTrace]
  refine ⟨62030026141621980159341987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41353350761081320106227991 62030026141621980159341987)
  ·
    refine ⟨93045039212432970239012981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62030026141621980159341987 93045039212432970239012981)
    ·
      refine ⟨8722972426165590959907467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93045039212432970239012981 8722972426165590959907467)
      ·
        refine ⟨13084458639248386439861201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722972426165590959907467 13084458639248386439861201)
        ·
          refine ⟨9813343979436289829895901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13084458639248386439861201 9813343979436289829895901)
          ·
            refine ⟨3680003992288608686210963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9813343979436289829895901 3680003992288608686210963)
            ·
              refine ⟨5520005988432913029316445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680003992288608686210963 5520005988432913029316445)
              ·
                refine ⟨2070002245662342385993667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5520005988432913029316445 2070002245662342385993667)
                ·
                  refine ⟨3105003368493513578990501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070002245662342385993667 3105003368493513578990501)
                  ·
                    refine ⟨582188131592533796060719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105003368493513578990501 582188131592533796060719)
                    ·
                      rfl

theorem cell22_1700711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1700711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700711 prefixEnd_1700711 := by exact prefixLift 1700711
  have htrace : WordTrace (prefixWord ++ tailWord_1700711) baseStart_1700711 baseEnd_1700711 := by
    simpa [prefixWord, tailWord_1700711, baseEnd_1700711] using wordTrace_append hprefix tailTrace_1700711
  have hstable : (prefixWord ++ tailWord_1700711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700711).length < 2 ^ (prefixWord ++ tailWord_1700711).sum := by decide
  have hdescent : baseEnd_1700711 < baseStart_1700711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700726 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1700726 : Nat := 118140960795 + 1700726 * 2 ^ 59
def prefixEnd_1700726 : Nat := 4983230072969 + 3 ^ 40 * 1700726 * 2
def baseEnd_1700726 : Nat := 194064422133026252311891

theorem tailTrace_1700726 : CollatzResearch.WordTrace tailWord_1700726 prefixEnd_1700726 194064422133026252311891 := by
  unfold tailWord_1700726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876910827285477357571127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41353715491045091814092021 3876910827285477357571127)
  ·
    refine ⟨5815366240928216036356691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3876910827285477357571127 5815366240928216036356691)
    ·
      refine ⟨8723049361392324054535037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5815366240928216036356691 8723049361392324054535037)
      ·
        refine ⟨3271143510522121520450639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8723049361392324054535037 3271143510522121520450639)
        ·
          refine ⟨4906715265783182280675959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271143510522121520450639 4906715265783182280675959)
          ·
            refine ⟨7360072898674773421013939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4906715265783182280675959 7360072898674773421013939)
            ·
              refine ⟨11040109348012160131520909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360072898674773421013939 11040109348012160131520909)
              ·
                refine ⟨4140041005504560049320341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11040109348012160131520909 4140041005504560049320341)
                ·
                  refine ⟨194064422133026252311891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4140041005504560049320341 194064422133026252311891)
                  ·
                    rfl

theorem cell22_1700726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1700726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700726 prefixEnd_1700726 := by exact prefixLift 1700726
  have htrace : WordTrace (prefixWord ++ tailWord_1700726) baseStart_1700726 baseEnd_1700726 := by
    simpa [prefixWord, tailWord_1700726, baseEnd_1700726] using wordTrace_append hprefix tailTrace_1700726
  have hstable : (prefixWord ++ tailWord_1700726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700726).length < 2 ^ (prefixWord ++ tailWord_1700726).sum := by decide
  have hdescent : baseEnd_1700726 < baseStart_1700726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700741 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_1700741 : Nat := 118140960795 + 1700741 * 2 ^ 59
def prefixEnd_1700741 : Nat := 4983230072969 + 3 ^ 40 * 1700741 * 2
def baseEnd_1700741 : Nat := 582198401205623717810627

theorem tailTrace_1700741 : CollatzResearch.WordTrace tailWord_1700741 prefixEnd_1700741 582198401205623717810627 := by
  unfold tailWord_1700741
  simp only [CollatzResearch.WordTrace]
  refine ⟨62031120331513295282934077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41354080221008863521956051 62031120331513295282934077)
  ·
    refine ⟨23261670124317485731100279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62031120331513295282934077 23261670124317485731100279)
    ·
      refine ⟨34892505186476228596650419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23261670124317485731100279 34892505186476228596650419)
      ·
        refine ⟨52338757779714342894975629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34892505186476228596650419 52338757779714342894975629)
        ·
          refine ⟨19627034167392878585615861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52338757779714342894975629 19627034167392878585615861)
          ·
            refine ⟨1840034453193082367401487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19627034167392878585615861 1840034453193082367401487)
            ·
              refine ⟨2760051679789623551102231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840034453193082367401487 2760051679789623551102231)
              ·
                refine ⟨4140077519684435326653347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760051679789623551102231 4140077519684435326653347)
                ·
                  refine ⟨6210116279526652989980021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140077519684435326653347 6210116279526652989980021)
                  ·
                    refine ⟨582198401205623717810627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6210116279526652989980021 582198401205623717810627)
                    ·
                      rfl

theorem cell22_1700741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_1700741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700741 prefixEnd_1700741 := by exact prefixLift 1700741
  have htrace : WordTrace (prefixWord ++ tailWord_1700741) baseStart_1700741 baseEnd_1700741 := by
    simpa [prefixWord, tailWord_1700741, baseEnd_1700741] using wordTrace_append hprefix tailTrace_1700741
  have hstable : (prefixWord ++ tailWord_1700741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700741).length < 2 ^ (prefixWord ++ tailWord_1700741).sum := by decide
  have hdescent : baseEnd_1700741 < baseStart_1700741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700756 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1700756 : Nat := 118140960795 + 1700756 * 2 ^ 59
def prefixEnd_1700756 : Nat := 4983230072969 + 3 ^ 40 * 1700756 * 2
def baseEnd_1700756 : Nat := 582203536012168678685581

theorem tailTrace_1700756 : CollatzResearch.WordTrace tailWord_1700756 prefixEnd_1700756 582203536012168678685581 := by
  unfold tailWord_1700756
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015833713229476422365061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41354444950972635229820081 31015833713229476422365061)
  ·
    refine ⟨5815468821230526829193449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31015833713229476422365061 5815468821230526829193449)
    ·
      refine ⟨4361601615922895121895087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5815468821230526829193449 4361601615922895121895087)
      ·
        refine ⟨6542402423884342682842631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361601615922895121895087 6542402423884342682842631)
        ·
          refine ⟨9813603635826514024263947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542402423884342682842631 9813603635826514024263947)
          ·
            refine ⟨14720405453739771036395921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813603635826514024263947 14720405453739771036395921)
            ·
              refine ⟨11040304090304828277296941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720405453739771036395921 11040304090304828277296941)
              ·
                refine ⟨4140114033864310603986353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11040304090304828277296941 4140114033864310603986353)
                ·
                  refine ⟨3105085525398232952989765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140114033864310603986353 3105085525398232952989765)
                  ·
                    refine ⟨582203536012168678685581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105085525398232952989765 582203536012168678685581)
                    ·
                      rfl

theorem cell22_1700756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1700756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700756 prefixEnd_1700756 := by exact prefixLift 1700756
  have htrace : WordTrace (prefixWord ++ tailWord_1700756) baseStart_1700756 baseEnd_1700756 := by
    simpa [prefixWord, tailWord_1700756, baseEnd_1700756] using wordTrace_append hprefix tailTrace_1700756
  have hstable : (prefixWord ++ tailWord_1700756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700756).length < 2 ^ (prefixWord ++ tailWord_1700756).sum := by decide
  have hdescent : baseEnd_1700756 < baseStart_1700756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700788 : List Nat := [2, 5, 2, 1, 1, 2, 2, 7]
def baseStart_1700788 : Nat := 118140960795 + 1700788 * 2 ^ 59
def prefixEnd_1700788 : Nat := 4983230072969 + 3 ^ 40 * 1700788 * 2
def baseEnd_1700788 : Nat := 64690498918459029098387

theorem tailTrace_1700788 : CollatzResearch.WordTrace tailWord_1700788 prefixEnd_1700788 64690498918459029098387 := by
  unfold tailWord_1700788
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016417281171511154947509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41355223041562014873263345 31016417281171511154947509)
  ·
    refine ⟨2907789120109829170776329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31016417281171511154947509 2907789120109829170776329)
    ·
      refine ⟨2180841840082371878082247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2907789120109829170776329 2180841840082371878082247)
      ·
        refine ⟨3271262760123557817123371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180841840082371878082247 3271262760123557817123371)
        ·
          refine ⟨4906894140185336725685057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271262760123557817123371 4906894140185336725685057)
          ·
            refine ⟨3680170605139002544263793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906894140185336725685057 3680170605139002544263793)
            ·
              refine ⟨2760127953854251908197845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680170605139002544263793 2760127953854251908197845)
              ·
                refine ⟨64690498918459029098387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2760127953854251908197845 64690498918459029098387)
                ·
                  rfl

theorem cell22_1700788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_1700788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700788 prefixEnd_1700788 := by exact prefixLift 1700788
  have htrace : WordTrace (prefixWord ++ tailWord_1700788) baseStart_1700788 baseEnd_1700788 := by
    simpa [prefixWord, tailWord_1700788, baseEnd_1700788] using wordTrace_append hprefix tailTrace_1700788
  have hstable : (prefixWord ++ tailWord_1700788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700788).length < 2 ^ (prefixWord ++ tailWord_1700788).sum := by decide
  have hdescent : baseEnd_1700788 < baseStart_1700788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700837 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_1700837 : Nat := 118140960795 + 1700837 * 2 ^ 59
def prefixEnd_1700837 : Nat := 4983230072969 + 3 ^ 40 * 1700837 * 2
def baseEnd_1700837 : Nat := 582231263967511467410333

theorem tailTrace_1700837 : CollatzResearch.WordTrace tailWord_1700837 prefixEnd_1700837 582231263967511467410333 := by
  unfold tailWord_1700837
  simp only [CollatzResearch.WordTrace]
  refine ⟨62034621739165503678428765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41356414492777002452285843 62034621739165503678428765)
  ·
    refine ⟨23262983152187063879410787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62034621739165503678428765 23262983152187063879410787)
    ·
      refine ⟨34894474728280595819116181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23262983152187063879410787 34894474728280595819116181)
      ·
        refine ⟨1635678502888152929021071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34894474728280595819116181 1635678502888152929021071)
        ·
          refine ⟨2453517754332229393531607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635678502888152929021071 2453517754332229393531607)
          ·
            refine ⟨3680276631498344090297411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453517754332229393531607 3680276631498344090297411)
            ·
              refine ⟨5520414947247516135446117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680276631498344090297411 5520414947247516135446117)
              ·
                refine ⟨1035077802608909275396147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5520414947247516135446117 1035077802608909275396147)
                ·
                  refine ⟨1552616703913363913094221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035077802608909275396147 1552616703913363913094221)
                  ·
                    refine ⟨582231263967511467410333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552616703913363913094221 582231263967511467410333)
                    ·
                      rfl

theorem cell22_1700837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_1700837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700837 prefixEnd_1700837 := by exact prefixLift 1700837
  have htrace : WordTrace (prefixWord ++ tailWord_1700837) baseStart_1700837 baseEnd_1700837 := by
    simpa [prefixWord, tailWord_1700837, baseEnd_1700837] using wordTrace_append hprefix tailTrace_1700837
  have hstable : (prefixWord ++ tailWord_1700837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700837).length < 2 ^ (prefixWord ++ tailWord_1700837).sum := by decide
  have hdescent : baseEnd_1700837 < baseStart_1700837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700876 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_1700876 : Nat := 118140960795 + 1700876 * 2 ^ 59
def prefixEnd_1700876 : Nat := 4983230072969 + 3 ^ 40 * 1700876 * 2
def baseEnd_1700876 : Nat := 582244614464528365685213

theorem tailTrace_1700876 : CollatzResearch.WordTrace tailWord_1700876 prefixEnd_1700876 582244614464528365685213 := by
  unfold tailWord_1700876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31018022093012106669549241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41357362790682808892732321 31018022093012106669549241)
  ·
    refine ⟨23263516569759080002161931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31018022093012106669549241 23263516569759080002161931)
    ·
      refine ⟨34895274854638620003242897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23263516569759080002161931 34895274854638620003242897)
      ·
        refine ⟨26171456140978965002432173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34895274854638620003242897 26171456140978965002432173)
        ·
          refine ⟨9814296052867111875912065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26171456140978965002432173 9814296052867111875912065)
          ·
            refine ⟨7360722039650333906934049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9814296052867111875912065 7360722039650333906934049)
            ·
              refine ⟨5520541529737750430200537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360722039650333906934049 5520541529737750430200537)
              ·
                refine ⟨4140406147303312822650403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520541529737750430200537 4140406147303312822650403)
                ·
                  refine ⟨6210609220954969233975605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140406147303312822650403 6210609220954969233975605)
                  ·
                    refine ⟨582244614464528365685213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6210609220954969233975605 582244614464528365685213)
                    ·
                      rfl

theorem cell22_1700876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_1700876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700876 prefixEnd_1700876 := by exact prefixLift 1700876
  have htrace : WordTrace (prefixWord ++ tailWord_1700876) baseStart_1700876 baseEnd_1700876 := by
    simpa [prefixWord, tailWord_1700876, baseEnd_1700876] using wordTrace_append hprefix tailTrace_1700876
  have hstable : (prefixWord ++ tailWord_1700876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700876).length < 2 ^ (prefixWord ++ tailWord_1700876).sum := by decide
  have hdescent : baseEnd_1700876 < baseStart_1700876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700878 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1700878 : Nat := 118140960795 + 1700878 * 2 ^ 59
def prefixEnd_1700878 : Nat := 4983230072969 + 3 ^ 40 * 1700878 * 2
def baseEnd_1700878 : Nat := 194081766368467009045069

theorem tailTrace_1700878 : CollatzResearch.WordTrace tailWord_1700878 prefixEnd_1700878 194081766368467009045069 := by
  unfold tailWord_1700878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754514641502120960083911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41357411421344645120447525 7754514641502120960083911)
  ·
    refine ⟨11631771962253181440125867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7754514641502120960083911 11631771962253181440125867)
    ·
      refine ⟨17447657943379772160188801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11631771962253181440125867 17447657943379772160188801)
      ·
        refine ⟨13085743457534829120141601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17447657943379772160188801 13085743457534829120141601)
        ·
          refine ⟨9814307593151121840106201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13085743457534829120141601 9814307593151121840106201)
          ·
            refine ⟨7360730694863341380079651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9814307593151121840106201 7360730694863341380079651)
            ·
              refine ⟨11041096042295012070119477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360730694863341380079651 11041096042295012070119477)
              ·
                refine ⟨1035102753965157381573701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11041096042295012070119477 1035102753965157381573701)
                ·
                  refine ⟨194081766368467009045069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035102753965157381573701 194081766368467009045069)
                  ·
                    rfl

theorem cell22_1700878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1700878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700878 prefixEnd_1700878 := by exact prefixLift 1700878
  have htrace : WordTrace (prefixWord ++ tailWord_1700878) baseStart_1700878 baseEnd_1700878 := by
    simpa [prefixWord, tailWord_1700878, baseEnd_1700878] using wordTrace_append hprefix tailTrace_1700878
  have hstable : (prefixWord ++ tailWord_1700878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700878).length < 2 ^ (prefixWord ++ tailWord_1700878).sum := by decide
  have hdescent : baseEnd_1700878 < baseStart_1700878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700951 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 5]
def baseStart_1700951 : Nat := 118140960795 + 1700951 * 2 ^ 59
def prefixEnd_1700951 : Nat := 4983230072969 + 3 ^ 40 * 1700951 * 2
def baseEnd_1700951 : Nat := 194090096165751056686661

theorem tailTrace_1700951 : CollatzResearch.WordTrace tailWord_1700951 prefixEnd_1700951 194090096165751056686661 := by
  unfold tailWord_1700951
  simp only [CollatzResearch.WordTrace]
  refine ⟨62038779660752501148078707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41359186440501667432052471 62038779660752501148078707)
  ·
    refine ⟨93058169491128751722118061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62038779660752501148078707 93058169491128751722118061)
    ·
      refine ⟨34896813559173281895794273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93058169491128751722118061 34896813559173281895794273)
      ·
        refine ⟨26172610169379961421845705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34896813559173281895794273 26172610169379961421845705)
        ·
          refine ⟨19629457627034971066384279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26172610169379961421845705 19629457627034971066384279)
          ·
            refine ⟨29444186440552456599576419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19629457627034971066384279 29444186440552456599576419)
            ·
              refine ⟨44166279660828684899364629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29444186440552456599576419 44166279660828684899364629)
              ·
                refine ⟨2070294359101344604657717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44166279660828684899364629 2070294359101344604657717)
                ·
                  refine ⟨194090096165751056686661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2070294359101344604657717 194090096165751056686661)
                  ·
                    rfl

theorem cell22_1700951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 5].length) (baseStart_1700951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1700951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1700951 prefixEnd_1700951 := by exact prefixLift 1700951
  have htrace : WordTrace (prefixWord ++ tailWord_1700951) baseStart_1700951 baseEnd_1700951 := by
    simpa [prefixWord, tailWord_1700951, baseEnd_1700951] using wordTrace_append hprefix tailTrace_1700951
  have hstable : (prefixWord ++ tailWord_1700951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700951).length < 2 ^ (prefixWord ++ tailWord_1700951).sum := by decide
  have hdescent : baseEnd_1700951 < baseStart_1700951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701028 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1701028 : Nat := 118140960795 + 1701028 * 2 ^ 59
def prefixEnd_1701028 : Nat := 4983230072969 + 3 ^ 40 * 1701028 * 2
def baseEnd_1701028 : Nat := 582296647170850635884747

theorem tailTrace_1701028 : CollatzResearch.WordTrace tailWord_1701028 prefixEnd_1701028 582296647170850635884747 := by
  unfold tailWord_1701028
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020794040736771649315869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41361058720982362199087825 31020794040736771649315869)
  ·
    refine ⟨11632797765276289368493451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31020794040736771649315869 11632797765276289368493451)
    ·
      refine ⟨17449196647914434052740177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11632797765276289368493451 17449196647914434052740177)
      ·
        refine ⟨13086897485935825539555133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17449196647914434052740177 13086897485935825539555133)
        ·
          refine ⟨4907586557225934577333175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13086897485935825539555133 4907586557225934577333175)
          ·
            refine ⟨7361379835838901865999763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907586557225934577333175 7361379835838901865999763)
            ·
              refine ⟨11042069753758352798999645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361379835838901865999763 11042069753758352798999645)
              ·
                refine ⟨4140776157659382299624867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11042069753758352798999645 4140776157659382299624867)
                ·
                  refine ⟨6211164236489073449437301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140776157659382299624867 6211164236489073449437301)
                  ·
                    refine ⟨582296647170850635884747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6211164236489073449437301 582296647170850635884747)
                    ·
                      rfl

theorem cell22_1701028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1701028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701028 prefixEnd_1701028 := by exact prefixLift 1701028
  have htrace : WordTrace (prefixWord ++ tailWord_1701028) baseStart_1701028 baseEnd_1701028 := by
    simpa [prefixWord, tailWord_1701028, baseEnd_1701028] using wordTrace_append hprefix tailTrace_1701028
  have hstable : (prefixWord ++ tailWord_1701028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701028).length < 2 ^ (prefixWord ++ tailWord_1701028).sum := by decide
  have hdescent : baseEnd_1701028 < baseStart_1701028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701043 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 2, 4]
def baseStart_1701043 : Nat := 118140960795 + 1701043 * 2 ^ 59
def prefixEnd_1701043 : Nat := 4983230072969 + 3 ^ 40 * 1701043 * 2
def baseEnd_1701043 : Nat := 582301781977395596759701

theorem tailTrace_1701043 : CollatzResearch.WordTrace tailWord_1701043 prefixEnd_1701043 582301781977395596759701 := by
  unfold tailWord_1701043
  simp only [CollatzResearch.WordTrace]
  refine ⟨62042135176419200860427783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41361423450946133906951855 62042135176419200860427783)
  ·
    refine ⟨93063202764628801290641675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62042135176419200860427783 93063202764628801290641675)
    ·
      refine ⟨139594804146943201935962513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93063202764628801290641675 139594804146943201935962513)
      ·
        refine ⟨104696103110207401451971885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139594804146943201935962513 104696103110207401451971885)
        ·
          refine ⟨39261038666327775544489457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104696103110207401451971885 39261038666327775544489457)
          ·
            refine ⟨29445778999745831658367093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39261038666327775544489457 29445778999745831658367093)
            ·
              refine ⟨2760541781226171717971915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29445778999745831658367093 2760541781226171717971915)
              ·
                refine ⟨4140812671839257576957873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760541781226171717971915 4140812671839257576957873)
                ·
                  refine ⟨3105609503879443182718405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140812671839257576957873 3105609503879443182718405)
                  ·
                    refine ⟨582301781977395596759701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105609503879443182718405 582301781977395596759701)
                    ·
                      rfl

theorem cell22_1701043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_1701043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701043 prefixEnd_1701043 := by exact prefixLift 1701043
  have htrace : WordTrace (prefixWord ++ tailWord_1701043) baseStart_1701043 baseEnd_1701043 := by
    simpa [prefixWord, tailWord_1701043, baseEnd_1701043] using wordTrace_append hprefix tailTrace_1701043
  have hstable : (prefixWord ++ tailWord_1701043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701043).length < 2 ^ (prefixWord ++ tailWord_1701043).sum := by decide
  have hdescent : baseEnd_1701043 < baseStart_1701043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701071 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1701071 : Nat := 118140960795 + 1701071 * 2 ^ 59
def prefixEnd_1701071 : Nat := 4983230072969 + 3 ^ 40 * 1701071 * 2
def baseEnd_1701071 : Nat := 582311366949612857059615

theorem tailTrace_1701071 : CollatzResearch.WordTrace tailWord_1701071 prefixEnd_1701071 582311366949612857059615 := by
  unfold tailWord_1701071
  simp only [CollatzResearch.WordTrace]
  refine ⟨62043156420317761642447067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41362104280211841094964711 62043156420317761642447067)
  ·
    refine ⟨93064734630476642463670601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62043156420317761642447067 93064734630476642463670601)
    ·
      refine ⟨69798550972857481847752951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93064734630476642463670601 69798550972857481847752951)
      ·
        refine ⟨104697826459286222771629427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69798550972857481847752951 104697826459286222771629427)
        ·
          refine ⟨157046739688929334157444141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104697826459286222771629427 157046739688929334157444141)
          ·
            refine ⟨58892527383348500309041553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157046739688929334157444141 58892527383348500309041553)
            ·
              refine ⟨44169395537511375231781165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58892527383348500309041553 44169395537511375231781165)
              ·
                refine ⟨16563523326566765711917937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44169395537511375231781165 16563523326566765711917937)
                ·
                  refine ⟨12422642494925074283938453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16563523326566765711917937 12422642494925074283938453)
                  ·
                    refine ⟨582311366949612857059615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12422642494925074283938453 582311366949612857059615)
                    ·
                      rfl

theorem cell22_1701071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1701071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701071 prefixEnd_1701071 := by exact prefixLift 1701071
  have htrace : WordTrace (prefixWord ++ tailWord_1701071) baseStart_1701071 baseEnd_1701071 := by
    simpa [prefixWord, tailWord_1701071, baseEnd_1701071] using wordTrace_append hprefix tailTrace_1701071
  have hstable : (prefixWord ++ tailWord_1701071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701071).length < 2 ^ (prefixWord ++ tailWord_1701071).sum := by decide
  have hdescent : baseEnd_1701071 < baseStart_1701071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701107 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 1, 3]
def baseStart_1701107 : Nat := 118140960795 + 1701107 * 2 ^ 59
def prefixEnd_1701107 : Nat := 4983230072969 + 3 ^ 40 * 1701107 * 2
def baseEnd_1701107 : Nat := 582323690485320763159505

theorem tailTrace_1701107 : CollatzResearch.WordTrace tailWord_1701107 prefixEnd_1701107 582323690485320763159505 := by
  unfold tailWord_1701107
  simp only [CollatzResearch.WordTrace]
  refine ⟨62044469448187339790757575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41362979632124893193838383 62044469448187339790757575)
  ·
    refine ⟨93066704172281009686136363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62044469448187339790757575 93066704172281009686136363)
    ·
      refine ⟨139600056258421514529204545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93066704172281009686136363 139600056258421514529204545)
      ·
        refine ⟨104700042193816135896903409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139600056258421514529204545 104700042193816135896903409)
        ·
          refine ⟨78525031645362101922677557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104700042193816135896903409 78525031645362101922677557)
          ·
            refine ⟨7361721716752697055251021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78525031645362101922677557 7361721716752697055251021)
            ·
              refine ⟨2760645643782261395719133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7361721716752697055251021 2760645643782261395719133)
              ·
                refine ⟨1035242116418348023394675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2760645643782261395719133 1035242116418348023394675)
                ·
                  refine ⟨1552863174627522035092013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035242116418348023394675 1552863174627522035092013)
                  ·
                    refine ⟨582323690485320763159505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1552863174627522035092013 582323690485320763159505)
                    ·
                      rfl

theorem cell22_1701107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 1, 3].length) (baseStart_1701107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701107 prefixEnd_1701107 := by exact prefixLift 1701107
  have htrace : WordTrace (prefixWord ++ tailWord_1701107) baseStart_1701107 baseEnd_1701107 := by
    simpa [prefixWord, tailWord_1701107, baseEnd_1701107] using wordTrace_append hprefix tailTrace_1701107
  have hstable : (prefixWord ++ tailWord_1701107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701107).length < 2 ^ (prefixWord ++ tailWord_1701107).sum := by decide
  have hdescent : baseEnd_1701107 < baseStart_1701107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701148 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_1701148 : Nat := 118140960795 + 1701148 * 2 ^ 59
def prefixEnd_1701148 : Nat := 4983230072969 + 3 ^ 40 * 1701148 * 2
def baseEnd_1701148 : Nat := 194112575207736774294793

theorem tailTrace_1701148 : CollatzResearch.WordTrace tailWord_1701148 prefixEnd_1701148 194112575207736774294793 := by
  unfold tailWord_1701148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022982420519401896500049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41363976560692535862000065 31022982420519401896500049)
  ·
    refine ⟨23267236815389551422375037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31022982420519401896500049 23267236815389551422375037)
    ·
      refine ⟨8725213805771081783390639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23267236815389551422375037 8725213805771081783390639)
      ·
        refine ⟨13087820708656622675085959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725213805771081783390639 13087820708656622675085959)
        ·
          refine ⟨19631731062984934012628939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13087820708656622675085959 19631731062984934012628939)
          ·
            refine ⟨29447596594477401018943409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19631731062984934012628939 29447596594477401018943409)
            ·
              refine ⟨22085697445858050764207557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29447596594477401018943409 22085697445858050764207557)
              ·
                refine ⟨4141068271098384518288917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22085697445858050764207557 4141068271098384518288917)
                ·
                  refine ⟨194112575207736774294793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4141068271098384518288917 194112575207736774294793)
                  ·
                    rfl

theorem cell22_1701148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_1701148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701148 prefixEnd_1701148 := by exact prefixLift 1701148
  have htrace : WordTrace (prefixWord ++ tailWord_1701148) baseStart_1701148 baseEnd_1701148 := by
    simpa [prefixWord, tailWord_1701148, baseEnd_1701148] using wordTrace_append hprefix tailTrace_1701148
  have hstable : (prefixWord ++ tailWord_1701148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701148).length < 2 ^ (prefixWord ++ tailWord_1701148).sum := by decide
  have hdescent : baseEnd_1701148 < baseStart_1701148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701182 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1701182 : Nat := 118140960795 + 1701182 * 2 ^ 59
def prefixEnd_1701182 : Nat := 4983230072969 + 3 ^ 40 * 1701182 * 2
def baseEnd_1701182 : Nat := 194116454839348522511425

theorem tailTrace_1701182 : CollatzResearch.WordTrace tailWord_1701182 prefixEnd_1701182 194116454839348522511425 := by
  unfold tailWord_1701182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755900615364453449967225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41364803281943751733158533 7755900615364453449967225)
  ·
    refine ⟨5816925461523340087475419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7755900615364453449967225 5816925461523340087475419)
    ·
      refine ⟨8725388192285010131213129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5816925461523340087475419 8725388192285010131213129)
      ·
        refine ⟨6544041144213757598409847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8725388192285010131213129 6544041144213757598409847)
        ·
          refine ⟨9816061716320636397614771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544041144213757598409847 9816061716320636397614771)
          ·
            refine ⟨14724092574480954596422157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816061716320636397614771 14724092574480954596422157)
            ·
              refine ⟨5521534715430357973658309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14724092574480954596422157 5521534715430357973658309)
              ·
                refine ⟨1035287759143192120060933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5521534715430357973658309 1035287759143192120060933)
                ·
                  refine ⟨194116454839348522511425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035287759143192120060933 194116454839348522511425)
                  ·
                    rfl

theorem cell22_1701182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1701182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701182 prefixEnd_1701182 := by exact prefixLift 1701182
  have htrace : WordTrace (prefixWord ++ tailWord_1701182) baseStart_1701182 baseEnd_1701182 := by
    simpa [prefixWord, tailWord_1701182, baseEnd_1701182] using wordTrace_append hprefix tailTrace_1701182
  have hstable : (prefixWord ++ tailWord_1701182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701182).length < 2 ^ (prefixWord ++ tailWord_1701182).sum := by decide
  have hdescent : baseEnd_1701182 < baseStart_1701182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701193 : List Nat := [1, 2, 1, 1, 2, 3, 5, 7]
def baseStart_1701193 : Nat := 118140960795 + 1701193 * 2 ^ 59
def prefixEnd_1701193 : Nat := 4983230072969 + 3 ^ 40 * 1701193 * 2
def baseEnd_1701193 : Nat := 64705903338093911723249

theorem tailTrace_1701193 : CollatzResearch.WordTrace tailWord_1701193 prefixEnd_1701193 64705903338093911723249 := by
  unfold tailWord_1701193
  simp only [CollatzResearch.WordTrace]
  refine ⟨62047606125875776478388233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41365070750583850985592155 62047606125875776478388233)
  ·
    refine ⟨46535704594406832358791175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62047606125875776478388233 46535704594406832358791175)
    ·
      refine ⟨69803556891610248538186763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46535704594406832358791175 69803556891610248538186763)
      ·
        refine ⟨104705335337415372807280145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69803556891610248538186763 104705335337415372807280145)
        ·
          refine ⟨78529001503061529605460109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104705335337415372807280145 78529001503061529605460109)
          ·
            refine ⟨29448375563648073602047541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78529001503061529605460109 29448375563648073602047541)
            ·
              refine ⟨2760785209092006900191957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29448375563648073602047541 2760785209092006900191957)
              ·
                refine ⟨64705903338093911723249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2760785209092006900191957 64705903338093911723249)
                ·
                  rfl

theorem cell22_1701193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 7].length) (baseStart_1701193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701193 prefixEnd_1701193 := by exact prefixLift 1701193
  have htrace : WordTrace (prefixWord ++ tailWord_1701193) baseStart_1701193 baseEnd_1701193 := by
    simpa [prefixWord, tailWord_1701193, baseEnd_1701193] using wordTrace_append hprefix tailTrace_1701193
  have hstable : (prefixWord ++ tailWord_1701193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701193).length < 2 ^ (prefixWord ++ tailWord_1701193).sum := by decide
  have hdescent : baseEnd_1701193 < baseStart_1701193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701293 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_1701293 : Nat := 118140960795 + 1701293 * 2 ^ 59
def prefixEnd_1701293 : Nat := 4983230072969 + 3 ^ 40 * 1701293 * 2
def baseEnd_1701293 : Nat := 582387362086478278008935

theorem tailTrace_1701293 : CollatzResearch.WordTrace tailWord_1701293 prefixEnd_1701293 582387362086478278008935 := by
  unfold tailWord_1701293
  simp only [CollatzResearch.WordTrace]
  refine ⟨62051253425513493557028533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41367502283675662371352355 62051253425513493557028533)
  ·
    refine ⟨5817305008641890020971425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62051253425513493557028533 5817305008641890020971425)
    ·
      refine ⟨4362978756481417515728569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5817305008641890020971425 4362978756481417515728569)
      ·
        refine ⟨3272234067361063136796427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362978756481417515728569 3272234067361063136796427)
        ·
          refine ⟨4908351101041594705194641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272234067361063136796427 4908351101041594705194641)
          ·
            refine ⟨3681263325781196028895981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4908351101041594705194641 3681263325781196028895981)
            ·
              refine ⟨1380473747167948510835993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3681263325781196028895981 1380473747167948510835993)
              ·
                refine ⟨1035355310375961383126995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380473747167948510835993 1035355310375961383126995)
                ·
                  refine ⟨1553032965563942074690493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035355310375961383126995 1553032965563942074690493)
                  ·
                    refine ⟨582387362086478278008935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553032965563942074690493 582387362086478278008935)
                    ·
                      rfl

theorem cell22_1701293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_1701293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701293 prefixEnd_1701293 := by exact prefixLift 1701293
  have htrace : WordTrace (prefixWord ++ tailWord_1701293) baseStart_1701293 baseEnd_1701293 := by
    simpa [prefixWord, tailWord_1701293, baseEnd_1701293] using wordTrace_append hprefix tailTrace_1701293
  have hstable : (prefixWord ++ tailWord_1701293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701293).length < 2 ^ (prefixWord ++ tailWord_1701293).sum := by decide
  have hdescent : baseEnd_1701293 < baseStart_1701293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701347 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_1701347 : Nat := 118140960795 + 1701347 * 2 ^ 59
def prefixEnd_1701347 : Nat := 4983230072969 + 3 ^ 40 * 1701347 * 2
def baseEnd_1701347 : Nat := 582405847390040137158769

theorem tailTrace_1701347 : CollatzResearch.WordTrace tailWord_1701347 prefixEnd_1701347 582405847390040137158769 := by
  unfold tailWord_1701347
  simp only [CollatzResearch.WordTrace]
  refine ⟨62053222967317860779494295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41368815311545240519662863 62053222967317860779494295)
  ·
    refine ⟨93079834450976791169241443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62053222967317860779494295 93079834450976791169241443)
    ·
      refine ⟨139619751676465186753862165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93079834450976791169241443 139619751676465186753862165)
      ·
        refine ⟨6544675859834305629087289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139619751676465186753862165 6544675859834305629087289)
        ·
          refine ⟨4908506894875729221815467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6544675859834305629087289 4908506894875729221815467)
          ·
            refine ⟨7362760342313593832723201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908506894875729221815467 7362760342313593832723201)
            ·
              refine ⟨5522070256735195374542401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7362760342313593832723201 5522070256735195374542401)
              ·
                refine ⟨4141552692551396530906801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522070256735195374542401 4141552692551396530906801)
                ·
                  refine ⟨3106164519413547398180101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4141552692551396530906801 3106164519413547398180101)
                  ·
                    refine ⟨582405847390040137158769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3106164519413547398180101 582405847390040137158769)
                    ·
                      rfl

theorem cell22_1701347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_1701347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701347 prefixEnd_1701347 := by exact prefixLift 1701347
  have htrace : WordTrace (prefixWord ++ tailWord_1701347) baseStart_1701347 baseEnd_1701347 := by
    simpa [prefixWord, tailWord_1701347, baseEnd_1701347] using wordTrace_append hprefix tailTrace_1701347
  have hstable : (prefixWord ++ tailWord_1701347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701347).length < 2 ^ (prefixWord ++ tailWord_1701347).sum := by decide
  have hdescent : baseEnd_1701347 < baseStart_1701347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701349 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_1701349 : Nat := 118140960795 + 1701349 * 2 ^ 59
def prefixEnd_1701349 : Nat := 4983230072969 + 3 ^ 40 * 1701349 * 2
def baseEnd_1701349 : Nat := 582406532030912798608763

theorem tailTrace_1701349 : CollatzResearch.WordTrace tailWord_1701349 prefixEnd_1701349 582406532030912798608763 := by
  unfold tailWord_1701349
  simp only [CollatzResearch.WordTrace]
  refine ⟨62053295913310615121067101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41368863942207076747378067 62053295913310615121067101)
  ·
    refine ⟨23269985967491480670400163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62053295913310615121067101 23269985967491480670400163)
    ·
      refine ⟨34904978951237221005600245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23269985967491480670400163 34904978951237221005600245)
      ·
        refine ⟨3272341776678489469275023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34904978951237221005600245 3272341776678489469275023)
        ·
          refine ⟨4908512665017734203912535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272341776678489469275023 4908512665017734203912535)
          ·
            refine ⟨7362768997526601305868803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908512665017734203912535 7362768997526601305868803)
            ·
              refine ⟨11044153496289901958803205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362768997526601305868803 11044153496289901958803205)
              ·
                refine ⟨2070778780554356617275601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11044153496289901958803205 2070778780554356617275601)
                ·
                  refine ⟨1553084085415767462956701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2070778780554356617275601 1553084085415767462956701)
                  ·
                    refine ⟨582406532030912798608763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553084085415767462956701 582406532030912798608763)
                    ·
                      rfl

theorem cell22_1701349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_1701349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701349 prefixEnd_1701349 := by exact prefixLift 1701349
  have htrace : WordTrace (prefixWord ++ tailWord_1701349) baseStart_1701349 baseEnd_1701349 := by
    simpa [prefixWord, tailWord_1701349, baseEnd_1701349] using wordTrace_append hprefix tailTrace_1701349
  have hstable : (prefixWord ++ tailWord_1701349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701349).length < 2 ^ (prefixWord ++ tailWord_1701349).sum := by decide
  have hdescent : baseEnd_1701349 < baseStart_1701349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701351 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 4]
def baseStart_1701351 : Nat := 118140960795 + 1701351 * 2 ^ 59
def prefixEnd_1701351 : Nat := 4983230072969 + 3 ^ 40 * 1701351 * 2
def baseEnd_1701351 : Nat := 194135738890595153352919

theorem tailTrace_1701351 : CollatzResearch.WordTrace tailWord_1701351 prefixEnd_1701351 194135738890595153352919 := by
  unfold tailWord_1701351
  simp only [CollatzResearch.WordTrace]
  refine ⟨62053368859303369462639907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41368912572868912975093271 62053368859303369462639907)
  ·
    refine ⟨93080053288955054193959861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62053368859303369462639907 93080053288955054193959861)
    ·
      refine ⟨8726254995839536330683737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93080053288955054193959861 8726254995839536330683737)
      ·
        refine ⟨6544691246879652248012803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726254995839536330683737 6544691246879652248012803)
        ·
          refine ⟨9817036870319478372019205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544691246879652248012803 9817036870319478372019205)
          ·
            refine ⟨1840694413184902194753601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9817036870319478372019205 1840694413184902194753601)
            ·
              refine ⟨1380520809888676646065201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840694413184902194753601 1380520809888676646065201)
              ·
                refine ⟨1035390607416507484548901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380520809888676646065201 1035390607416507484548901)
                ·
                  refine ⟨194135738890595153352919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1035390607416507484548901 194135738890595153352919)
                  ·
                    rfl

theorem cell22_1701351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 4].length) (baseStart_1701351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701351 prefixEnd_1701351 := by exact prefixLift 1701351
  have htrace : WordTrace (prefixWord ++ tailWord_1701351) baseStart_1701351 baseEnd_1701351 := by
    simpa [prefixWord, tailWord_1701351, baseEnd_1701351] using wordTrace_append hprefix tailTrace_1701351
  have hstable : (prefixWord ++ tailWord_1701351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701351).length < 2 ^ (prefixWord ++ tailWord_1701351).sum := by decide
  have hdescent : baseEnd_1701351 < baseStart_1701351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701362 : List Nat := [3, 2, 1, 4, 1, 1, 3, 7]
def baseStart_1701362 : Nat := 118140960795 + 1701362 * 2 ^ 59
def prefixEnd_1701362 : Nat := 4983230072969 + 3 ^ 40 * 1701362 * 2
def baseEnd_1701362 : Nat := 64712331355176122003747

theorem tailTrace_1701362 : CollatzResearch.WordTrace tailWord_1701362 prefixEnd_1701362 64712331355176122003747 := by
  unfold tailWord_1701362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15513442515565879585322585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41369180041509012227526893 15513442515565879585322585)
  ·
    refine ⟨11635081886674409688991939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15513442515565879585322585 11635081886674409688991939)
    ·
      refine ⟨17452622830011614533487909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11635081886674409688991939 17452622830011614533487909)
      ·
        refine ⟨3272366780627177725028983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17452622830011614533487909 3272366780627177725028983)
        ·
          refine ⟨4908550170940766587543475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272366780627177725028983 4908550170940766587543475)
          ·
            refine ⟨7362825256411149881315213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908550170940766587543475 7362825256411149881315213)
            ·
              refine ⟨2761059471154181205493205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7362825256411149881315213 2761059471154181205493205)
              ·
                refine ⟨64712331355176122003747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2761059471154181205493205 64712331355176122003747)
                ·
                  rfl

theorem cell22_1701362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_1701362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701362 prefixEnd_1701362 := by exact prefixLift 1701362
  have htrace : WordTrace (prefixWord ++ tailWord_1701362) baseStart_1701362 baseEnd_1701362 := by
    simpa [prefixWord, tailWord_1701362, baseEnd_1701362] using wordTrace_append hprefix tailTrace_1701362
  have hstable : (prefixWord ++ tailWord_1701362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701362).length < 2 ^ (prefixWord ++ tailWord_1701362).sum := by decide
  have hdescent : baseEnd_1701362 < baseStart_1701362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701407 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 5]
def baseStart_1701407 : Nat := 118140960795 + 1701407 * 2 ^ 59
def prefixEnd_1701407 : Nat := 4983230072969 + 3 ^ 40 * 1701407 * 2
def baseEnd_1701407 : Nat := 194142128872073326886195

theorem tailTrace_1701407 : CollatzResearch.WordTrace tailWord_1701407 prefixEnd_1701407 194142128872073326886195 := by
  unfold tailWord_1701407
  simp only [CollatzResearch.WordTrace]
  refine ⟨62055411347100491026678475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41370274231400327351118983 62055411347100491026678475)
  ·
    refine ⟨93083117020650736540017713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62055411347100491026678475 93083117020650736540017713)
    ·
      refine ⟨69812337765488052405013285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93083117020650736540017713 69812337765488052405013285)
      ·
        refine ⟨13089813331029009825939991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69812337765488052405013285 13089813331029009825939991)
        ·
          refine ⟨19634719996543514738909987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089813331029009825939991 19634719996543514738909987)
          ·
            refine ⟨29452079994815272108364981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19634719996543514738909987 29452079994815272108364981)
            ·
              refine ⟨2761132499513931760159217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29452079994815272108364981 2761132499513931760159217)
              ·
                refine ⟨2070849374635448820119413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2761132499513931760159217 2070849374635448820119413)
                ·
                  refine ⟨194142128872073326886195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2070849374635448820119413 194142128872073326886195)
                  ·
                    rfl

theorem cell22_1701407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 5].length) (baseStart_1701407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701407 prefixEnd_1701407 := by exact prefixLift 1701407
  have htrace : WordTrace (prefixWord ++ tailWord_1701407) baseStart_1701407 baseEnd_1701407 := by
    simpa [prefixWord, tailWord_1701407, baseEnd_1701407] using wordTrace_append hprefix tailTrace_1701407
  have hstable : (prefixWord ++ tailWord_1701407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701407).length < 2 ^ (prefixWord ++ tailWord_1701407).sum := by decide
  have hdescent : baseEnd_1701407 < baseStart_1701407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701462 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1701462 : Nat := 118140960795 + 1701462 * 2 ^ 59
def prefixEnd_1701462 : Nat := 4983230072969 + 3 ^ 40 * 1701462 * 2
def baseEnd_1701462 : Nat := 582445214240218170533417

theorem tailTrace_1701462 : CollatzResearch.WordTrace tailWord_1701462 prefixEnd_1701462 582445214240218170533417 := by
  unfold tailWord_1701462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878588585118827213745665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41371611574600823613287093 3878588585118827213745665)
  ·
    refine ⟨2908941438839120410309249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3878588585118827213745665 2908941438839120410309249)
    ·
      refine ⟨2181706079129340307731937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2908941438839120410309249 2181706079129340307731937)
      ·
        refine ⟨1636279559347005230798953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2181706079129340307731937 1636279559347005230798953)
        ·
          refine ⟨1227209669510253923099215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1636279559347005230798953 1227209669510253923099215)
          ·
            refine ⟨1840814504265380884648823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227209669510253923099215 1840814504265380884648823)
            ·
              refine ⟨2761221756398071326973235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840814504265380884648823 2761221756398071326973235)
              ·
                refine ⟨4141832634597106990459853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761221756398071326973235 4141832634597106990459853)
                ·
                  refine ⟨1553187237973915121422445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4141832634597106990459853 1553187237973915121422445)
                  ·
                    refine ⟨582445214240218170533417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553187237973915121422445 582445214240218170533417)
                    ·
                      rfl

theorem cell22_1701462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1701462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701462 prefixEnd_1701462 := by exact prefixLift 1701462
  have htrace : WordTrace (prefixWord ++ tailWord_1701462) baseStart_1701462 baseEnd_1701462 := by
    simpa [prefixWord, tailWord_1701462, baseEnd_1701462] using wordTrace_append hprefix tailTrace_1701462
  have hstable : (prefixWord ++ tailWord_1701462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701462).length < 2 ^ (prefixWord ++ tailWord_1701462).sum := by decide
  have hdescent : baseEnd_1701462 < baseStart_1701462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701527 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1701527 : Nat := 118140960795 + 1701527 * 2 ^ 59
def prefixEnd_1701527 : Nat := 4983230072969 + 3 ^ 40 * 1701527 * 2
def baseEnd_1701527 : Nat := 582467465068579667658217

theorem tailTrace_1701527 : CollatzResearch.WordTrace tailWord_1701527 prefixEnd_1701527 582467465068579667658217 := by
  unfold tailWord_1701527
  simp only [CollatzResearch.WordTrace]
  refine ⟨62059788106665751521046835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41373192071110501014031223 62059788106665751521046835)
  ·
    refine ⟨93089682159998627281570253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62059788106665751521046835 93089682159998627281570253)
    ·
      refine ⟨34908630809999485230588845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93089682159998627281570253 34908630809999485230588845)
      ·
        refine ⟨13090736553749806961470817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34908630809999485230588845 13090736553749806961470817)
        ·
          refine ⟨9818052415312355221103113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13090736553749806961470817 9818052415312355221103113)
          ·
            refine ⟨7363539311484266415827335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818052415312355221103113 7363539311484266415827335)
            ·
              refine ⟨11045308967226399623741003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363539311484266415827335 11045308967226399623741003)
              ·
                refine ⟨16567963450839599435611505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045308967226399623741003 16567963450839599435611505)
                ·
                  refine ⟨12425972588129699576708629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16567963450839599435611505 12425972588129699576708629)
                  ·
                    refine ⟨582467465068579667658217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12425972588129699576708629 582467465068579667658217)
                    ·
                      rfl

theorem cell22_1701527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1701527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701527 prefixEnd_1701527 := by exact prefixLift 1701527
  have htrace : WordTrace (prefixWord ++ tailWord_1701527) baseStart_1701527 baseEnd_1701527 := by
    simpa [prefixWord, tailWord_1701527, baseEnd_1701527] using wordTrace_append hprefix tailTrace_1701527
  have hstable : (prefixWord ++ tailWord_1701527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701527).length < 2 ^ (prefixWord ++ tailWord_1701527).sum := by decide
  have hdescent : baseEnd_1701527 < baseStart_1701527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701550 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1701550 : Nat := 118140960795 + 1701550 * 2 ^ 59
def prefixEnd_1701550 : Nat := 4983230072969 + 3 ^ 40 * 1701550 * 2
def baseEnd_1701550 : Nat := 582475338438615274333147

theorem tailTrace_1701550 : CollatzResearch.WordTrace tailWord_1701550 prefixEnd_1701550 582475338438615274333147 := by
  unfold tailWord_1701550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7757578373197803306141763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41373751323721617632756069 7757578373197803306141763)
  ·
    refine ⟨11636367559796704959212645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7757578373197803306141763 11636367559796704959212645)
    ·
      refine ⟨2181818917461882179852371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11636367559796704959212645 2181818917461882179852371)
      ·
        refine ⟨3272728376192823269778557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181818917461882179852371 3272728376192823269778557)
        ·
          refine ⟨1227273141072308726166959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3272728376192823269778557 1227273141072308726166959)
          ·
            refine ⟨1840909711608463089250439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227273141072308726166959 1840909711608463089250439)
            ·
              refine ⟨2761364567412694633875659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840909711608463089250439 2761364567412694633875659)
              ·
                refine ⟨4142046851119041950813489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761364567412694633875659 4142046851119041950813489)
                ·
                  refine ⟨3106535138339281463110117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142046851119041950813489 3106535138339281463110117)
                  ·
                    refine ⟨582475338438615274333147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3106535138339281463110117 582475338438615274333147)
                    ·
                      rfl

theorem cell22_1701550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1701550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701550 prefixEnd_1701550 := by exact prefixLift 1701550
  have htrace : WordTrace (prefixWord ++ tailWord_1701550) baseStart_1701550 baseEnd_1701550 := by
    simpa [prefixWord, tailWord_1701550, baseEnd_1701550] using wordTrace_append hprefix tailTrace_1701550
  have hstable : (prefixWord ++ tailWord_1701550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701550).length < 2 ^ (prefixWord ++ tailWord_1701550).sum := by decide
  have hdescent : baseEnd_1701550 < baseStart_1701550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701619 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 4, 3]
def baseStart_1701619 : Nat := 118140960795 + 1701619 * 2 ^ 59
def prefixEnd_1701619 : Nat := 4983230072969 + 3 ^ 40 * 1701619 * 2
def baseEnd_1701619 : Nat := 582498958548722094357935

theorem tailTrace_1701619 : CollatzResearch.WordTrace tailWord_1701619 prefixEnd_1701619 582498958548722094357935 := by
  unfold tailWord_1701619
  simp only [CollatzResearch.WordTrace]
  refine ⟨62063143622332451233395911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41375429081554967488930607 62063143622332451233395911)
  ·
    refine ⟨93094715433498676850093867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62063143622332451233395911 93094715433498676850093867)
    ·
      refine ⟨139642073150248015275140801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93094715433498676850093867 139642073150248015275140801)
      ·
        refine ⟨104731554862686011456355601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139642073150248015275140801 104731554862686011456355601)
        ·
          refine ⟨78548666147014508592266701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104731554862686011456355601 78548666147014508592266701)
          ·
            refine ⟨29455749805130440722100013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78548666147014508592266701 29455749805130440722100013)
            ·
              refine ⟨11045906176923915270787505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29455749805130440722100013 11045906176923915270787505)
              ·
                refine ⟨8284429632692936453090629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045906176923915270787505 8284429632692936453090629)
                ·
                  refine ⟨1553330556129925584954493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8284429632692936453090629 1553330556129925584954493)
                  ·
                    refine ⟨582498958548722094357935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553330556129925584954493 582498958548722094357935)
                    ·
                      rfl

theorem cell22_1701619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3].length) (baseStart_1701619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701619 prefixEnd_1701619 := by exact prefixLift 1701619
  have htrace : WordTrace (prefixWord ++ tailWord_1701619) baseStart_1701619 baseEnd_1701619 := by
    simpa [prefixWord, tailWord_1701619, baseEnd_1701619] using wordTrace_append hprefix tailTrace_1701619
  have hstable : (prefixWord ++ tailWord_1701619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701619).length < 2 ^ (prefixWord ++ tailWord_1701619).sum := by decide
  have hdescent : baseEnd_1701619 < baseStart_1701619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701636 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1701636 : Nat := 118140960795 + 1701636 * 2 ^ 59
def prefixEnd_1701636 : Nat := 4983230072969 + 3 ^ 40 * 1701636 * 2
def baseEnd_1701636 : Nat := 582504777996139716682883

theorem tailTrace_1701636 : CollatzResearch.WordTrace tailWord_1701636 prefixEnd_1701636 582504777996139716682883 := by
  unfold tailWord_1701636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031881831635431568382381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41375842442180575424509841 31031881831635431568382381)
  ·
    refine ⟨11636955686863286838143393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31031881831635431568382381 11636955686863286838143393)
    ·
      refine ⟨8727716765147465128607545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11636955686863286838143393 8727716765147465128607545)
      ·
        refine ⟨6545787573860598846455659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8727716765147465128607545 6545787573860598846455659)
        ·
          refine ⟨9818681360790898269683489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545787573860598846455659 9818681360790898269683489)
          ·
            refine ⟨7364011020593173702262617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818681360790898269683489 7364011020593173702262617)
            ·
              refine ⟨5523008265444880276696963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364011020593173702262617 5523008265444880276696963)
              ·
                refine ⟨8284512398167320415045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523008265444880276696963 8284512398167320415045445)
                ·
                  refine ⟨1553346074656372577821021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8284512398167320415045445 1553346074656372577821021)
                  ·
                    refine ⟨582504777996139716682883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553346074656372577821021 582504777996139716682883)
                    ·
                      rfl

theorem cell22_1701636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1701636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701636 prefixEnd_1701636 := by exact prefixLift 1701636
  have htrace : WordTrace (prefixWord ++ tailWord_1701636) baseStart_1701636 baseEnd_1701636 := by
    simpa [prefixWord, tailWord_1701636, baseEnd_1701636] using wordTrace_append hprefix tailTrace_1701636
  have hstable : (prefixWord ++ tailWord_1701636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701636).length < 2 ^ (prefixWord ++ tailWord_1701636).sum := by decide
  have hdescent : baseEnd_1701636 < baseStart_1701636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1701647 : Nat := 118140960795 + 1701647 * 2 ^ 59
def prefixEnd_1701647 : Nat := 4983230072969 + 3 ^ 40 * 1701647 * 2
def baseEnd_1701647 : Nat := 582508543520939354657849

theorem tailTrace_1701647 : CollatzResearch.WordTrace tailWord_1701647 prefixEnd_1701647 582508543520939354657849 := by
  unfold tailWord_1701647
  simp only [CollatzResearch.WordTrace]
  refine ⟨62064164866231012015415195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41376109910820674676943463 62064164866231012015415195)
  ·
    refine ⟨93096247299346518023122793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62064164866231012015415195 93096247299346518023122793)
    ·
      refine ⟨69822185474509888517342095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93096247299346518023122793 69822185474509888517342095)
      ·
        refine ⟨104733278211764832776013143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69822185474509888517342095 104733278211764832776013143)
        ·
          refine ⟨157099917317647249164019715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104733278211764832776013143 157099917317647249164019715)
          ·
            refine ⟨235649875976470873746029573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157099917317647249164019715 235649875976470873746029573)
            ·
              refine ⟨44184351745588288827380545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235649875976470873746029573 44184351745588288827380545)
              ·
                refine ⟨33138263809191216620535409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44184351745588288827380545 33138263809191216620535409)
                ·
                  refine ⟨24853697856893412465401557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33138263809191216620535409 24853697856893412465401557)
                  ·
                    refine ⟨582508543520939354657849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24853697856893412465401557 582508543520939354657849)
                    ·
                      rfl

theorem cell22_1701647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1701647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701647 prefixEnd_1701647 := by exact prefixLift 1701647
  have htrace : WordTrace (prefixWord ++ tailWord_1701647) baseStart_1701647 baseEnd_1701647 := by
    simpa [prefixWord, tailWord_1701647, baseEnd_1701647] using wordTrace_append hprefix tailTrace_1701647
  have hstable : (prefixWord ++ tailWord_1701647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701647).length < 2 ^ (prefixWord ++ tailWord_1701647).sum := by decide
  have hdescent : baseEnd_1701647 < baseStart_1701647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701653 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1701653 : Nat := 118140960795 + 1701653 * 2 ^ 59
def prefixEnd_1701653 : Nat := 4983230072969 + 3 ^ 40 * 1701653 * 2
def baseEnd_1701653 : Nat := 582510597443557339007831

theorem tailTrace_1701653 : CollatzResearch.WordTrace tailWord_1701653 prefixEnd_1701653 582510597443557339007831 := by
  unfold tailWord_1701653
  simp only [CollatzResearch.WordTrace]
  refine ⟨62064383704209275040133613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41376255802806183360089075 62064383704209275040133613)
  ·
    refine ⟨23274143889078478140050105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62064383704209275040133613 23274143889078478140050105)
    ·
      refine ⟨17455607916808858605037579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23274143889078478140050105 17455607916808858605037579)
      ·
        refine ⟨26183411875213287907556369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17455607916808858605037579 26183411875213287907556369)
        ·
          refine ⟨19637558906409965930667277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26183411875213287907556369 19637558906409965930667277)
          ·
            refine ⟨7364084589903737224000229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19637558906409965930667277 7364084589903737224000229)
            ·
              refine ⟨1380765860606950729500043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7364084589903737224000229 1380765860606950729500043)
              ·
                refine ⟨2071148790910426094250065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380765860606950729500043 2071148790910426094250065)
                ·
                  refine ⟨1553361593182819570687549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071148790910426094250065 1553361593182819570687549)
                  ·
                    refine ⟨582510597443557339007831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553361593182819570687549 582510597443557339007831)
                    ·
                      rfl

theorem cell22_1701653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1701653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701653 prefixEnd_1701653 := by exact prefixLift 1701653
  have htrace : WordTrace (prefixWord ++ tailWord_1701653) baseStart_1701653 baseEnd_1701653 := by
    simpa [prefixWord, tailWord_1701653, baseEnd_1701653] using wordTrace_append hprefix tailTrace_1701653
  have hstable : (prefixWord ++ tailWord_1701653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701653).length < 2 ^ (prefixWord ++ tailWord_1701653).sum := by decide
  have hdescent : baseEnd_1701653 < baseStart_1701653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701754 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1701754 : Nat := 118140960795 + 1701754 * 2 ^ 59
def prefixEnd_1701754 : Nat := 4983230072969 + 3 ^ 40 * 1701754 * 2
def baseEnd_1701754 : Nat := 582545171807626742232521

theorem tailTrace_1701754 : CollatzResearch.WordTrace tailWord_1701754 prefixEnd_1701754 582545171807626742232521 := by
  unfold tailWord_1701754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517016869210842322390079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41378711651228912859706877 15517016869210842322390079)
  ·
    refine ⟨23275525303816263483585119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517016869210842322390079 23275525303816263483585119)
    ·
      refine ⟨34913287955724395225377679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275525303816263483585119 34913287955724395225377679)
      ·
        refine ⟨52369931933586592838066519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34913287955724395225377679 52369931933586592838066519)
        ·
          refine ⟨78554897900379889257099779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52369931933586592838066519 78554897900379889257099779)
          ·
            refine ⟨117832346850569833885649669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78554897900379889257099779 117832346850569833885649669)
            ·
              refine ⟨22093565034481843853559313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117832346850569833885649669 22093565034481843853559313)
              ·
                refine ⟨16570173775861382890169485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22093565034481843853559313 16570173775861382890169485)
                ·
                  refine ⟨6213815165948018583813557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16570173775861382890169485 6213815165948018583813557)
                  ·
                    refine ⟨582545171807626742232521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6213815165948018583813557 582545171807626742232521)
                    ·
                      rfl

theorem cell22_1701754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1701754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701754 prefixEnd_1701754 := by exact prefixLift 1701754
  have htrace : WordTrace (prefixWord ++ tailWord_1701754) baseStart_1701754 baseEnd_1701754 := by
    simpa [prefixWord, tailWord_1701754, baseEnd_1701754] using wordTrace_append hprefix tailTrace_1701754
  have hstable : (prefixWord ++ tailWord_1701754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701754).length < 2 ^ (prefixWord ++ tailWord_1701754).sum := by decide
  have hdescent : baseEnd_1701754 < baseStart_1701754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701769 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1701769 : Nat := 118140960795 + 1701769 * 2 ^ 59
def prefixEnd_1701769 : Nat := 4983230072969 + 3 ^ 40 * 1701769 * 2
def baseEnd_1701769 : Nat := 582550306614171703107475

theorem tailTrace_1701769 : CollatzResearch.WordTrace tailWord_1701769 prefixEnd_1701769 582550306614171703107475 := by
  unfold tailWord_1701769
  simp only [CollatzResearch.WordTrace]
  refine ⟨62068614571789026851356361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41379076381192684567570907 62068614571789026851356361)
  ·
    refine ⟨46551460928841770138517271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62068614571789026851356361 46551460928841770138517271)
    ·
      refine ⟨69827191393262655207775907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46551460928841770138517271 69827191393262655207775907)
      ·
        refine ⟨104740787089893982811663861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69827191393262655207775907 104740787089893982811663861)
        ·
          refine ⟨9819448789677560888593487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104740787089893982811663861 9819448789677560888593487)
          ·
            refine ⟨14729173184516341332890231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819448789677560888593487 14729173184516341332890231)
            ·
              refine ⟨22093759776774511999335347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729173184516341332890231 22093759776774511999335347)
              ·
                refine ⟨33140639665161767999003021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22093759776774511999335347 33140639665161767999003021)
                ·
                  refine ⟨12427739874435662999626133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33140639665161767999003021 12427739874435662999626133)
                  ·
                    refine ⟨582550306614171703107475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12427739874435662999626133 582550306614171703107475)
                    ·
                      rfl

theorem cell22_1701769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1701769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701769 prefixEnd_1701769 := by exact prefixLift 1701769
  have htrace : WordTrace (prefixWord ++ tailWord_1701769) baseStart_1701769 baseEnd_1701769 := by
    simpa [prefixWord, tailWord_1701769, baseEnd_1701769] using wordTrace_append hprefix tailTrace_1701769
  have hstable : (prefixWord ++ tailWord_1701769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701769).length < 2 ^ (prefixWord ++ tailWord_1701769).sum := by decide
  have hdescent : baseEnd_1701769 < baseStart_1701769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701786 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1701786 : Nat := 118140960795 + 1701786 * 2 ^ 59
def prefixEnd_1701786 : Nat := 4983230072969 + 3 ^ 40 * 1701786 * 2
def baseEnd_1701786 : Nat := 582556126061589325432423

theorem tailTrace_1701786 : CollatzResearch.WordTrace tailWord_1701786 prefixEnd_1701786 582556126061589325432423 := by
  unfold tailWord_1701786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517308653181859688681303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41379489741818292503150141 15517308653181859688681303)
  ·
    refine ⟨23275962979772789533021955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517308653181859688681303 23275962979772789533021955)
    ·
      refine ⟨34913944469659184299532933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275962979772789533021955 34913944469659184299532933)
      ·
        refine ⟨6546364588061097056162425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34913944469659184299532933 6546364588061097056162425)
        ·
          refine ⟨4909773441045822792121819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6546364588061097056162425 4909773441045822792121819)
          ·
            refine ⟨7364660161568734188182729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909773441045822792121819 7364660161568734188182729)
            ·
              refine ⟨5523495121176550641137047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364660161568734188182729 5523495121176550641137047)
              ·
                refine ⟨8285242681764825961705571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523495121176550641137047 8285242681764825961705571)
                ·
                  refine ⟨12427864022647238942558357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285242681764825961705571 12427864022647238942558357)
                  ·
                    refine ⟨582556126061589325432423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12427864022647238942558357 582556126061589325432423)
                    ·
                      rfl

theorem cell22_1701786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1701786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701786 prefixEnd_1701786 := by exact prefixLift 1701786
  have htrace : WordTrace (prefixWord ++ tailWord_1701786) baseStart_1701786 baseEnd_1701786 := by
    simpa [prefixWord, tailWord_1701786, baseEnd_1701786] using wordTrace_append hprefix tailTrace_1701786
  have hstable : (prefixWord ++ tailWord_1701786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701786).length < 2 ^ (prefixWord ++ tailWord_1701786).sum := by decide
  have hdescent : baseEnd_1701786 < baseStart_1701786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701788 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1701788 : Nat := 118140960795 + 1701788 * 2 ^ 59
def prefixEnd_1701788 : Nat := 4983230072969 + 3 ^ 40 * 1701788 * 2
def baseEnd_1701788 : Nat := 582556810702461986882417

theorem tailTrace_1701788 : CollatzResearch.WordTrace tailWord_1701788 prefixEnd_1701788 582556810702461986882417 := by
  unfold tailWord_1701788
  simp only [CollatzResearch.WordTrace]
  refine ⟨31034653779360096548149009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41379538372480128730865345 31034653779360096548149009)
  ·
    refine ⟨23275990334520072411111757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31034653779360096548149009 23275990334520072411111757)
    ·
      refine ⟨8728496375445027154166909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23275990334520072411111757 8728496375445027154166909)
      ·
        refine ⟨3273186140791885182812591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8728496375445027154166909 3273186140791885182812591)
        ·
          refine ⟨4909779211187827774218887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273186140791885182812591 4909779211187827774218887)
          ·
            refine ⟨7364668816781741661328331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909779211187827774218887 7364668816781741661328331)
            ·
              refine ⟨11047003225172612491992497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364668816781741661328331 11047003225172612491992497)
              ·
                refine ⟨8285252418879459368994373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11047003225172612491992497 8285252418879459368994373)
                ·
                  refine ⟨1553484828539898631686445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8285252418879459368994373 1553484828539898631686445)
                  ·
                    refine ⟨582556810702461986882417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553484828539898631686445 582556810702461986882417)
                    ·
                      rfl

theorem cell22_1701788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1701788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701788 prefixEnd_1701788 := by exact prefixLift 1701788
  have htrace : WordTrace (prefixWord ++ tailWord_1701788) baseStart_1701788 baseEnd_1701788 := by
    simpa [prefixWord, tailWord_1701788, baseEnd_1701788] using wordTrace_append hprefix tailTrace_1701788
  have hstable : (prefixWord ++ tailWord_1701788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701788).length < 2 ^ (prefixWord ++ tailWord_1701788).sum := by decide
  have hdescent : baseEnd_1701788 < baseStart_1701788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701822 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1701822 : Nat := 118140960795 + 1701822 * 2 ^ 59
def prefixEnd_1701822 : Nat := 4983230072969 + 3 ^ 40 * 1701822 * 2
def baseEnd_1701822 : Nat := 582568449597297231532313

theorem tailTrace_1701822 : CollatzResearch.WordTrace tailWord_1701822 prefixEnd_1701822 582568449597297231532313 := by
  unfold tailWord_1701822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758818455074627112879465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41380365093731344602023813 7758818455074627112879465)
  ·
    refine ⟨5819113841305970334659599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7758818455074627112879465 5819113841305970334659599)
    ·
      refine ⟨8728670761958955501989399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819113841305970334659599 8728670761958955501989399)
      ·
        refine ⟨13093006142938433252984099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728670761958955501989399 13093006142938433252984099)
        ·
          refine ⟨19639509214407649879476149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13093006142938433252984099 19639509214407649879476149)
          ·
            refine ⟨1841203988850717176200889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19639509214407649879476149 1841203988850717176200889)
            ·
              refine ⟨1380902991638037882150667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841203988850717176200889 1380902991638037882150667)
              ·
                refine ⟨2071354487457056823226001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380902991638037882150667 2071354487457056823226001)
                ·
                  refine ⟨1553515865592792617419501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071354487457056823226001 1553515865592792617419501)
                  ·
                    refine ⟨582568449597297231532313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553515865592792617419501 582568449597297231532313)
                    ·
                      rfl

theorem cell22_1701822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1701822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701822 prefixEnd_1701822 := by exact prefixLift 1701822
  have htrace : WordTrace (prefixWord ++ tailWord_1701822) baseStart_1701822 baseEnd_1701822 := by
    simpa [prefixWord, tailWord_1701822, baseEnd_1701822] using wordTrace_append hprefix tailTrace_1701822
  have hstable : (prefixWord ++ tailWord_1701822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701822).length < 2 ^ (prefixWord ++ tailWord_1701822).sum := by decide
  have hdescent : baseEnd_1701822 < baseStart_1701822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701829 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1701829 : Nat := 118140960795 + 1701829 * 2 ^ 59
def prefixEnd_1701829 : Nat := 4983230072969 + 3 ^ 40 * 1701829 * 2
def baseEnd_1701829 : Nat := 194190281946783848869097

theorem tailTrace_1701829 : CollatzResearch.WordTrace tailWord_1701829 prefixEnd_1701829 194190281946783848869097 := by
  unfold tailWord_1701829
  simp only [CollatzResearch.WordTrace]
  refine ⟨62070802951571657098540541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41380535301047771399027027 62070802951571657098540541)
  ·
    refine ⟨23276551106839371411952703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62070802951571657098540541 23276551106839371411952703)
    ·
      refine ⟨34914826660259057117929055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23276551106839371411952703 34914826660259057117929055)
      ·
        refine ⟨52372239990388585676893583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34914826660259057117929055 52372239990388585676893583)
        ·
          refine ⟨78558359985582878515340375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52372239990388585676893583 78558359985582878515340375)
          ·
            refine ⟨117837539978374317773010563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78558359985582878515340375 117837539978374317773010563)
            ·
              refine ⟨176756309967561476659515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117837539978374317773010563 176756309967561476659515845)
              ·
                refine ⟨33141808118917776873659221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176756309967561476659515845 33141808118917776873659221)
                ·
                  refine ⟨194190281946783848869097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33141808118917776873659221 194190281946783848869097)
                  ·
                    rfl

theorem cell22_1701829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1701829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701829 prefixEnd_1701829 := by exact prefixLift 1701829
  have htrace : WordTrace (prefixWord ++ tailWord_1701829) baseStart_1701829 baseEnd_1701829 := by
    simpa [prefixWord, tailWord_1701829, baseEnd_1701829] using wordTrace_append hprefix tailTrace_1701829
  have hstable : (prefixWord ++ tailWord_1701829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701829).length < 2 ^ (prefixWord ++ tailWord_1701829).sum := by decide
  have hdescent : baseEnd_1701829 < baseStart_1701829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701923 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 4, 3]
def baseStart_1701923 : Nat := 118140960795 + 1701923 * 2 ^ 59
def prefixEnd_1701923 : Nat := 4983230072969 + 3 ^ 40 * 1701923 * 2
def baseEnd_1701923 : Nat := 582603023961366634757003

theorem tailTrace_1701923 : CollatzResearch.WordTrace tailWord_1701923 prefixEnd_1701923 582603023961366634757003 := by
  unfold tailWord_1701923
  simp only [CollatzResearch.WordTrace]
  refine ⟨62074231413231111152462423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41382820942154074101641615 62074231413231111152462423)
  ·
    refine ⟨93111347119846666728693635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62074231413231111152462423 93111347119846666728693635)
    ·
      refine ⟨139667020679770000093040453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93111347119846666728693635 139667020679770000093040453)
      ·
        refine ⟨26187566377456875017445085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139667020679770000093040453 26187566377456875017445085)
        ·
          refine ⟨9820337391546328131541907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26187566377456875017445085 9820337391546328131541907)
          ·
            refine ⟨14730506087319492197312861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820337391546328131541907 14730506087319492197312861)
            ·
              refine ⟨5523939782744809573992323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14730506087319492197312861 5523939782744809573992323)
              ·
                refine ⟨8285909674117214360988485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523939782744809573992323 8285909674117214360988485)
                ·
                  refine ⟨1553608063896977692685341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8285909674117214360988485 1553608063896977692685341)
                  ·
                    refine ⟨582603023961366634757003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553608063896977692685341 582603023961366634757003)
                    ·
                      rfl

theorem cell22_1701923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3].length) (baseStart_1701923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701923 prefixEnd_1701923 := by exact prefixLift 1701923
  have htrace : WordTrace (prefixWord ++ tailWord_1701923) baseStart_1701923 baseEnd_1701923 := by
    simpa [prefixWord, tailWord_1701923, baseEnd_1701923] using wordTrace_append hprefix tailTrace_1701923
  have hstable : (prefixWord ++ tailWord_1701923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701923).length < 2 ^ (prefixWord ++ tailWord_1701923).sum := by decide
  have hdescent : baseEnd_1701923 < baseStart_1701923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701953 : List Nat := [1, 2, 5, 1, 2, 2, 1, 8]
def baseStart_1701953 : Nat := 118140960795 + 1701953 * 2 ^ 59
def prefixEnd_1701953 : Nat := 4983230072969 + 3 ^ 40 * 1701953 * 2
def baseEnd_1701953 : Nat := 64734810397161839611879

theorem tailTrace_1701953 : CollatzResearch.WordTrace tailWord_1701953 prefixEnd_1701953 64734810397161839611879 := by
  unfold tailWord_1701953
  simp only [CollatzResearch.WordTrace]
  refine ⟨62075325603122426276054513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41383550402081617517369675 62075325603122426276054513)
  ·
    refine ⟨46556494202341819707040885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62075325603122426276054513 46556494202341819707040885)
    ·
      refine ⟨4364671331469545597535083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46556494202341819707040885 4364671331469545597535083)
      ·
        refine ⟨6547006997204318396302625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364671331469545597535083 6547006997204318396302625)
        ·
          refine ⟨4910255247903238797226969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547006997204318396302625 4910255247903238797226969)
          ·
            refine ⟨3682691435927429097920227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910255247903238797226969 3682691435927429097920227)
            ·
              refine ⟨5524037153891143646880341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682691435927429097920227 5524037153891143646880341)
              ·
                refine ⟨64734810397161839611879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5524037153891143646880341 64734810397161839611879)
                ·
                  rfl

theorem cell22_1701953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 8].length) (baseStart_1701953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701953 prefixEnd_1701953 := by exact prefixLift 1701953
  have htrace : WordTrace (prefixWord ++ tailWord_1701953) baseStart_1701953 baseEnd_1701953 := by
    simpa [prefixWord, tailWord_1701953, baseEnd_1701953] using wordTrace_append hprefix tailTrace_1701953
  have hstable : (prefixWord ++ tailWord_1701953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701953).length < 2 ^ (prefixWord ++ tailWord_1701953).sum := by decide
  have hdescent : baseEnd_1701953 < baseStart_1701953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701970 : List Nat := [3, 2, 2, 1, 5, 1, 8]
def baseStart_1701970 : Nat := 118140960795 + 1701970 * 2 ^ 59
def prefixEnd_1701970 : Nat := 4983230072969 + 3 ^ 40 * 1701970 * 2
def baseEnd_1701970 : Nat := 21578485667476821438217

theorem tailTrace_1701970 : CollatzResearch.WordTrace tailWord_1701970 prefixEnd_1701970 21578485667476821438217 := by
  unfold tailWord_1701970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518986411015209544855841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41383963762707225452948909 15518986411015209544855841)
  ·
    refine ⟨11639239808261407158641881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15518986411015209544855841 11639239808261407158641881)
    ·
      refine ⟨8729429856196055368981411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11639239808261407158641881 8729429856196055368981411)
      ·
        refine ⟨13094144784294083053472117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729429856196055368981411 13094144784294083053472117)
        ·
          refine ⟨1227576073527570286263011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13094144784294083053472117 1227576073527570286263011)
          ·
            refine ⟨1841364110291355429394517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227576073527570286263011 1841364110291355429394517)
            ·
              refine ⟨21578485667476821438217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1841364110291355429394517 21578485667476821438217)
              ·
                rfl

theorem cell22_1701970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 8].length) (baseStart_1701970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1701970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1701970 prefixEnd_1701970 := by exact prefixLift 1701970
  have htrace : WordTrace (prefixWord ++ tailWord_1701970) baseStart_1701970 baseEnd_1701970 := by
    simpa [prefixWord, tailWord_1701970, baseEnd_1701970] using wordTrace_append hprefix tailTrace_1701970
  have hstable : (prefixWord ++ tailWord_1701970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701970).length < 2 ^ (prefixWord ++ tailWord_1701970).sum := by decide
  have hdescent : baseEnd_1701970 < baseStart_1701970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702036 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1702036 : Nat := 118140960795 + 1702036 * 2 ^ 59
def prefixEnd_1702036 : Nat := 4983230072969 + 3 ^ 40 * 1702036 * 2
def baseEnd_1702036 : Nat := 582641706170672006681657

theorem tailTrace_1702036 : CollatzResearch.WordTrace tailWord_1702036 prefixEnd_1702036 582641706170672006681657 := by
  unfold tailWord_1702036
  simp only [CollatzResearch.WordTrace]
  refine ⟨31039176430910865725662981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41385568574547820967550641 31039176430910865725662981)
  ·
    refine ⟨5819845580795787323561809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31039176430910865725662981 5819845580795787323561809)
    ·
      refine ⟨4364884185596840492671357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5819845580795787323561809 4364884185596840492671357)
      ·
        refine ⟨1636831569598815184751759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4364884185596840492671357 1636831569598815184751759)
        ·
          refine ⟨2455247354398222777127639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636831569598815184751759 2455247354398222777127639)
          ·
            refine ⟨3682871031597334165691459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455247354398222777127639 3682871031597334165691459)
            ·
              refine ⟨5524306547396001248537189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682871031597334165691459 5524306547396001248537189)
              ·
                refine ⟨1035807477636750234100723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5524306547396001248537189 1035807477636750234100723)
                ·
                  refine ⟨1553711216455125351151085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035807477636750234100723 1553711216455125351151085)
                  ·
                    refine ⟨582641706170672006681657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553711216455125351151085 582641706170672006681657)
                    ·
                      rfl

theorem cell22_1702036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1702036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702036 prefixEnd_1702036 := by exact prefixLift 1702036
  have htrace : WordTrace (prefixWord ++ tailWord_1702036) baseStart_1702036 baseEnd_1702036 := by
    simpa [prefixWord, tailWord_1702036, baseEnd_1702036] using wordTrace_append hprefix tailTrace_1702036
  have hstable : (prefixWord ++ tailWord_1702036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702036).length < 2 ^ (prefixWord ++ tailWord_1702036).sum := by decide
  have hdescent : baseEnd_1702036 < baseStart_1702036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702038 : List Nat := [5, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1702038 : Nat := 118140960795 + 1702038 * 2 ^ 59
def prefixEnd_1702038 : Nat := 4983230072969 + 3 ^ 40 * 1702038 * 2
def baseEnd_1702038 : Nat := 64738043423504963125739

theorem tailTrace_1702038 : CollatzResearch.WordTrace tailWord_1702038 prefixEnd_1702038 64738043423504963125739 := by
  unfold tailWord_1702038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879901612988405362056173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41385617205209657195265845 3879901612988405362056173)
  ·
    refine ⟨1454963104870652010771065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3879901612988405362056173 1454963104870652010771065)
    ·
      refine ⟨1091222328652989008078299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454963104870652010771065 1091222328652989008078299)
      ·
        refine ⟨1636833492979483512117449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091222328652989008078299 1636833492979483512117449)
        ·
          refine ⟨1227625119734612634088087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1636833492979483512117449 1227625119734612634088087)
          ·
            refine ⟨1841437679601918951132131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227625119734612634088087 1841437679601918951132131)
            ·
              refine ⟨2762156519402878426698197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841437679601918951132131 2762156519402878426698197)
              ·
                refine ⟨64738043423504963125739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2762156519402878426698197 64738043423504963125739)
                ·
                  rfl

theorem cell22_1702038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1702038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702038 prefixEnd_1702038 := by exact prefixLift 1702038
  have htrace : WordTrace (prefixWord ++ tailWord_1702038) baseStart_1702038 baseEnd_1702038 := by
    simpa [prefixWord, tailWord_1702038, baseEnd_1702038] using wordTrace_append hprefix tailTrace_1702038
  have hstable : (prefixWord ++ tailWord_1702038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702038).length < 2 ^ (prefixWord ++ tailWord_1702038).sum := by decide
  have hdescent : baseEnd_1702038 < baseStart_1702038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702073 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_1702073 : Nat := 118140960795 + 1702073 * 2 ^ 59
def prefixEnd_1702073 : Nat := 4983230072969 + 3 ^ 40 * 1702073 * 2
def baseEnd_1702073 : Nat := 582654372026816243506543

theorem tailTrace_1702073 : CollatzResearch.WordTrace tailWord_1702073 prefixEnd_1702073 582654372026816243506543 := by
  unfold tailWord_1702073
  simp only [CollatzResearch.WordTrace]
  refine ⟨62079702362687686770422873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41386468241791791180281915 62079702362687686770422873)
  ·
    refine ⟨46559776772015765077817155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62079702362687686770422873 46559776772015765077817155)
    ·
      refine ⟨69839665158023647616725733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46559776772015765077817155 69839665158023647616725733)
      ·
        refine ⟨13094937217129433928136075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69839665158023647616725733 13094937217129433928136075)
        ·
          refine ⟨19642405825694150892204113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13094937217129433928136075 19642405825694150892204113)
          ·
            refine ⟨14731804369270613169153085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19642405825694150892204113 14731804369270613169153085)
            ·
              refine ⟨5524426638476479938432407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14731804369270613169153085 5524426638476479938432407)
              ·
                refine ⟨8286639957714719907648611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524426638476479938432407 8286639957714719907648611)
                ·
                  refine ⟨12429959936572079861472917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286639957714719907648611 12429959936572079861472917)
                  ·
                    refine ⟨582654372026816243506543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12429959936572079861472917 582654372026816243506543)
                    ·
                      rfl

theorem cell22_1702073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_1702073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702073 prefixEnd_1702073 := by exact prefixLift 1702073
  have htrace : WordTrace (prefixWord ++ tailWord_1702073) baseStart_1702073 baseEnd_1702073 := by
    simpa [prefixWord, tailWord_1702073, baseEnd_1702073] using wordTrace_append hprefix tailTrace_1702073
  have hstable : (prefixWord ++ tailWord_1702073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702073).length < 2 ^ (prefixWord ++ tailWord_1702073).sum := by decide
  have hdescent : baseEnd_1702073 < baseStart_1702073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702137 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 1, 3]
def baseStart_1702137 : Nat := 118140960795 + 1702137 * 2 ^ 59
def prefixEnd_1702137 : Nat := 4983230072969 + 3 ^ 40 * 1702137 * 2
def baseEnd_1702137 : Nat := 582676280534741409906347

theorem tailTrace_1702137 : CollatzResearch.WordTrace tailWord_1702137 prefixEnd_1702137 582676280534741409906347 := by
  unfold tailWord_1702137
  simp only [CollatzResearch.WordTrace]
  refine ⟨62082036634455825700752665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41388024422970550467168443 62082036634455825700752665)
  ·
    refine ⟨46561527475841869275564499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62082036634455825700752665 46561527475841869275564499)
    ·
      refine ⟨69842291213762803913346749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46561527475841869275564499 69842291213762803913346749)
      ·
        refine ⟨26190859205161051467505031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69842291213762803913346749 26190859205161051467505031)
        ·
          refine ⟨39286288807741577201257547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26190859205161051467505031 39286288807741577201257547)
          ·
            refine ⟨58929433211612365801886321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39286288807741577201257547 58929433211612365801886321)
            ·
              refine ⟨44197074908709274351414741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58929433211612365801886321 44197074908709274351414741)
              ·
                refine ⟨1035868943172873617611283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44197074908709274351414741 1035868943172873617611283)
                ·
                  refine ⟨1553803414759310426416925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035868943172873617611283 1553803414759310426416925)
                  ·
                    refine ⟨582676280534741409906347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553803414759310426416925 582676280534741409906347)
                    ·
                      rfl

theorem cell22_1702137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_1702137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702137 prefixEnd_1702137 := by exact prefixLift 1702137
  have htrace : WordTrace (prefixWord ++ tailWord_1702137) baseStart_1702137 baseEnd_1702137 := by
    simpa [prefixWord, tailWord_1702137, baseEnd_1702137] using wordTrace_append hprefix tailTrace_1702137
  have hstable : (prefixWord ++ tailWord_1702137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702137).length < 2 ^ (prefixWord ++ tailWord_1702137).sum := by decide
  have hdescent : baseEnd_1702137 < baseStart_1702137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702167 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 5]
def baseStart_1702167 : Nat := 118140960795 + 1702167 * 2 ^ 59
def prefixEnd_1702167 : Nat := 4983230072969 + 3 ^ 40 * 1702167 * 2
def baseEnd_1702167 : Nat := 194228850049277110552085

theorem tailTrace_1702167 : CollatzResearch.WordTrace tailWord_1702167 prefixEnd_1702167 194228850049277110552085 := by
  unfold tailWord_1702167
  simp only [CollatzResearch.WordTrace]
  refine ⟨62083130824347140824344755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41388753882898093882896503 62083130824347140824344755)
  ·
    refine ⟨93124696236520711236517133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62083130824347140824344755 93124696236520711236517133)
    ·
      refine ⟨34921761088695266713693925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93124696236520711236517133 34921761088695266713693925)
      ·
        refine ⟨6547830204130362508817611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34921761088695266713693925 6547830204130362508817611)
        ·
          refine ⟨9821745306195543763226417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547830204130362508817611 9821745306195543763226417)
          ·
            refine ⟨7366308979646657822419813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9821745306195543763226417 7366308979646657822419813)
            ·
              refine ⟨1381182933683748341703715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7366308979646657822419813 1381182933683748341703715)
              ·
                refine ⟨2071774400525622512555573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381182933683748341703715 2071774400525622512555573)
                ·
                  refine ⟨194228850049277110552085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2071774400525622512555573 194228850049277110552085)
                  ·
                    rfl

theorem cell22_1702167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 5].length) (baseStart_1702167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702167 prefixEnd_1702167 := by exact prefixLift 1702167
  have htrace : WordTrace (prefixWord ++ tailWord_1702167) baseStart_1702167 baseEnd_1702167 := by
    simpa [prefixWord, tailWord_1702167, baseEnd_1702167] using wordTrace_append hprefix tailTrace_1702167
  have hstable : (prefixWord ++ tailWord_1702167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702167).length < 2 ^ (prefixWord ++ tailWord_1702167).sum := by decide
  have hdescent : baseEnd_1702167 < baseStart_1702167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702223 : List Nat := [1, 1, 2, 1, 1, 2, 1, 13]
def baseStart_1702223 : Nat := 118140960795 + 1702223 * 2 ^ 59
def prefixEnd_1702223 : Nat := 4983230072969 + 3 ^ 40 * 1702223 * 2
def baseEnd_1702223 : Nat := 64745080010251761361787

theorem tailTrace_1702223 : CollatzResearch.WordTrace tailWord_1702223 prefixEnd_1702223 64745080010251761361787 := by
  unfold tailWord_1702223
  simp only [CollatzResearch.WordTrace]
  refine ⟨62085173312144262388383323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41390115541429508258922215 62085173312144262388383323)
  ·
    refine ⟨93127759968216393582574985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62085173312144262388383323 93127759968216393582574985)
    ·
      refine ⟨69845819976162295186931239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93127759968216393582574985 69845819976162295186931239)
      ·
        refine ⟨104768729964243442780396859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69845819976162295186931239 104768729964243442780396859)
        ·
          refine ⟨157153094946365164170595289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104768729964243442780396859 157153094946365164170595289)
          ·
            refine ⟨117864821209773873127946467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157153094946365164170595289 117864821209773873127946467)
            ·
              refine ⟨176797231814660809691919701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117864821209773873127946467 176797231814660809691919701)
              ·
                refine ⟨64745080010251761361787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 176797231814660809691919701 64745080010251761361787)
                ·
                  rfl

theorem cell22_1702223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 13].length) (baseStart_1702223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702223 prefixEnd_1702223 := by exact prefixLift 1702223
  have htrace : WordTrace (prefixWord ++ tailWord_1702223) baseStart_1702223 baseEnd_1702223 := by
    simpa [prefixWord, tailWord_1702223, baseEnd_1702223] using wordTrace_append hprefix tailTrace_1702223
  have hstable : (prefixWord ++ tailWord_1702223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702223).length < 2 ^ (prefixWord ++ tailWord_1702223).sum := by decide
  have hdescent : baseEnd_1702223 < baseStart_1702223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702242 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1702242 : Nat := 118140960795 + 1702242 * 2 ^ 59
def prefixEnd_1702242 : Nat := 4983230072969 + 3 ^ 40 * 1702242 * 2
def baseEnd_1702242 : Nat := 582712224180556136031025

theorem tailTrace_1702242 : CollatzResearch.WordTrace tailWord_1702242 prefixEnd_1702242 582712224180556136031025 := by
  unfold tailWord_1702242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521466574768857158331245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41390577532716952422216653 15521466574768857158331245)
  ·
    refine ⟨5820549965538321434374217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15521466574768857158331245 5820549965538321434374217)
    ·
      refine ⟨4365412474153741075780663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5820549965538321434374217 4365412474153741075780663)
      ·
        refine ⟨6548118711230611613670995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365412474153741075780663 6548118711230611613670995)
        ·
          refine ⟨9822178066845917420506493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548118711230611613670995 9822178066845917420506493)
          ·
            refine ⟨3683316775067219032689935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9822178066845917420506493 3683316775067219032689935)
            ·
              refine ⟨5524975162600828549034903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683316775067219032689935 5524975162600828549034903)
              ·
                refine ⟨8287462743901242823552355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524975162600828549034903 8287462743901242823552355)
                ·
                  refine ⟨12431194115851864235328533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8287462743901242823552355 12431194115851864235328533)
                  ·
                    refine ⟨582712224180556136031025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12431194115851864235328533 582712224180556136031025)
                    ·
                      rfl

theorem cell22_1702242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1702242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702242 prefixEnd_1702242 := by exact prefixLift 1702242
  have htrace : WordTrace (prefixWord ++ tailWord_1702242) baseStart_1702242 baseEnd_1702242 := by
    simpa [prefixWord, tailWord_1702242, baseEnd_1702242] using wordTrace_append hprefix tailTrace_1702242
  have hstable : (prefixWord ++ tailWord_1702242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702242).length < 2 ^ (prefixWord ++ tailWord_1702242).sum := by decide
  have hdescent : baseEnd_1702242 < baseStart_1702242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702261 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1702261 : Nat := 118140960795 + 1702261 * 2 ^ 59
def prefixEnd_1702261 : Nat := 4983230072969 + 3 ^ 40 * 1702261 * 2
def baseEnd_1702261 : Nat := 582718728268846419805967

theorem tailTrace_1702261 : CollatzResearch.WordTrace tailWord_1702261 prefixEnd_1702261 582718728268846419805967 := by
  unfold tailWord_1702261
  simp only [CollatzResearch.WordTrace]
  refine ⟨62086559286006594878266637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41391039524004396585511091 62086559286006594878266637)
  ·
    refine ⟨23282459732252473079349989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62086559286006594878266637 23282459732252473079349989)
    ·
      refine ⟨4365461199797338702378123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23282459732252473079349989 4365461199797338702378123)
      ·
        refine ⟨6548191799696008053567185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365461199797338702378123 6548191799696008053567185)
        ·
          refine ⟨4911143849772006040175389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6548191799696008053567185 4911143849772006040175389)
          ·
            refine ⟨1841678943664502265065771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4911143849772006040175389 1841678943664502265065771)
            ·
              refine ⟨2762518415496753397598657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841678943664502265065771 2762518415496753397598657)
              ·
                refine ⟨2071888811622565048198993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762518415496753397598657 2071888811622565048198993)
                ·
                  refine ⟨1553916608716923786149245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071888811622565048198993 1553916608716923786149245)
                  ·
                    refine ⟨582718728268846419805967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553916608716923786149245 582718728268846419805967)
                    ·
                      rfl

theorem cell22_1702261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1702261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702261 prefixEnd_1702261 := by exact prefixLift 1702261
  have htrace : WordTrace (prefixWord ++ tailWord_1702261) baseStart_1702261 baseEnd_1702261 := by
    simpa [prefixWord, tailWord_1702261, baseEnd_1702261] using wordTrace_append hprefix tailTrace_1702261
  have hstable : (prefixWord ++ tailWord_1702261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702261).length < 2 ^ (prefixWord ++ tailWord_1702261).sum := by decide
  have hdescent : baseEnd_1702261 < baseStart_1702261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702362 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1702362 : Nat := 118140960795 + 1702362 * 2 ^ 59
def prefixEnd_1702362 : Nat := 4983230072969 + 3 ^ 40 * 1702362 * 2
def baseEnd_1702362 : Nat := 582753302632915823030657

theorem tailTrace_1702362 : CollatzResearch.WordTrace tailWord_1702362 prefixEnd_1702362 582753302632915823030657 := by
  unfold tailWord_1702362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522560764660172281923335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41393495372427126085128893 15522560764660172281923335)
  ·
    refine ⟨23283841146990258422885003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15522560764660172281923335 23283841146990258422885003)
    ·
      refine ⟨34925761720485387634327505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23283841146990258422885003 34925761720485387634327505)
      ·
        refine ⟨26194321290364040725745629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34925761720485387634327505 26194321290364040725745629)
        ·
          refine ⟨9822870483886515272154611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26194321290364040725745629 9822870483886515272154611)
          ·
            refine ⟨14734305725829772908231917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822870483886515272154611 14734305725829772908231917)
            ·
              refine ⟨5525364647186164840586969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14734305725829772908231917 5525364647186164840586969)
              ·
                refine ⟨4144023485389623630440227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525364647186164840586969 4144023485389623630440227)
                ·
                  refine ⟨6216035228084435445660341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144023485389623630440227 6216035228084435445660341)
                  ·
                    refine ⟨582753302632915823030657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6216035228084435445660341 582753302632915823030657)
                    ·
                      rfl

theorem cell22_1702362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1702362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702362 prefixEnd_1702362 := by exact prefixLift 1702362
  have htrace : WordTrace (prefixWord ++ tailWord_1702362) baseStart_1702362 baseEnd_1702362 := by
    simpa [prefixWord, tailWord_1702362, baseEnd_1702362] using wordTrace_append hprefix tailTrace_1702362
  have hstable : (prefixWord ++ tailWord_1702362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702362).length < 2 ^ (prefixWord ++ tailWord_1702362).sum := by decide
  have hdescent : baseEnd_1702362 < baseStart_1702362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702379 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 2, 3]
def baseStart_1702379 : Nat := 118140960795 + 1702379 * 2 ^ 59
def prefixEnd_1702379 : Nat := 4983230072969 + 3 ^ 40 * 1702379 * 2
def baseEnd_1702379 : Nat := 582759122080333445355605

theorem tailTrace_1702379 : CollatzResearch.WordTrace tailWord_1702379 prefixEnd_1702379 582759122080333445355605 := by
  unfold tailWord_1702379
  simp only [CollatzResearch.WordTrace]
  refine ⟨62090863099579101031062191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41393908733052734020708127 62090863099579101031062191)
  ·
    refine ⟨93136294649368651546593287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62090863099579101031062191 93136294649368651546593287)
    ·
      refine ⟨139704441974052977319889931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93136294649368651546593287 139704441974052977319889931)
      ·
        refine ⟨209556662961079465979834897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139704441974052977319889931 209556662961079465979834897)
        ·
          refine ⟨157167497220809599484876173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209556662961079465979834897 157167497220809599484876173)
          ·
            refine ⟨58937811457803599806828565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157167497220809599484876173 58937811457803599806828565)
            ·
              refine ⟨2762709912084543740945089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58937811457803599806828565 2762709912084543740945089)
              ·
                refine ⟨2072032434063407805708817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762709912084543740945089 2072032434063407805708817)
                ·
                  refine ⟨1554024325547555854281613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072032434063407805708817 1554024325547555854281613)
                  ·
                    refine ⟨582759122080333445355605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554024325547555854281613 582759122080333445355605)
                    ·
                      rfl

theorem cell22_1702379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3].length) (baseStart_1702379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702379 prefixEnd_1702379 := by exact prefixLift 1702379
  have htrace : WordTrace (prefixWord ++ tailWord_1702379) baseStart_1702379 baseEnd_1702379 := by
    simpa [prefixWord, tailWord_1702379, baseEnd_1702379] using wordTrace_append hprefix tailTrace_1702379
  have hstable : (prefixWord ++ tailWord_1702379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702379).length < 2 ^ (prefixWord ++ tailWord_1702379).sum := by decide
  have hdescent : baseEnd_1702379 < baseStart_1702379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702381 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1702381 : Nat := 118140960795 + 1702381 * 2 ^ 59
def prefixEnd_1702381 : Nat := 4983230072969 + 3 ^ 40 * 1702381 * 2
def baseEnd_1702381 : Nat := 194253268907068702268533

theorem tailTrace_1702381 : CollatzResearch.WordTrace tailWord_1702381 prefixEnd_1702381 194253268907068702268533 := by
  unfold tailWord_1702381
  simp only [CollatzResearch.WordTrace]
  refine ⟨62090936045571855372634997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41393957363714570248423331 62090936045571855372634997)
  ·
    refine ⟨5821025254272361441184531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62090936045571855372634997 5821025254272361441184531)
    ·
      refine ⟨8731537881408542161776797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821025254272361441184531 8731537881408542161776797)
      ·
        refine ⟨3274326705528203310666299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8731537881408542161776797 3274326705528203310666299)
        ·
          refine ⟨4911490058292304965999449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274326705528203310666299 4911490058292304965999449)
          ·
            refine ⟨3683617543719228724499587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911490058292304965999449 3683617543719228724499587)
            ·
              refine ⟨5525426315578843086749381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683617543719228724499587 5525426315578843086749381)
              ·
                refine ⟨1036017434171033078765509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5525426315578843086749381 1036017434171033078765509)
                ·
                  refine ⟨194253268907068702268533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036017434171033078765509 194253268907068702268533)
                  ·
                    rfl

theorem cell22_1702381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1702381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702381 prefixEnd_1702381 := by exact prefixLift 1702381
  have htrace : WordTrace (prefixWord ++ tailWord_1702381) baseStart_1702381 baseEnd_1702381 := by
    simpa [prefixWord, tailWord_1702381, baseEnd_1702381] using wordTrace_append hprefix tailTrace_1702381
  have hstable : (prefixWord ++ tailWord_1702381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702381).length < 2 ^ (prefixWord ++ tailWord_1702381).sum := by decide
  have hdescent : baseEnd_1702381 < baseStart_1702381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702467 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_1702467 : Nat := 118140960795 + 1702467 * 2 ^ 59
def prefixEnd_1702467 : Nat := 4983230072969 + 3 ^ 40 * 1702467 * 2
def baseEnd_1702467 : Nat := 582789246278730549155335

theorem tailTrace_1702467 : CollatzResearch.WordTrace tailWord_1702467 prefixEnd_1702467 582789246278730549155335 := by
  unfold tailWord_1702467
  simp only [CollatzResearch.WordTrace]
  refine ⟨62094072723260292060265655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41396048482173528040177103 62094072723260292060265655)
  ·
    refine ⟨93141109084890438090398483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62094072723260292060265655 93141109084890438090398483)
    ·
      refine ⟨139711663627335657135597725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93141109084890438090398483 139711663627335657135597725)
      ·
        refine ⟨52391873860250871425849147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139711663627335657135597725 52391873860250871425849147)
        ·
          refine ⟨78587810790376307138773721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52391873860250871425849147 78587810790376307138773721)
          ·
            refine ⟨58940858092782230354080291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78587810790376307138773721 58940858092782230354080291)
            ·
              refine ⟨88411287139173345531120437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58940858092782230354080291 88411287139173345531120437)
              ·
                refine ⟨8288558169297501143542541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88411287139173345531120437 8288558169297501143542541)
                ·
                  refine ⟨3108209313486562928828453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8288558169297501143542541 3108209313486562928828453)
                  ·
                    refine ⟨582789246278730549155335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3108209313486562928828453 582789246278730549155335)
                    ·
                      rfl

theorem cell22_1702467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_1702467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702467 prefixEnd_1702467 := by exact prefixLift 1702467
  have htrace : WordTrace (prefixWord ++ tailWord_1702467) baseStart_1702467 baseEnd_1702467 := by
    simpa [prefixWord, tailWord_1702467, baseEnd_1702467] using wordTrace_append hprefix tailTrace_1702467
  have hstable : (prefixWord ++ tailWord_1702467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702467).length < 2 ^ (prefixWord ++ tailWord_1702467).sum := by decide
  have hdescent : baseEnd_1702467 < baseStart_1702467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702546 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1702546 : Nat := 118140960795 + 1702546 * 2 ^ 59
def prefixEnd_1702546 : Nat := 4983230072969 + 3 ^ 40 * 1702546 * 2
def baseEnd_1702546 : Nat := 582816289593200676430093

theorem tailTrace_1702546 : CollatzResearch.WordTrace tailWord_1702546 prefixEnd_1702546 582816289593200676430093 := by
  unfold tailWord_1702546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15524238522493522138097873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41397969393316059034927661 15524238522493522138097873)
  ·
    refine ⟨11643178891870141603573405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15524238522493522138097873 11643178891870141603573405)
    ·
      refine ⟨4366192084451303101340027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11643178891870141603573405 4366192084451303101340027)
      ·
        refine ⟨6549288126676954652010041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4366192084451303101340027 6549288126676954652010041)
        ·
          refine ⟨4911966095007715989007531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6549288126676954652010041 4911966095007715989007531)
          ·
            refine ⟨7367949142511573983511297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911966095007715989007531 7367949142511573983511297)
            ·
              refine ⟨5525961856883680487633473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367949142511573983511297 5525961856883680487633473)
              ·
                refine ⟨4144471392662760365725105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525961856883680487633473 4144471392662760365725105)
                ·
                  refine ⟨3108353544497070274293829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4144471392662760365725105 3108353544497070274293829)
                  ·
                    refine ⟨582816289593200676430093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3108353544497070274293829 582816289593200676430093)
                    ·
                      rfl

theorem cell22_1702546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1702546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702546 prefixEnd_1702546 := by exact prefixLift 1702546
  have htrace : WordTrace (prefixWord ++ tailWord_1702546) baseStart_1702546 baseEnd_1702546 := by
    simpa [prefixWord, tailWord_1702546, baseEnd_1702546] using wordTrace_append hprefix tailTrace_1702546
  have hstable : (prefixWord ++ tailWord_1702546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702546).length < 2 ^ (prefixWord ++ tailWord_1702546).sum := by decide
  have hdescent : baseEnd_1702546 < baseStart_1702546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702548 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1702548 : Nat := 118140960795 + 1702548 * 2 ^ 59
def prefixEnd_1702548 : Nat := 4983230072969 + 3 ^ 40 * 1702548 * 2
def baseEnd_1702548 : Nat := 582816974234073337880087

theorem tailTrace_1702548 : CollatzResearch.WordTrace tailWord_1702548 prefixEnd_1702548 582816974234073337880087 := by
  unfold tailWord_1702548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048513517983421446982149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41398018023977895262642865 31048513517983421446982149)
  ·
    refine ⟨5821596284621891521309153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31048513517983421446982149 5821596284621891521309153)
    ·
      refine ⟨4366197213466418640981865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5821596284621891521309153 4366197213466418640981865)
      ·
        refine ⟨3274647910099813980736399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4366197213466418640981865 3274647910099813980736399)
        ·
          refine ⟨4911971865149720971104599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274647910099813980736399 4911971865149720971104599)
          ·
            refine ⟨7367957797724581456656899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911971865149720971104599 7367957797724581456656899)
            ·
              refine ⟨11051936696586872184985349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7367957797724581456656899 11051936696586872184985349)
              ·
                refine ⟨2072238130610038534684753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11051936696586872184985349 2072238130610038534684753)
                ·
                  refine ⟨1554178597957528901013565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072238130610038534684753 1554178597957528901013565)
                  ·
                    refine ⟨582816974234073337880087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554178597957528901013565 582816974234073337880087)
                    ·
                      rfl

theorem cell22_1702548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1702548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702548 prefixEnd_1702548 := by exact prefixLift 1702548
  have htrace : WordTrace (prefixWord ++ tailWord_1702548) baseStart_1702548 baseEnd_1702548 := by
    simpa [prefixWord, tailWord_1702548, baseEnd_1702548] using wordTrace_append hprefix tailTrace_1702548
  have hstable : (prefixWord ++ tailWord_1702548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702548).length < 2 ^ (prefixWord ++ tailWord_1702548).sum := by decide
  have hdescent : baseEnd_1702548 < baseStart_1702548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702561 : List Nat := [1, 2, 3, 3, 3, 2, 1, 7]
def baseStart_1702561 : Nat := 118140960795 + 1702561 * 2 ^ 59
def prefixEnd_1702561 : Nat := 4983230072969 + 3 ^ 40 * 1702561 * 2
def baseEnd_1702561 : Nat := 64757936044416181922783

theorem tailTrace_1702561 : CollatzResearch.WordTrace tailWord_1702561 prefixEnd_1702561 64757936044416181922783 := by
  unfold tailWord_1702561
  simp only [CollatzResearch.WordTrace]
  refine ⟨62097501184919746114187537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41398334123279830742791691 62097501184919746114187537)
  ·
    refine ⟨46573125888689809585640653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62097501184919746114187537 46573125888689809585640653)
    ·
      refine ⟨17464922208258678594615245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46573125888689809585640653 17464922208258678594615245)
      ·
        refine ⟨6549345828097004472980717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17464922208258678594615245 6549345828097004472980717)
        ·
          refine ⟨2456004685536376677367769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6549345828097004472980717 2456004685536376677367769)
          ·
            refine ⟨1842003514152282508025827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2456004685536376677367769 1842003514152282508025827)
            ·
              refine ⟨2763005271228423762038741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842003514152282508025827 2763005271228423762038741)
              ·
                refine ⟨64757936044416181922783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2763005271228423762038741 64757936044416181922783)
                ·
                  rfl

theorem cell22_1702561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 7].length) (baseStart_1702561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702561 prefixEnd_1702561 := by exact prefixLift 1702561
  have htrace : WordTrace (prefixWord ++ tailWord_1702561) baseStart_1702561 baseEnd_1702561 := by
    simpa [prefixWord, tailWord_1702561, baseEnd_1702561] using wordTrace_append hprefix tailTrace_1702561
  have hstable : (prefixWord ++ tailWord_1702561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702561).length < 2 ^ (prefixWord ++ tailWord_1702561).sum := by decide
  have hdescent : baseEnd_1702561 < baseStart_1702561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702606 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1702606 : Nat := 118140960795 + 1702606 * 2 ^ 59
def prefixEnd_1702606 : Nat := 4983230072969 + 3 ^ 40 * 1702606 * 2
def baseEnd_1702606 : Nat := 194278942939793506643303

theorem tailTrace_1702606 : CollatzResearch.WordTrace tailWord_1702606 prefixEnd_1702606 194278942939793506643303 := by
  unfold tailWord_1702606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762392808719589849946959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41399428313171145866383781 7762392808719589849946959)
  ·
    refine ⟨11643589213079384774920439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762392808719589849946959 11643589213079384774920439)
    ·
      refine ⟨17465383819619077162380659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11643589213079384774920439 17465383819619077162380659)
      ·
        refine ⟨26198075729428615743570989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17465383819619077162380659 26198075729428615743570989)
        ·
          refine ⟨9824278398535730903839121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26198075729428615743570989 9824278398535730903839121)
          ·
            refine ⟨7368208798901798177879341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9824278398535730903839121 7368208798901798177879341)
            ·
              refine ⟨2763078299588174316704753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7368208798901798177879341 2763078299588174316704753)
              ·
                refine ⟨2072308724691130737528565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763078299588174316704753 2072308724691130737528565)
                ·
                  refine ⟨194278942939793506643303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072308724691130737528565 194278942939793506643303)
                  ·
                    rfl

theorem cell22_1702606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1702606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702606 prefixEnd_1702606 := by exact prefixLift 1702606
  have htrace : WordTrace (prefixWord ++ tailWord_1702606) baseStart_1702606 baseEnd_1702606 := by
    simpa [prefixWord, tailWord_1702606, baseEnd_1702606] using wordTrace_append hprefix tailTrace_1702606
  have hstable : (prefixWord ++ tailWord_1702606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702606).length < 2 ^ (prefixWord ++ tailWord_1702606).sum := by decide
  have hdescent : baseEnd_1702606 < baseStart_1702606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702649 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_1702649 : Nat := 118140960795 + 1702649 * 2 ^ 59
def prefixEnd_1702649 : Nat := 4983230072969 + 3 ^ 40 * 1702649 * 2
def baseEnd_1702649 : Nat := 582851548598142741104777

theorem tailTrace_1702649 : CollatzResearch.WordTrace tailWord_1702649 prefixEnd_1702649 582851548598142741104777 := by
  unfold tailWord_1702649
  simp only [CollatzResearch.WordTrace]
  refine ⟨62100710808600937143391001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41400473872400624762260667 62100710808600937143391001)
  ·
    refine ⟨46575533106450702857543251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62100710808600937143391001 46575533106450702857543251)
    ·
      refine ⟨69863299659676054286314877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46575533106450702857543251 69863299659676054286314877)
      ·
        refine ⟨26198737372378520357368079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69863299659676054286314877 26198737372378520357368079)
        ·
          refine ⟨39298106058567780536052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26198737372378520357368079 39298106058567780536052119)
          ·
            refine ⟨58947159087851670804078179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39298106058567780536052119 58947159087851670804078179)
            ·
              refine ⟨88420738631777506206117269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58947159087851670804078179 88420738631777506206117269)
              ·
                refine ⟨4144722123364570603411747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88420738631777506206117269 4144722123364570603411747)
                ·
                  refine ⟨6217083185046855905117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144722123364570603411747 6217083185046855905117621)
                  ·
                    refine ⟨582851548598142741104777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6217083185046855905117621 582851548598142741104777)
                    ·
                      rfl

theorem cell22_1702649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_1702649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702649 prefixEnd_1702649 := by exact prefixLift 1702649
  have htrace : WordTrace (prefixWord ++ tailWord_1702649) baseStart_1702649 baseEnd_1702649 := by
    simpa [prefixWord, tailWord_1702649, baseEnd_1702649] using wordTrace_append hprefix tailTrace_1702649
  have hstable : (prefixWord ++ tailWord_1702649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702649).length < 2 ^ (prefixWord ++ tailWord_1702649).sum := by decide
  have hdescent : baseEnd_1702649 < baseStart_1702649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702666 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1702666 : Nat := 118140960795 + 1702666 * 2 ^ 59
def prefixEnd_1702666 : Nat := 4983230072969 + 3 ^ 40 * 1702666 * 2
def baseEnd_1702666 : Nat := 582857368045560363429725

theorem tailTrace_1702666 : CollatzResearch.WordTrace tailWord_1702666 prefixEnd_1702666 582857368045560363429725 := by
  unfold tailWord_1702666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15525332712384837261689963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41400887233026232697839901 15525332712384837261689963)
  ·
    refine ⟨23287999068577255892534945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15525332712384837261689963 23287999068577255892534945)
    ·
      refine ⟨17465999301432941919401209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23287999068577255892534945 17465999301432941919401209)
      ·
        refine ⟨13099499476074706439550907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17465999301432941919401209 13099499476074706439550907)
        ·
          refine ⟨19649249214112059659326361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13099499476074706439550907 19649249214112059659326361)
          ·
            refine ⟨14736936910584044744494771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19649249214112059659326361 14736936910584044744494771)
            ·
              refine ⟨22105405365876067116742157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14736936910584044744494771 22105405365876067116742157)
              ·
                refine ⟨8289527012203525168778309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22105405365876067116742157 8289527012203525168778309)
                ·
                  refine ⟨1554286314788160969145933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8289527012203525168778309 1554286314788160969145933)
                  ·
                    refine ⟨582857368045560363429725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554286314788160969145933 582857368045560363429725)
                    ·
                      rfl

theorem cell22_1702666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1702666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702666 prefixEnd_1702666 := by exact prefixLift 1702666
  have htrace : WordTrace (prefixWord ++ tailWord_1702666) baseStart_1702666 baseEnd_1702666 := by
    simpa [prefixWord, tailWord_1702666, baseEnd_1702666] using wordTrace_append hprefix tailTrace_1702666
  have hstable : (prefixWord ++ tailWord_1702666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702666).length < 2 ^ (prefixWord ++ tailWord_1702666).sum := by decide
  have hdescent : baseEnd_1702666 < baseStart_1702666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702741 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 5]
def baseStart_1702741 : Nat := 118140960795 + 1702741 * 2 ^ 59
def prefixEnd_1702741 : Nat := 4983230072969 + 3 ^ 40 * 1702741 * 2
def baseEnd_1702741 : Nat := 194294347359428389268165

theorem tailTrace_1702741 : CollatzResearch.WordTrace tailWord_1702741 prefixEnd_1702741 194294347359428389268165 := by
  unfold tailWord_1702741
  simp only [CollatzResearch.WordTrace]
  refine ⟨62104066324267636855740077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41402710882845091237160051 62104066324267636855740077)
  ·
    refine ⟨23289024871600363820902529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62104066324267636855740077 23289024871600363820902529)
    ·
      refine ⟨17466768653700272865676897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23289024871600363820902529 17466768653700272865676897)
      ·
        refine ⟨13100076490275204649257673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17466768653700272865676897 13100076490275204649257673)
        ·
          refine ⟨9825057367706403486943255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13100076490275204649257673 9825057367706403486943255)
          ·
            refine ⟨14737586051559605230414883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825057367706403486943255 14737586051559605230414883)
            ·
              refine ⟨22106379077339407845622325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14737586051559605230414883 22106379077339407845622325)
              ·
                refine ⟨2072473038500569485527093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22106379077339407845622325 2072473038500569485527093)
                ·
                  refine ⟨194294347359428389268165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072473038500569485527093 194294347359428389268165)
                  ·
                    rfl

theorem cell22_1702741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_1702741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702741 prefixEnd_1702741 := by exact prefixLift 1702741
  have htrace : WordTrace (prefixWord ++ tailWord_1702741) baseStart_1702741 baseEnd_1702741 := by
    simpa [prefixWord, tailWord_1702741, baseEnd_1702741] using wordTrace_append hprefix tailTrace_1702741
  have hstable : (prefixWord ++ tailWord_1702741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702741).length < 2 ^ (prefixWord ++ tailWord_1702741).sum := by decide
  have hdescent : baseEnd_1702741 < baseStart_1702741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702816 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_1702816 : Nat := 118140960795 + 1702816 * 2 ^ 59
def prefixEnd_1702816 : Nat := 4983230072969 + 3 ^ 40 * 1702816 * 2
def baseEnd_1702816 : Nat := 582908716111009972179265

theorem tailTrace_1702816 : CollatzResearch.WordTrace tailWord_1702816 prefixEnd_1702816 582908716111009972179265 := by
  unfold tailWord_1702816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31053400899497962332360151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41404534532663949776480201 31053400899497962332360151)
  ·
    refine ⟨46580101349246943498540227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31053400899497962332360151 46580101349246943498540227)
    ·
      refine ⟨69870152023870415247810341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46580101349246943498540227 69870152023870415247810341)
      ·
        refine ⟨13100653504475702858964439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69870152023870415247810341 13100653504475702858964439)
        ·
          refine ⟨19650980256713554288446659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100653504475702858964439 19650980256713554288446659)
          ·
            refine ⟨29476470385070331432669989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19650980256713554288446659 29476470385070331432669989)
            ·
              refine ⟨5526838197200687143625623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29476470385070331432669989 5526838197200687143625623)
              ·
                refine ⟨8290257295801030715438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526838197200687143625623 8290257295801030715438435)
                ·
                  refine ⟨12435385943701546073157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290257295801030715438435 12435385943701546073157653)
                  ·
                    refine ⟨582908716111009972179265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12435385943701546073157653 582908716111009972179265)
                    ·
                      rfl

theorem cell22_1702816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_1702816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702816 prefixEnd_1702816 := by exact prefixLift 1702816
  have htrace : WordTrace (prefixWord ++ tailWord_1702816) baseStart_1702816 baseEnd_1702816 := by
    simpa [prefixWord, tailWord_1702816, baseEnd_1702816] using wordTrace_append hprefix tailTrace_1702816
  have hstable : (prefixWord ++ tailWord_1702816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702816).length < 2 ^ (prefixWord ++ tailWord_1702816).sum := by decide
  have hdescent : baseEnd_1702816 < baseStart_1702816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702897 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 1, 3]
def baseStart_1702897 : Nat := 118140960795 + 1702897 * 2 ^ 59
def prefixEnd_1702897 : Nat := 4983230072969 + 3 ^ 40 * 1702897 * 2
def baseEnd_1702897 : Nat := 582936444066352760904017

theorem tailTrace_1702897 : CollatzResearch.WordTrace tailWord_1702897 prefixEnd_1702897 582936444066352760904017 := by
  unfold tailWord_1702897
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109756111702475498418945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41406504074468316998945963 62109756111702475498418945)
  ·
    refine ⟨46582317083776856623814209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62109756111702475498418945 46582317083776856623814209)
    ·
      refine ⟨34936737812832642467860657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46582317083776856623814209 34936737812832642467860657)
      ·
        refine ⟨26202553359624481850895493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34936737812832642467860657 26202553359624481850895493)
        ·
          refine ⟨4912978754929590347042905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26202553359624481850895493 4912978754929590347042905)
          ·
            refine ⟨3684734066197192760282179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4912978754929590347042905 3684734066197192760282179)
            ·
              refine ⟨5527101099295789140423269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684734066197192760282179 5527101099295789140423269)
              ·
                refine ⟨1036331456117960463829363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5527101099295789140423269 1036331456117960463829363)
                ·
                  refine ⟨1554497184176940695744045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036331456117960463829363 1554497184176940695744045)
                  ·
                    refine ⟨582936444066352760904017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554497184176940695744045 582936444066352760904017)
                    ·
                      rfl

theorem cell22_1702897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_1702897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702897 prefixEnd_1702897 := by exact prefixLift 1702897
  have htrace : WordTrace (prefixWord ++ tailWord_1702897) baseStart_1702897 baseEnd_1702897 := by
    simpa [prefixWord, tailWord_1702897, baseEnd_1702897] using wordTrace_append hprefix tailTrace_1702897
  have hstable : (prefixWord ++ tailWord_1702897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702897).length < 2 ^ (prefixWord ++ tailWord_1702897).sum := by decide
  have hdescent : baseEnd_1702897 < baseStart_1702897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702908 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1702908 : Nat := 118140960795 + 1702908 * 2 ^ 59
def prefixEnd_1702908 : Nat := 4983230072969 + 3 ^ 40 * 1702908 * 2
def baseEnd_1702908 : Nat := 582940209591152398878983

theorem tailTrace_1702908 : CollatzResearch.WordTrace tailWord_1702908 prefixEnd_1702908 582940209591152398878983 := by
  unfold tailWord_1702908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055078657331312188534689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41406771543108416251379585 31055078657331312188534689)
  ·
    refine ⟨23291308992998484141401017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31055078657331312188534689 23291308992998484141401017)
    ·
      refine ⟨17468481744748863106050763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23291308992998484141401017 17468481744748863106050763)
      ·
        refine ⟨26202722617123294659076145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17468481744748863106050763 26202722617123294659076145)
        ·
          refine ⟨19652041962842470994307109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26202722617123294659076145 19652041962842470994307109)
          ·
            refine ⟨3684757868032963311432583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19652041962842470994307109 3684757868032963311432583)
            ·
              refine ⟨5527136802049444967148875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684757868032963311432583 5527136802049444967148875)
              ·
                refine ⟨8290705203074167450723313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527136802049444967148875 8290705203074167450723313)
                ·
                  refine ⟨6218028902305625588042485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8290705203074167450723313 6218028902305625588042485)
                  ·
                    refine ⟨582940209591152398878983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6218028902305625588042485 582940209591152398878983)
                    ·
                      rfl

theorem cell22_1702908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1702908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702908 prefixEnd_1702908 := by exact prefixLift 1702908
  have htrace : WordTrace (prefixWord ++ tailWord_1702908) baseStart_1702908 baseEnd_1702908 := by
    simpa [prefixWord, tailWord_1702908, baseEnd_1702908] using wordTrace_append hprefix tailTrace_1702908
  have hstable : (prefixWord ++ tailWord_1702908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702908).length < 2 ^ (prefixWord ++ tailWord_1702908).sum := by decide
  have hdescent : baseEnd_1702908 < baseStart_1702908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702914 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1702914 : Nat := 118140960795 + 1702914 * 2 ^ 59
def prefixEnd_1702914 : Nat := 4983230072969 + 3 ^ 40 * 1702914 * 2
def baseEnd_1702914 : Nat := 582942263513770383228965

theorem tailTrace_1702914 : CollatzResearch.WordTrace tailWord_1702914 prefixEnd_1702914 582942263513770383228965 := by
  unfold tailWord_1702914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15527594038160221850446949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41406917435093924934525197 15527594038160221850446949)
  ·
    refine ⟨2911423882155041596958803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15527594038160221850446949 2911423882155041596958803)
    ·
      refine ⟨4367135823232562395438205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911423882155041596958803 4367135823232562395438205)
      ·
        refine ⟨1637675933712210898289327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4367135823232562395438205 1637675933712210898289327)
        ·
          refine ⟨2456513900568316347433991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637675933712210898289327 2456513900568316347433991)
          ·
            refine ⟨3684770850852474521150987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456513900568316347433991 3684770850852474521150987)
            ·
              refine ⟨5527156276278711781726481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684770850852474521150987 5527156276278711781726481)
              ·
                refine ⟨4145367207209033836294861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5527156276278711781726481 4145367207209033836294861)
                ·
                  refine ⟨1554512702703387688610573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4145367207209033836294861 1554512702703387688610573)
                  ·
                    refine ⟨582942263513770383228965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554512702703387688610573 582942263513770383228965)
                    ·
                      rfl

theorem cell22_1702914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1702914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702914 prefixEnd_1702914 := by exact prefixLift 1702914
  have htrace : WordTrace (prefixWord ++ tailWord_1702914) baseStart_1702914 baseEnd_1702914 := by
    simpa [prefixWord, tailWord_1702914, baseEnd_1702914] using wordTrace_append hprefix tailTrace_1702914
  have hstable : (prefixWord ++ tailWord_1702914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702914).length < 2 ^ (prefixWord ++ tailWord_1702914).sum := by decide
  have hdescent : baseEnd_1702914 < baseStart_1702914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702923 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_1702923 : Nat := 118140960795 + 1702923 * 2 ^ 59
def prefixEnd_1702923 : Nat := 4983230072969 + 3 ^ 40 * 1702923 * 2
def baseEnd_1702923 : Nat := 582945344397697359753937

theorem tailTrace_1702923 : CollatzResearch.WordTrace tailWord_1702923 prefixEnd_1702923 582945344397697359753937 := by
  unfold tailWord_1702923
  simp only [CollatzResearch.WordTrace]
  refine ⟨62110704409608281938865423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41407136273072187959243615 62110704409608281938865423)
  ·
    refine ⟨93166056614412422908298135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62110704409608281938865423 93166056614412422908298135)
    ·
      refine ⟨139749084921618634362447203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93166056614412422908298135 139749084921618634362447203)
      ·
        refine ⟨209623627382427951543670805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139749084921618634362447203 209623627382427951543670805)
        ·
          refine ⟨9826107533551310228609569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209623627382427951543670805 9826107533551310228609569)
          ·
            refine ⟨7369580650163482671457177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9826107533551310228609569 7369580650163482671457177)
            ·
              refine ⟨5527185487622612003592883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7369580650163482671457177 5527185487622612003592883)
              ·
                refine ⟨8290778231433918005389325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527185487622612003592883 8290778231433918005389325)
                ·
                  refine ⟨3109041836787719252020997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8290778231433918005389325 3109041836787719252020997)
                  ·
                    refine ⟨582945344397697359753937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3109041836787719252020997 582945344397697359753937)
                    ·
                      rfl

theorem cell22_1702923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_1702923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702923 prefixEnd_1702923 := by exact prefixLift 1702923
  have htrace : WordTrace (prefixWord ++ tailWord_1702923) baseStart_1702923 baseEnd_1702923 := by
    simpa [prefixWord, tailWord_1702923, baseEnd_1702923] using wordTrace_append hprefix tailTrace_1702923
  have hstable : (prefixWord ++ tailWord_1702923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702923).length < 2 ^ (prefixWord ++ tailWord_1702923).sum := by decide
  have hdescent : baseEnd_1702923 < baseStart_1702923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702944 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_1702944 : Nat := 118140960795 + 1702944 * 2 ^ 59
def prefixEnd_1702944 : Nat := 4983230072969 + 3 ^ 40 * 1702944 * 2
def baseEnd_1702944 : Nat := 194317511042286768326291

theorem tailTrace_1702944 : CollatzResearch.WordTrace tailWord_1702944 prefixEnd_1702944 194317511042286768326291 := by
  unfold tailWord_1702944
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055735171266101262689943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41407646895021468350253257 31055735171266101262689943)
  ·
    refine ⟨46583602756899151894034915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31055735171266101262689943 46583602756899151894034915)
    ·
      refine ⟨69875404135348727841052373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46583602756899151894034915 69875404135348727841052373)
      ·
        refine ⟨1637704784422235808774665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69875404135348727841052373 1637704784422235808774665)
        ·
          refine ⟨1228278588316676856580999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1637704784422235808774665 1228278588316676856580999)
          ·
            refine ⟨1842417882475015284871499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228278588316676856580999 1842417882475015284871499)
            ·
              refine ⟨2763626823712522927307249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842417882475015284871499 2763626823712522927307249)
              ·
                refine ⟨2072720117784392195480437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763626823712522927307249 2072720117784392195480437)
                ·
                  refine ⟨194317511042286768326291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072720117784392195480437 194317511042286768326291)
                  ·
                    rfl

theorem cell22_1702944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_1702944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702944 prefixEnd_1702944 := by exact prefixLift 1702944
  have htrace : WordTrace (prefixWord ++ tailWord_1702944) baseStart_1702944 baseEnd_1702944 := by
    simpa [prefixWord, tailWord_1702944, baseEnd_1702944] using wordTrace_append hprefix tailTrace_1702944
  have hstable : (prefixWord ++ tailWord_1702944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702944).length < 2 ^ (prefixWord ++ tailWord_1702944).sum := by decide
  have hdescent : baseEnd_1702944 < baseStart_1702944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702968 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_1702968 : Nat := 118140960795 + 1702968 * 2 ^ 59
def prefixEnd_1702968 : Nat := 4983230072969 + 3 ^ 40 * 1702968 * 2
def baseEnd_1702968 : Nat := 582960748817332242378799

theorem tailTrace_1702968 : CollatzResearch.WordTrace tailWord_1702968 prefixEnd_1702968 582960748817332242378799 := by
  unfold tailWord_1702968
  simp only [CollatzResearch.WordTrace]
  refine ⟨31056172847222627312126779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41408230462963503082835705 31056172847222627312126779)
  ·
    refine ⟨46584259270833940968190169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31056172847222627312126779 46584259270833940968190169)
    ·
      refine ⟨34938194453125455726142627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46584259270833940968190169 34938194453125455726142627)
      ·
        refine ⟨52407291679688183589213941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34938194453125455726142627 52407291679688183589213941)
        ·
          refine ⟨4913183594970767211488807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52407291679688183589213941 4913183594970767211488807)
          ·
            refine ⟨7369775392456150817233211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913183594970767211488807 7369775392456150817233211)
            ·
              refine ⟨11054663088684226225849817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369775392456150817233211 11054663088684226225849817)
              ·
                refine ⟨8290997316513169669387363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11054663088684226225849817 8290997316513169669387363)
                ·
                  refine ⟨12436495974769754504081045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290997316513169669387363 12436495974769754504081045)
                  ·
                    refine ⟨582960748817332242378799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12436495974769754504081045 582960748817332242378799)
                    ·
                      rfl

theorem cell22_1702968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_1702968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702968 prefixEnd_1702968 := by exact prefixLift 1702968
  have htrace : WordTrace (prefixWord ++ tailWord_1702968) baseStart_1702968 baseEnd_1702968 := by
    simpa [prefixWord, tailWord_1702968, baseEnd_1702968] using wordTrace_append hprefix tailTrace_1702968
  have hstable : (prefixWord ++ tailWord_1702968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702968).length < 2 ^ (prefixWord ++ tailWord_1702968).sum := by decide
  have hdescent : baseEnd_1702968 < baseStart_1702968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702970 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_1702970 : Nat := 118140960795 + 1702970 * 2 ^ 59
def prefixEnd_1702970 : Nat := 4983230072969 + 3 ^ 40 * 1702970 * 2
def baseEnd_1702970 : Nat := 582961433458204903828793

theorem tailTrace_1702970 : CollatzResearch.WordTrace tailWord_1702970 prefixEnd_1702970 582961433458204903828793 := by
  unfold tailWord_1702970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528104660109502241456591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41408279093625339310550909 15528104660109502241456591)
  ·
    refine ⟨23292156990164253362184887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15528104660109502241456591 23292156990164253362184887)
    ·
      refine ⟨34938235485246380043277331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23292156990164253362184887 34938235485246380043277331)
      ·
        refine ⟨52407353227869570064915997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34938235485246380043277331 52407353227869570064915997)
        ·
          refine ⟨19652757460451088774343499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52407353227869570064915997 19652757460451088774343499)
          ·
            refine ⟨29479136190676633161515249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19652757460451088774343499 29479136190676633161515249)
            ·
              refine ⟨22109352143007474871136437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29479136190676633161515249 22109352143007474871136437)
              ·
                refine ⟨2072751763406950769169041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22109352143007474871136437 2072751763406950769169041)
                ·
                  refine ⟨1554563822555213076876781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072751763406950769169041 1554563822555213076876781)
                  ·
                    refine ⟨582961433458204903828793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554563822555213076876781 582961433458204903828793)
                    ·
                      rfl

theorem cell22_1702970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_1702970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702970 prefixEnd_1702970 := by exact prefixLift 1702970
  have htrace : WordTrace (prefixWord ++ tailWord_1702970) baseStart_1702970 baseEnd_1702970 := by
    simpa [prefixWord, tailWord_1702970, baseEnd_1702970] using wordTrace_append hprefix tailTrace_1702970
  have hstable : (prefixWord ++ tailWord_1702970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702970).length < 2 ^ (prefixWord ++ tailWord_1702970).sum := by decide
  have hdescent : baseEnd_1702970 < baseStart_1702970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702983 : List Nat := [1, 1, 4, 1, 3, 3, 1, 8]
def baseStart_1702983 : Nat := 118140960795 + 1702983 * 2 ^ 59
def prefixEnd_1702983 : Nat := 4983230072969 + 3 ^ 40 * 1702983 * 2
def baseEnd_1702983 : Nat := 64773987069319689250417

theorem tailTrace_1702983 : CollatzResearch.WordTrace tailWord_1702983 prefixEnd_1702983 64773987069319689250417 := by
  unfold tailWord_1702983
  simp only [CollatzResearch.WordTrace]
  refine ⟨62112892789390912186049603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41408595192927274790699735 62112892789390912186049603)
  ·
    refine ⟨93169339184086368279074405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62112892789390912186049603 93169339184086368279074405)
    ·
      refine ⟨17469251097016194052326451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93169339184086368279074405 17469251097016194052326451)
      ·
        refine ⟨26203876645524291078489677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17469251097016194052326451 26203876645524291078489677)
        ·
          refine ⟨9826453742071609154433629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26203876645524291078489677 9826453742071609154433629)
          ·
            refine ⟨3684920153276853432912611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9826453742071609154433629 3684920153276853432912611)
            ·
              refine ⟨5527380229915280149368917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684920153276853432912611 5527380229915280149368917)
              ·
                refine ⟨64773987069319689250417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5527380229915280149368917 64773987069319689250417)
                ·
                  rfl

theorem cell22_1702983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 8].length) (baseStart_1702983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702983 prefixEnd_1702983 := by exact prefixLift 1702983
  have htrace : WordTrace (prefixWord ++ tailWord_1702983) baseStart_1702983 baseEnd_1702983 := by
    simpa [prefixWord, tailWord_1702983, baseEnd_1702983] using wordTrace_append hprefix tailTrace_1702983
  have hstable : (prefixWord ++ tailWord_1702983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702983).length < 2 ^ (prefixWord ++ tailWord_1702983).sum := by decide
  have hdescent : baseEnd_1702983 < baseStart_1702983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702989 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1702989 : Nat := 118140960795 + 1702989 * 2 ^ 59
def prefixEnd_1702989 : Nat := 4983230072969 + 3 ^ 40 * 1702989 * 2
def baseEnd_1702989 : Nat := 194322645848831729201245

theorem tailTrace_1702989 : CollatzResearch.WordTrace tailWord_1702989 prefixEnd_1702989 194322645848831729201245 := by
  unfold tailWord_1702989
  simp only [CollatzResearch.WordTrace]
  refine ⟨62113111627369175210768021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41408741084912783473845347 62113111627369175210768021)
  ·
    refine ⟨2911552107532930088004751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62113111627369175210768021 2911552107532930088004751)
    ·
      refine ⟨4367328161299395132007127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911552107532930088004751 4367328161299395132007127)
      ·
        refine ⟨6550992241949092698010691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367328161299395132007127 6550992241949092698010691)
        ·
          refine ⟨9826488362923639047016037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550992241949092698010691 9826488362923639047016037)
          ·
            refine ⟨1842466568048182321315507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9826488362923639047016037 1842466568048182321315507)
            ·
              refine ⟨2763699852072273481973261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842466568048182321315507 2763699852072273481973261)
              ·
                refine ⟨1036387444527102555739973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2763699852072273481973261 1036387444527102555739973)
                ·
                  refine ⟨194322645848831729201245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1036387444527102555739973 194322645848831729201245)
                  ·
                    rfl

theorem cell22_1702989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1702989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1702989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1702989 prefixEnd_1702989 := by exact prefixLift 1702989
  have htrace : WordTrace (prefixWord ++ tailWord_1702989) baseStart_1702989 baseEnd_1702989 := by
    simpa [prefixWord, tailWord_1702989, baseEnd_1702989] using wordTrace_append hprefix tailTrace_1702989
  have hstable : (prefixWord ++ tailWord_1702989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702989).length < 2 ^ (prefixWord ++ tailWord_1702989).sum := by decide
  have hdescent : baseEnd_1702989 < baseStart_1702989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703013 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1703013 : Nat := 118140960795 + 1703013 * 2 ^ 59
def prefixEnd_1703013 : Nat := 4983230072969 + 3 ^ 40 * 1703013 * 2
def baseEnd_1703013 : Nat := 582976153236967125003661

theorem tailTrace_1703013 : CollatzResearch.WordTrace tailWord_1703013 prefixEnd_1703013 582976153236967125003661 := by
  unfold tailWord_1703013
  simp only [CollatzResearch.WordTrace]
  refine ⟨62113986979282227309641693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41409324652854818206427795 62113986979282227309641693)
  ·
    refine ⟨23292745117230835241115635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62113986979282227309641693 23292745117230835241115635)
    ·
      refine ⟨34939117675846252861673453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23292745117230835241115635 34939117675846252861673453)
      ·
        refine ⟨13102169128442344823127545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34939117675846252861673453 13102169128442344823127545)
        ·
          refine ⟨9826626846331758617345659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13102169128442344823127545 9826626846331758617345659)
          ·
            refine ⟨14739940269497637926018489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826626846331758617345659 14739940269497637926018489)
            ·
              refine ⟨11054955202123228444513867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14739940269497637926018489 11054955202123228444513867)
              ·
                refine ⟨16582432803184842666770801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054955202123228444513867 16582432803184842666770801)
                ·
                  refine ⟨12436824602388632000078101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16582432803184842666770801 12436824602388632000078101)
                  ·
                    refine ⟨582976153236967125003661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12436824602388632000078101 582976153236967125003661)
                    ·
                      rfl

theorem cell22_1703013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1703013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703013 prefixEnd_1703013 := by exact prefixLift 1703013
  have htrace : WordTrace (prefixWord ++ tailWord_1703013) baseStart_1703013 baseEnd_1703013 := by
    simpa [prefixWord, tailWord_1703013, baseEnd_1703013] using wordTrace_append hprefix tailTrace_1703013
  have hstable : (prefixWord ++ tailWord_1703013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703013).length < 2 ^ (prefixWord ++ tailWord_1703013).sum := by decide
  have hdescent : baseEnd_1703013 < baseStart_1703013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703066 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_1703066 : Nat := 118140960795 + 1703066 * 2 ^ 59
def prefixEnd_1703066 : Nat := 4983230072969 + 3 ^ 40 * 1703066 * 2
def baseEnd_1703066 : Nat := 582994296220092653428499

theorem tailTrace_1703066 : CollatzResearch.WordTrace tailWord_1703066 prefixEnd_1703066 582994296220092653428499 := by
  unfold tailWord_1703066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528980012022554340330263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41410613365393478240880701 15528980012022554340330263)
  ·
    refine ⟨23293470018033831510495395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15528980012022554340330263 23293470018033831510495395)
    ·
      refine ⟨34940205027050747265743093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23293470018033831510495395 34940205027050747265743093)
      ·
        refine ⟨3275644221286007556163415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34940205027050747265743093 3275644221286007556163415)
        ·
          refine ⟨4913466331929011334245123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275644221286007556163415 4913466331929011334245123)
          ·
            refine ⟨7370199497893517001367685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913466331929011334245123 7370199497893517001367685)
            ·
              refine ⟨1381912405855034437756441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7370199497893517001367685 1381912405855034437756441)
              ·
                refine ⟨1036434304391275828317331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381912405855034437756441 1036434304391275828317331)
                ·
                  refine ⟨1554651456586913742475997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036434304391275828317331 1554651456586913742475997)
                  ·
                    refine ⟨582994296220092653428499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554651456586913742475997 582994296220092653428499)
                    ·
                      rfl

theorem cell22_1703066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_1703066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703066 prefixEnd_1703066 := by exact prefixLift 1703066
  have htrace : WordTrace (prefixWord ++ tailWord_1703066) baseStart_1703066 baseEnd_1703066 := by
    simpa [prefixWord, tailWord_1703066, baseEnd_1703066] using wordTrace_append hprefix tailTrace_1703066
  have hstable : (prefixWord ++ tailWord_1703066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703066).length < 2 ^ (prefixWord ++ tailWord_1703066).sum := by decide
  have hdescent : baseEnd_1703066 < baseStart_1703066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703088 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_1703088 : Nat := 118140960795 + 1703088 * 2 ^ 59
def prefixEnd_1703088 : Nat := 4983230072969 + 3 ^ 40 * 1703088 * 2
def baseEnd_1703088 : Nat := 583001827269691929378431

theorem tailTrace_1703088 : CollatzResearch.WordTrace tailWord_1703088 prefixEnd_1703088 583001827269691929378431 := by
  unfold tailWord_1703088
  simp only [CollatzResearch.WordTrace]
  refine ⟨31058361227005257559310959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41411148302673676745747945 31058361227005257559310959)
  ·
    refine ⟨46587541840507886338966439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31058361227005257559310959 46587541840507886338966439)
    ·
      refine ⟨69881312760761829508449659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46587541840507886338966439 69881312760761829508449659)
      ·
        refine ⟨104821969141142744262674489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69881312760761829508449659 104821969141142744262674489)
        ·
          refine ⟨78616476855857058197005867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104821969141142744262674489 78616476855857058197005867)
          ·
            refine ⟨117924715283785587295508801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78616476855857058197005867 117924715283785587295508801)
            ·
              refine ⟨88443536462839190471631601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117924715283785587295508801 88443536462839190471631601)
              ·
                refine ⟨66332652347129392853723701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88443536462839190471631601 66332652347129392853723701)
                ·
                  refine ⟨6218686157543380580036597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66332652347129392853723701 6218686157543380580036597)
                  ·
                    refine ⟨583001827269691929378431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6218686157543380580036597 583001827269691929378431)
                    ·
                      rfl

theorem cell22_1703088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_1703088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703088 prefixEnd_1703088 := by exact prefixLift 1703088
  have htrace : WordTrace (prefixWord ++ tailWord_1703088) baseStart_1703088 baseEnd_1703088 := by
    simpa [prefixWord, tailWord_1703088, baseEnd_1703088] using wordTrace_append hprefix tailTrace_1703088
  have hstable : (prefixWord ++ tailWord_1703088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703088).length < 2 ^ (prefixWord ++ tailWord_1703088).sum := by decide
  have hdescent : baseEnd_1703088 < baseStart_1703088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703090 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_1703090 : Nat := 118140960795 + 1703090 * 2 ^ 59
def prefixEnd_1703090 : Nat := 4983230072969 + 3 ^ 40 * 1703090 * 2
def baseEnd_1703090 : Nat := 194334170636854863609475

theorem tailTrace_1703090 : CollatzResearch.WordTrace tailWord_1703090 prefixEnd_1703090 194334170636854863609475 := by
  unfold tailWord_1703090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529198850000817365048681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41411196933335512973463149 15529198850000817365048681)
  ·
    refine ⟨11646899137500613023786511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15529198850000817365048681 11646899137500613023786511)
    ·
      refine ⟨17470348706250919535679767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11646899137500613023786511 17470348706250919535679767)
      ·
        refine ⟨26205523059376379303519651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17470348706250919535679767 26205523059376379303519651)
        ·
          refine ⟨39308284589064568955279477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26205523059376379303519651 39308284589064568955279477)
          ·
            refine ⟨3685151680224803339557451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39308284589064568955279477 3685151680224803339557451)
            ·
              refine ⟨5527727520337205009336177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685151680224803339557451 5527727520337205009336177)
              ·
                refine ⟨4145795640252903757002133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5527727520337205009336177 4145795640252903757002133)
                ·
                  refine ⟨194334170636854863609475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4145795640252903757002133 194334170636854863609475)
                  ·
                    rfl

theorem cell22_1703090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_1703090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703090 prefixEnd_1703090 := by exact prefixLift 1703090
  have htrace : WordTrace (prefixWord ++ tailWord_1703090) baseStart_1703090 baseEnd_1703090 := by
    simpa [prefixWord, tailWord_1703090, baseEnd_1703090] using wordTrace_append hprefix tailTrace_1703090
  have hstable : (prefixWord ++ tailWord_1703090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703090).length < 2 ^ (prefixWord ++ tailWord_1703090).sum := by decide
  have hdescent : baseEnd_1703090 < baseStart_1703090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703122 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1703122 : Nat := 118140960795 + 1703122 * 2 ^ 59
def prefixEnd_1703122 : Nat := 4983230072969 + 3 ^ 40 * 1703122 * 2
def baseEnd_1703122 : Nat := 583013466164527174028327

theorem tailTrace_1703122 : CollatzResearch.WordTrace tailWord_1703122 prefixEnd_1703122 583013466164527174028327 := by
  unfold tailWord_1703122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529490633971834731339905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41411975023924892616906413 15529490633971834731339905)
  ·
    refine ⟨11647117975478876048504929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15529490633971834731339905 11647117975478876048504929)
    ·
      refine ⟨8735338481609157036378697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11647117975478876048504929 8735338481609157036378697)
      ·
        refine ⟨6551503861206867777284023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8735338481609157036378697 6551503861206867777284023)
        ·
          refine ⟨9827255791810301665926035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551503861206867777284023 9827255791810301665926035)
          ·
            refine ⟨14740883687715452498889053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827255791810301665926035 14740883687715452498889053)
            ·
              refine ⟨5527831382893294687083395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14740883687715452498889053 5527831382893294687083395)
              ·
                refine ⟨8291747074339942030625093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527831382893294687083395 8291747074339942030625093)
                ·
                  refine ⟨1554702576438739130742205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8291747074339942030625093 1554702576438739130742205)
                  ·
                    refine ⟨583013466164527174028327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554702576438739130742205 583013466164527174028327)
                    ·
                      rfl

theorem cell22_1703122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1703122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703122 prefixEnd_1703122 := by exact prefixLift 1703122
  have htrace : WordTrace (prefixWord ++ tailWord_1703122) baseStart_1703122 baseEnd_1703122 := by
    simpa [prefixWord, tailWord_1703122, baseEnd_1703122] using wordTrace_append hprefix tailTrace_1703122
  have hstable : (prefixWord ++ tailWord_1703122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703122).length < 2 ^ (prefixWord ++ tailWord_1703122).sum := by decide
  have hdescent : baseEnd_1703122 < baseStart_1703122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703124 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1703124 : Nat := 118140960795 + 1703124 * 2 ^ 59
def prefixEnd_1703124 : Nat := 4983230072969 + 3 ^ 40 * 1703124 * 2
def baseEnd_1703124 : Nat := 194338050268466611826107

theorem tailTrace_1703124 : CollatzResearch.WordTrace tailWord_1703124 prefixEnd_1703124 194338050268466611826107 := by
  unfold tailWord_1703124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31059017740940046633466213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41412023654586728844621617 31059017740940046633466213)
  ·
    refine ⟨5823565826426258743774915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31059017740940046633466213 5823565826426258743774915)
    ·
      refine ⟨8735348739639388115662373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823565826426258743774915 8735348739639388115662373)
      ·
        refine ⟨1637877888682385271686695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8735348739639388115662373 1637877888682385271686695)
        ·
          refine ⟨2456816833023577907530043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637877888682385271686695 2456816833023577907530043)
          ·
            refine ⟨3685225249535366861295065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456816833023577907530043 3685225249535366861295065)
            ·
              refine ⟨2763918937151525145971299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685225249535366861295065 2763918937151525145971299)
              ·
                refine ⟨4145878405727287718956949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763918937151525145971299 4145878405727287718956949)
                ·
                  refine ⟨194338050268466611826107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4145878405727287718956949 194338050268466611826107)
                  ·
                    rfl

theorem cell22_1703124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1703124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703124 prefixEnd_1703124 := by exact prefixLift 1703124
  have htrace : WordTrace (prefixWord ++ tailWord_1703124) baseStart_1703124 baseEnd_1703124 := by
    simpa [prefixWord, tailWord_1703124, baseEnd_1703124] using wordTrace_append hprefix tailTrace_1703124
  have hstable : (prefixWord ++ tailWord_1703124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703124).length < 2 ^ (prefixWord ++ tailWord_1703124).sum := by decide
  have hdescent : baseEnd_1703124 < baseStart_1703124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703180 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 7]
def baseStart_1703180 : Nat := 118140960795 + 1703180 * 2 ^ 59
def prefixEnd_1703180 : Nat := 4983230072969 + 3 ^ 40 * 1703180 * 2
def baseEnd_1703180 : Nat := 194344440249944785359383

theorem tailTrace_1703180 : CollatzResearch.WordTrace tailWord_1703180 prefixEnd_1703180 194344440249944785359383 := by
  unfold tailWord_1703180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31060038984838607415485497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41413385313118143220647329 31060038984838607415485497)
  ·
    refine ⟨23295029238628955561614123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31060038984838607415485497 23295029238628955561614123)
    ·
      refine ⟨34942543857943433342421185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23295029238628955561614123 34942543857943433342421185)
      ·
        refine ⟨26206907893457575006815889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34942543857943433342421185 26206907893457575006815889)
        ·
          refine ⟨19655180920093181255111917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26206907893457575006815889 19655180920093181255111917)
          ·
            refine ⟨7370692845034942970666969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19655180920093181255111917 7370692845034942970666969)
            ·
              refine ⟨5528019633776207228000227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7370692845034942970666969 5528019633776207228000227)
              ·
                refine ⟨8292029450664310842000341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528019633776207228000227 8292029450664310842000341)
                ·
                  refine ⟨194344440249944785359383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8292029450664310842000341 194344440249944785359383)
                  ·
                    rfl

theorem cell22_1703180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_1703180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703180 prefixEnd_1703180 := by exact prefixLift 1703180
  have htrace : WordTrace (prefixWord ++ tailWord_1703180) baseStart_1703180 baseEnd_1703180 := by
    simpa [prefixWord, tailWord_1703180, baseEnd_1703180] using wordTrace_append hprefix tailTrace_1703180
  have hstable : (prefixWord ++ tailWord_1703180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703180).length < 2 ^ (prefixWord ++ tailWord_1703180).sum := by decide
  have hdescent : baseEnd_1703180 < baseStart_1703180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703240 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1703240 : Nat := 118140960795 + 1703240 * 2 ^ 59
def prefixEnd_1703240 : Nat := 4983230072969 + 3 ^ 40 * 1703240 * 2
def baseEnd_1703240 : Nat := 583053859976014199577965

theorem tailTrace_1703240 : CollatzResearch.WordTrace tailWord_1703240 prefixEnd_1703240 583053859976014199577965 := by
  unfold tailWord_1703240
  simp only [CollatzResearch.WordTrace]
  refine ⟨31061133174729922539077587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41414844232973230052103449 31061133174729922539077587)
  ·
    refine ⟨46591699762094883808616381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31061133174729922539077587 46591699762094883808616381)
    ·
      refine ⟨17471887410785581428231143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46591699762094883808616381 17471887410785581428231143)
      ·
        refine ⟨26207831116178372142346715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17471887410785581428231143 26207831116178372142346715)
        ·
          refine ⟨39311746674267558213520073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26207831116178372142346715 39311746674267558213520073)
          ·
            refine ⟨29483810005700668660140055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39311746674267558213520073 29483810005700668660140055)
            ·
              refine ⟨44225715008551002990210083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29483810005700668660140055 44225715008551002990210083)
              ·
                refine ⟨66338572512826504485315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44225715008551002990210083 66338572512826504485315125)
                ·
                  refine ⟨6219241173077484795498293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66338572512826504485315125 6219241173077484795498293)
                  ·
                    refine ⟨583053859976014199577965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6219241173077484795498293 583053859976014199577965)
                    ·
                      rfl

theorem cell22_1703240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1703240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703240 prefixEnd_1703240 := by exact prefixLift 1703240
  have htrace : WordTrace (prefixWord ++ tailWord_1703240) baseStart_1703240 baseEnd_1703240 := by
    simpa [prefixWord, tailWord_1703240, baseEnd_1703240] using wordTrace_append hprefix tailTrace_1703240
  have hstable : (prefixWord ++ tailWord_1703240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703240).length < 2 ^ (prefixWord ++ tailWord_1703240).sum := by decide
  have hdescent : baseEnd_1703240 < baseStart_1703240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703353 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_1703353 : Nat := 118140960795 + 1703353 * 2 ^ 59
def prefixEnd_1703353 : Nat := 4983230072969 + 3 ^ 40 * 1703353 * 2
def baseEnd_1703353 : Nat := 583092542185319571502619

theorem tailTrace_1703353 : CollatzResearch.WordTrace tailWord_1703353 prefixEnd_1703353 583092542185319571502619 := by
  unfold tailWord_1703353
  simp only [CollatzResearch.WordTrace]
  refine ⟨62126387798050465377018713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41417591865366976918012475 62126387798050465377018713)
  ·
    refine ⟨46594790848537849032764035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62126387798050465377018713 46594790848537849032764035)
    ·
      refine ⟨69892186272806773549146053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46594790848537849032764035 69892186272806773549146053)
      ·
        refine ⟨13104784926151270040464885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69892186272806773549146053 13104784926151270040464885)
        ·
          refine ⟨1228573586826681566293583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13104784926151270040464885 1228573586826681566293583)
          ·
            refine ⟨1842860380240022349440375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228573586826681566293583 1842860380240022349440375)
            ·
              refine ⟨2764290570360033524160563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842860380240022349440375 2764290570360033524160563)
              ·
                refine ⟨4146435855540050286240845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764290570360033524160563 4146435855540050286240845)
                ·
                  refine ⟨1554913445827518857340317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4146435855540050286240845 1554913445827518857340317)
                  ·
                    refine ⟨583092542185319571502619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554913445827518857340317 583092542185319571502619)
                    ·
                      rfl

theorem cell22_1703353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_1703353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703353 prefixEnd_1703353 := by exact prefixLift 1703353
  have htrace : WordTrace (prefixWord ++ tailWord_1703353) baseStart_1703353 baseEnd_1703353 := by
    simpa [prefixWord, tailWord_1703353, baseEnd_1703353] using wordTrace_append hprefix tailTrace_1703353
  have hstable : (prefixWord ++ tailWord_1703353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703353).length < 2 ^ (prefixWord ++ tailWord_1703353).sum := by decide
  have hdescent : baseEnd_1703353 < baseStart_1703353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703426 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1703426 : Nat := 118140960795 + 1703426 * 2 ^ 59
def prefixEnd_1703426 : Nat := 4983230072969 + 3 ^ 40 * 1703426 * 2
def baseEnd_1703426 : Nat := 583117531577171714427395

theorem tailTrace_1703426 : CollatzResearch.WordTrace tailWord_1703426 prefixEnd_1703426 583117531577171714427395 := by
  unfold tailWord_1703426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532262581696499711106533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41419366884523999229617421 15532262581696499711106533)
  ·
    refine ⟨2912299234068093695832475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15532262581696499711106533 2912299234068093695832475)
    ·
      refine ⟨4368448851102140543748713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912299234068093695832475 4368448851102140543748713)
      ·
        refine ⟨3276336638326605407811535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368448851102140543748713 3276336638326605407811535)
        ·
          refine ⟨4914504957489908111717303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276336638326605407811535 4914504957489908111717303)
          ·
            refine ⟨7371757436234862167575955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914504957489908111717303 7371757436234862167575955)
            ·
              refine ⟨11057636154352293251363933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371757436234862167575955 11057636154352293251363933)
              ·
                refine ⟨4146613557882109969261475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11057636154352293251363933 4146613557882109969261475)
                ·
                  refine ⟨6219920336823164953892213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146613557882109969261475 6219920336823164953892213)
                  ·
                    refine ⟨583117531577171714427395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6219920336823164953892213 583117531577171714427395)
                    ·
                      rfl

theorem cell22_1703426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1703426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703426 prefixEnd_1703426 := by exact prefixLift 1703426
  have htrace : WordTrace (prefixWord ++ tailWord_1703426) baseStart_1703426 baseEnd_1703426 := by
    simpa [prefixWord, tailWord_1703426, baseEnd_1703426] using wordTrace_append hprefix tailTrace_1703426
  have hstable : (prefixWord ++ tailWord_1703426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703426).length < 2 ^ (prefixWord ++ tailWord_1703426).sum := by decide
  have hdescent : baseEnd_1703426 < baseStart_1703426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703497 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1703497 : Nat := 118140960795 + 1703497 * 2 ^ 59
def prefixEnd_1703497 : Nat := 4983230072969 + 3 ^ 40 * 1703497 * 2
def baseEnd_1703497 : Nat := 583141836328151195902177

theorem tailTrace_1703497 : CollatzResearch.WordTrace tailWord_1703497 prefixEnd_1703497 583141836328151195902177 := by
  unfold tailWord_1703497
  simp only [CollatzResearch.WordTrace]
  refine ⟨62131639909528777970260745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41421093273019185313507163 62131639909528777970260745)
  ·
    refine ⟨46598729932146583477695559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62131639909528777970260745 46598729932146583477695559)
    ·
      refine ⟨69898094898219875216543339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46598729932146583477695559 69898094898219875216543339)
      ·
        refine ⟨104847142347329812824815009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69898094898219875216543339 104847142347329812824815009)
        ·
          refine ⟨78635356760497359618611257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104847142347329812824815009 78635356760497359618611257)
          ·
            refine ⟨58976517570373019713958443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78635356760497359618611257 58976517570373019713958443)
            ·
              refine ⟨88464776355559529570937665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58976517570373019713958443 88464776355559529570937665)
              ·
                refine ⟨66348582266669647178203249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88464776355559529570937665 66348582266669647178203249)
                ·
                  refine ⟨49761436700002235383652437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66348582266669647178203249 49761436700002235383652437)
                  ·
                    refine ⟨583141836328151195902177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49761436700002235383652437 583141836328151195902177)
                    ·
                      rfl

theorem cell22_1703497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1703497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703497 prefixEnd_1703497 := by exact prefixLift 1703497
  have htrace : WordTrace (prefixWord ++ tailWord_1703497) baseStart_1703497 baseEnd_1703497 := by
    simpa [prefixWord, tailWord_1703497, baseEnd_1703497] using wordTrace_append hprefix tailTrace_1703497
  have hstable : (prefixWord ++ tailWord_1703497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703497).length < 2 ^ (prefixWord ++ tailWord_1703497).sum := by decide
  have hdescent : baseEnd_1703497 < baseStart_1703497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703529 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 6]
def baseStart_1703529 : Nat := 118140960795 + 1703529 * 2 ^ 59
def prefixEnd_1703529 : Nat := 4983230072969 + 3 ^ 40 * 1703529 * 2
def baseEnd_1703529 : Nat := 194384263527371259700693

theorem tailTrace_1703529 : CollatzResearch.WordTrace tailWord_1703529 prefixEnd_1703529 194384263527371259700693 := by
  unfold tailWord_1703529
  simp only [CollatzResearch.WordTrace]
  refine ⟨62132807045412847435425641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41421871363608564956950427 62132807045412847435425641)
  ·
    refine ⟨46599605284059635576569231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62132807045412847435425641 46599605284059635576569231)
    ·
      refine ⟨69899407926089453364853847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46599605284059635576569231 69899407926089453364853847)
      ·
        refine ⟨104849111889134180047280771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69899407926089453364853847 104849111889134180047280771)
        ·
          refine ⟨157273667833701270070921157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104849111889134180047280771 157273667833701270070921157)
          ·
            refine ⟨29488812718818988138297717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157273667833701270070921157 29488812718818988138297717)
            ·
              refine ⟨2764576192389280137965411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29488812718818988138297717 2764576192389280137965411)
              ·
                refine ⟨4146864288583920206948117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764576192389280137965411 4146864288583920206948117)
                ·
                  refine ⟨194384263527371259700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4146864288583920206948117 194384263527371259700693)
                  ·
                    rfl

theorem cell22_1703529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_1703529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1703529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1703529 prefixEnd_1703529 := by exact prefixLift 1703529
  have htrace : WordTrace (prefixWord ++ tailWord_1703529) baseStart_1703529 baseEnd_1703529 := by
    simpa [prefixWord, tailWord_1703529, baseEnd_1703529] using wordTrace_append hprefix tailTrace_1703529
  have hstable : (prefixWord ++ tailWord_1703529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703529).length < 2 ^ (prefixWord ++ tailWord_1703529).sum := by decide
  have hdescent : baseEnd_1703529 < baseStart_1703529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
